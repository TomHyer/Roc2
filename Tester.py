import sys
import os
import random
import shutil
import re
import multiprocessing
import subprocess
import threading
import time
import bisect
import math
from collections import defaultdict

ResultFile = "TestResults.csv"
TcecFile = 'D:/data/Ethereal_12_00_64-bit.commented.[1535].pgn'
ROUNDS_PER_MATCH, MATCHES_PER_PAIR = 12, [1000, 2500]
ENGINES = ['Base/Roc.exe', 'Test/Roc.exe', 'Gull 3 x64 syzygy.exe', 'Ethereal11.25-x64-nopopcnt.exe']
#ENGINES = ['Base/Roc.exe', 'Test/Roc.exe', 'Ethereal11.25-x64-nopopcnt.exe']
#ENGINES = ['Base/Roc.exe', 'Test/Roc.exe']
SENTINEL_FN, HALT_MSG = 'tester.live', "No sentinel; halting"

# courtesy of Stack Overflow
class Command(object):
    def __init__(self, cmd):
        self.cmd = cmd
        self.process = None

    def run(self, timeout):
        dst = [None]
        def target():
            self.process = subprocess.Popen(self.cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
            dst[0] = self.process.communicate()[0]

        thread = threading.Thread(target=target)
        thread.start()

        thread.join(timeout)
        if thread.is_alive():
            print('Unterminated thread; aborting')
            self.process.terminate()
            # thread.join()  # leak the thread, since our process is being shut down anyway

        return dst[0]

def RunMatch(arg):
    if not os.path.exists(SENTINEL_FN):
        if os.path.exists(SENTINEL_FN.replace("live", "die")):
            return HALT_MSG
        time.sleep(1)
        if not os.path.exists(SENTINEL_FN):
            time.sleep(1)
            if not os.path.exists(SENTINEL_FN):
                return HALT_MSG

    en1, en2, tc = arg
    matchP = re.compile('pipe reader')  # 'pipe reader was terminated' -- seems to be a windows process error

    cmd = "\"C:\\Program Files (x86)\\Cute Chess\\cutechess-cli.exe\""
    cmd += ' -engine name=c1 cmd=\"' + en1 + '\" proto=uci option.Threads=1' 
    cmd += ' -engine name=c2 cmd=\"' + en2 + '\" proto=uci option.Threads=1'
    cmd += ' -each tc=' + tc + ' -rounds ' + str(ROUNDS_PER_MATCH)
    cmd += ' -sprt elo0=-20 elo1=20 alpha=0.1 beta=0.1 -resign movecount=3 score=30 -draw movenumber=34 movecount=6 score=5'
    cmd += ' -openings file="' + TcecFile + '" order=random plies=6 -repeat'

    while True:
        try:
            print(cmd)
            task = Command(cmd)
            result = task.run(60 * ROUNDS_PER_MATCH)
            result = str(result)
            print(en1, "vs", en2, result.split("c1 vs c2")[-1].split("...")[0])
            if (not result) or matchP.search(result):   # internal failure, don't trust the result
                print("Ignoring that")
            else:
                return result
        except:
            continue


def _report_all(all_w1, all_w2, all_d):
    print("\n")
    for k in all_w1.keys():
        w1, w2, d = all_w1[k], all_w2[k], all_d[k]
        elo = math.log((1 + w1 + d/2)/(1 + w2 + d/2)) * 400 / math.log(10.0)
        pm = 347.0 * math.sqrt(w1 + w2) / (w1 + w2 + d)
        print("{} vs {}: +{} ={} -{} ({:.0f} +/- {:.0f})".format(k[0][:10], k[1][:10], w1, d, w2, elo, pm))
    print("\n")

if __name__ == "__main__":
    tc_scale = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    tc = f"{0.6*tc_scale:.2f}+{0.01*tc_scale:.2f}"
    print("tc = ", tc)
    n_proc = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    print("n_proc = ", n_proc)

    if os.path.exists(SENTINEL_FN.replace("live", "die")):
        os.rename(SENTINEL_FN.replace("live", "die"), SENTINEL_FN)

    tasks = []
    for e1 in ENGINES:
        for e2 in ENGINES:
            if e1 is e2:
                continue
            if 'roc' not in (e1 + e2).lower():
                continue
            matches = MATCHES_PER_PAIR[1 if 'test' in (e1 + e1).lower() else 0]
            tasks += [(e1, e2)] * matches
    random.shuffle(tasks)
    print(len(tasks), "total tasks")

    pool = multiprocessing.Pool(n_proc)
    print("Multiprocessing matches")
    all_results = pool.map(RunMatch, [(e1, e2, tc) for e1, e2 in tasks])
    print("Generated all results, there are", len(all_results))

    all_w1, all_w2, all_d = defaultdict(int), defaultdict(int), defaultdict(int)
    with open(ResultFile, "a") as results:
        matchS = re.compile('Score of c1 vs c2\: ([0-9]+) - ([0-9]+) - ([0-9]+)')
        matchX = re.compile('connect')  # match 'disconnects' or 'connection stalls' -- an engine failed
        matchF = re.compile('atal error')
        for (e1, e2), result in zip(tasks, all_results):
            try:
                if HALT_MSG in result:
                    continue
			
                #print('Starting matches')
                #result = RunMatch((e1, e2, tc))  # if not multiprocessing
                #time.sleep(1)
                if matchF.search(result):
                    print("Failed")
                    break   # end of match loop

                crash = matchX.search(result)
                if crash:
                    matchW1 = re.compile('c1 vs c2[^\n]+connect')
                    matchW2 = re.compile('1-0[^\n]+connect')
                    crash2 = (not matchW1.search(result)) == (not matchW2.search(result))
                    print(crash2 and 'C2 crashed' or 'C1 crashed')
                    crasher = crash2 and c2 or c1
                    break   # end of match loop

                score = None
                for score in re.finditer(matchS, result):
                    pass
                # now score holds the last match
                if not score:
                    print("Can't find score -- result text follows")
                    print(result)
                    break   # match loop failed

                print('Results:  ' + score.group(0))
                (w1, w2, d) = [int(score.group(i)) for i in range(1,4)]
                ad1 = (w1 - w2) / 2
                print(e1, 'wins by', ad1, 'vs', e2)

                if e1 > e2:
                    e1, e2 = e2, e1
                    w1, w2 = w2, w1
                results.write(','.join([str(x) for x in (e1, e2, w1, w2, d, w1-w2)])+"\n")

                k = (e1, e2)
                all_w1[k] += w1
                all_w2[k] += w2
                all_d[k] += d
                _report_all(all_w1, all_w2, all_d)
            except KeyboardInterrupt:
                _report_all(all_w1, all_w2, all_d)
                print("Really quit?")
                done = input()
                done = (done[:1] == 'y')

    _report_all(all_w1, all_w2, all_d)
