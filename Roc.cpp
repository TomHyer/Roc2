// This code is public domain, as defined by the "CC0" Creative Commons license
// This code is public domain, as defined by the "CC0" Creative Commons license

//#define REGRESSION
//#define W32_BUILD
#define _CRT_SECURE_NO_WARNINGS
//#define CPU_TIMING
//#define TWO_PHASE
#define LARGE_PAGES
#define MP_NPS
//#define TIME_TO_DEPTH
//#define HNI
//#define VERBOSE

#ifdef W32_BUILD
#define NTDDI_VERSION 0x05010200
#define _WIN32_WINNT 0x0501
#else
#define _WIN32_WINNT 0x0600
#endif

#include <iostream>
#include <fstream>
#include <array>
#include <numeric>
#include <string>
#include <vector>
#include <thread>
#include <cmath>
#include <algorithm>
#include <chrono>
#include <unordered_map>
#include <bitset>
typedef std::chrono::high_resolution_clock::time_point time_point;
#include <windows.h>
#undef min
#undef max
#include <assert.h>
template<class T> std::string Str(const T& src) { return std::to_string(src); }

#include "Base/Platform.h"
#include "Chess/Chess.h"
#include "Chess/Bit.h"
#include "Chess/Pack.h"
#include "Chess/Board.h"
#include "Chess/Score.h"
#include "Chess/Move.h"
#include "Chess/Killer.h"
#include "Chess/Piece.h"
#include "Chess/Material.h"
#include "Chess/PawnEval.h"
#include "Chess/Eval.h"
#include "Chess/PasserEval.h"
#include "Chess/Locus.h"
#include "Chess/Weights.h"
#include "Chess/Magic.h"
#include "Chess/Futility.h"
#include "Chess/Shared.h"
#include "Chess/Roc.h"

//#include "TunerParams.inc"

using Gull::Board_;
using std::array;


CommonData_ DATA;
CommonData_* const& RO = &DATA;	// generally we access DATA through RO

// Constants controlling play
constexpr int PliesToEvalCut = 50;	// halfway to 50-move
constexpr int KingSafetyNoQueen = 8;	// numerator; denominator is 16
constexpr int SeeThreshold = 40 * CP_EVAL;
constexpr int DrawCapConstant = 110 * CP_EVAL;
constexpr int DrawCapLinear = 0;	// numerator; denominator is 64
constexpr int DeltaDecrement = (3 * CP_SEARCH) / 2;	// 5 (+91/3) vs 3
int TBMinDepth = 2;

constexpr int InitiativeConst = int(1.5 * CP_SEARCH);
constexpr int InitiativePhase = int(4.5 * CP_SEARCH);

struct NoWatch_
{
	template<class T_> bool operator()(const char*, bool m, T_) const { return m; }
	template<class T_> void operator()(const char*, T_) const {}
};

#define IncWatch(var, x, n, loc) (WATCH()(loc, me, x) ? (var -= (n) * (x)) : (var += (n) * (x)))
#define IncVMultiple(var, n, x) IncWatch(var, x, n, #x)				// support tuner
#define IncV(var, x) IncWatch(var, x, 1, #x)				// support tuner
//#define IncV(var, x) (me ? (var -= (x)) : (var += (x)))	// tournament mode
#define DecV(var, x) IncV(var, -(x))
#define NOTICE(x) WATCH()(#x, x) 


constexpr sint16 KpkValue = 300 * CP_EVAL;
constexpr sint16 EvalValue = 30000;
constexpr sint16 MateValue = 32760 - 8 * (CP_SEARCH - 1);


/*
general move:
0 - 11: from & to
12 - 15: flags
16 - 23: history
24 - 25: spectial moves: killers, refutations...
26 - 30: MvvLva
delta move:
0 - 11: from & to
12 - 15: flags
16 - 31: sint16 delta + (sint16)0x4000
*/
constexpr array<int, 16> MvvLvaVictim = { 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3 };
constexpr array<int, 16> MvvLvaAttacker = { 0, 0, 5, 5, 4, 4, 3, 3, 3, 3, 2, 2, 1, 1, 6, 6 };
constexpr array<int, 16> MvvLvaAttackerKB = { 0, 0, 9, 9, 7, 7, 5, 5, 5, 5, 3, 3, 1, 1, 11, 11 };

INLINE int PawnCaptureMvvLva(int attacker) { return MvvLvaAttacker[attacker]; }
constexpr int MaxPawnCaptureMvvLva = MvvLvaAttacker[15];  // 6
INLINE int KnightCaptureMvvLva(int attacker) { return MaxPawnCaptureMvvLva + MvvLvaAttackerKB[attacker]; }
constexpr int MaxKnightCaptureMvvLva = MaxPawnCaptureMvvLva + MvvLvaAttackerKB[15];  // 17
INLINE int BishopCaptureMvvLva(int attacker) { return MaxPawnCaptureMvvLva + MvvLvaAttackerKB[attacker] + 1; }
constexpr int MaxBishopCaptureMvvLva = MaxPawnCaptureMvvLva + MvvLvaAttackerKB[15] + 1;  // usually 18
INLINE int RookCaptureMvvLva(int attacker) { return MaxBishopCaptureMvvLva + MvvLvaAttacker[attacker]; }
constexpr int MaxRookCaptureMvvLva = MaxBishopCaptureMvvLva + MvvLvaAttacker[15];  // usually 24
INLINE int QueenCaptureMvvLva(int attacker) { return MaxRookCaptureMvvLva + MvvLvaAttacker[attacker]; }


INLINE int MvvLvaXrayCap(int capture) { return MvvLva[WhiteKing][capture]; }



constexpr int RefOneScore = (0xFF << 16) | (3 << 24);
constexpr int RefTwoScore = (0xFF << 16) | (2 << 24);

INLINE int ExtToFlag(int ext)
{
	return ext << 16;
}
INLINE int ExtFromFlag(int flags)
{
	return (flags >> 16) & 0xF;
}
constexpr int FlagHashCheck = 1 << 20;  // first 20 bits are reserved for the hash killer and extension
constexpr int FlagHaltCheck = 1 << 21;
constexpr int FlagCallEvaluation = 1 << 22;
constexpr int FlagDisableNull = 1 << 23;
constexpr int FlagNeatSearch = FlagHashCheck | FlagHaltCheck | FlagCallEvaluation;
constexpr int FlagNoKillerUpdate = 1 << 24;
constexpr int FlagReturnBestMove = 1 << 25;

typedef struct
{
	array<uint8, 64> square;
	uint64 key, pawn_key;
	packed_t material, pst;
	uint16 move;
	uint8 turn, castle_flags, ply, ep_square, piece, capture;
} GPosData;

typedef struct
{
	array<uint16, 2> moves_;
} Ref1_;

struct TimeLimits_
{
	time_point start_;
	uint64 softLimit_, hardLimit_;
} TheTimeLimit;

template<typename T_, int N> struct Circle_
{
	array<T_, N> vals_ = {};
	int loc_ = 0;
	void push(T_ val)
	{
		vals_[loc_++] = val;
		loc_ %= N;
	}
	bool same() const
	{
		return adjacent_find(vals_.begin(), vals_.end(), std::not_equal_to<T_>()) == vals_.end();
	}
};

struct SearchInfo_
{
	int singular_, hashDepth_;
	bool early_, failLow_, failHigh_;
	Circle_<uint16, 3> moves_;
};

constexpr int N_PAWN_HASH = 1 << 17;
constexpr int PAWN_HASH_MASK = N_PAWN_HASH - 1;
constexpr uint64 N_REF_1 = 4096, N_REF_MULTI = 62717;

struct State_
{
	std::array<PlyState_, MAX_HEIGHT> stack_;
	PlyState_* current_;
	Board_ board_;
	SearchInfo_ searchInfo_;
	std::vector<uint64> hashHist_;

	std::vector<array<array<uint16, 2>, 64>> historyVals_;
	std::vector<sint16> deltaVals_;
	std::vector<Ref1_> ref1_;
	uint64 nodes_, tbHits_;
	int selDepth_;

	std::vector<GPawnEntry> pawnHash_;

	State_() : current_(&stack_[0]), pawnHash_(N_PAWN_HASH), historyVals_(16), deltaVals_(16 * 4096), ref1_(N_REF_1) {}

	void ClearStack() 
	{ 
		memset(&stack_[1], 0, (MAX_HEIGHT - 1) * sizeof(PlyState_)); 
		current_ = &stack_[0];
	}
	void Reset(const State_& exemplar)
	{
		stack_ = exemplar.stack_;
		current_ = &stack_[exemplar.Height()];
		board_ = exemplar.board_;
		searchInfo_ = exemplar.searchInfo_;
		hashHist_ = exemplar.hashHist_;

		historyVals_ = exemplar.historyVals_;
		for (auto& hp : historyVals_)
			for (auto& hs: hp)
				for (auto& hv: hs)
					if (F(hv & 0x00FF))
						hv = 1;

		deltaVals_ = exemplar.deltaVals_;
		ref1_ = exemplar.ref1_;
		nodes_ = tbHits_ = 0;

		if (exemplar.pawnHash_.size() == N_PAWN_HASH)
			pawnHash_ = exemplar.pawnHash_;
	}

	INLINE const PlyState_& operator[](int lookback) const { return *(current_ - lookback); }
	INLINE int Height() const { return static_cast<int>(current_ - &stack_[0]); }

	INLINE const Board_& operator()() const { return board_; }
	INLINE const uint64& operator()(int piece_id) const { return board_.Piece(piece_id); }
};

constexpr uint8 FlagSort = 1 << 0;
constexpr uint8 FlagNoBcSort = 1 << 1;

constexpr sint16 TBMateValue = 31380;
constexpr sint16 TBCursedMateValue = 13;
const int TbValues[5] = { -TBMateValue, -TBCursedMateValue, 0, TBCursedMateValue, TBMateValue };
constexpr int NominalTbDepth = 33;
constexpr int MaxDepth = 125;
inline int TbDepth(int depth) { return Min(depth + NominalTbDepth, 117); }

extern int TB_LARGEST;
unsigned PyrrhicWDL(const State_& state, int depth);


enum
{
	stage_search,
	s_hash_move,
	s_good_cap,
	s_special,
	s_quiet,
	s_bad_cap,
	s_none,
	stage_evasion,
	e_hash_move,
	e_ev,
	e_none,
	stage_razoring,
	r_hash_move,
	r_cap,
	r_checks,
	r_none
};

inline Progress_ Progress(const Board_& board) { return Progress_(popcnt(board.Piece(White)), popcnt(board.Piece(Black))); }

struct GEntry
{
	uint32 key;
	uint16 date;
	uint16 move;
	score_t low;
	score_t high;
	uint8 low_depth;
	uint8 high_depth;
};
constexpr GEntry NullEntry = { 0, 1, 0, 0, 0, 0, 0 };

typedef struct
{
	int knodes;
	int ply;
	uint32 key;
	uint16 date;
	uint16 move;
	score_t value;
	score_t exclusion;
	uint8 depth;
	uint8 ex_depth;
} GPVEntry;
constexpr GPVEntry NullPVEntry = { 0, 0, 0, 1, 0, 0, 0, 0, 0 };
constexpr int N_PV_HASH = 1 << 19;
constexpr int PV_CLUSTER = 1 << 2;
constexpr int PV_HASH_MASK = N_PV_HASH - PV_CLUSTER;
constexpr int MAX_MOVES = 256;

std::vector<int> RootList;

template<class T> void prefetch(T* p)
{
	_mm_prefetch(reinterpret_cast<const char*>(p), _MM_HINT_NTA);
}

template<bool me> INLINE int OwnRank(int loc)
{
	return me ? (7 - RankOf(loc)) : RankOf(loc);
}
INLINE int OwnRank(bool me, int loc)
{
	return me ? (7 - RankOf(loc)) : RankOf(loc);
}

namespace Futility
{
	constexpr std::array<sint16, 10> PieceThreshold = { 12, 18, 22, 24, 25, 26, 27, 26, 40, 40 };	// in CP
	constexpr std::array<sint16, 8> PasserThreshold = { 0, 0, 0, 0, 0, 20, 40, 0 };

	template<bool me> inline sint16 x(const State_& state)
	{
		sint16 retval = PieceThreshold[pop0(state().NonPawnKing(me))];
		if (uint64 passer = state[0].passer & state().Pawn(me))
			retval = Max(retval, PasserThreshold[OwnRank<me>(NB<opp>(passer))]);
		return retval;
	}

	template<bool me> inline sint16 HashCut(const State_& state, bool did_delta_moves)
	{
		return (did_delta_moves ? 4 : 8) * x<me>(state);
	}
	template<bool me> inline sint16 CheckCut(const State_& state)
	{
		return 11 * x<me>(state);
	}
	template<bool me> inline sint16 DeltaCut(const State_& state)
	{
		return HashCut<me>(state, false);
	}
	template<bool me> inline sint16 ScoutCut(const State_& state, int depth)
	{
		return (depth > 3 ? 4 : 7) * x<me>(state);
	}
};

#ifdef HNI
inline uint64 BishopAttacks(int sq, const uint64& occ)
{
	return  RO->BMagic_.Attacks[Magic::BOffset[sq] + _pext_u64(occ, RO->BMagic_.Mask[sq])];
}
inline uint64 RookAttacks(int sq, const uint64& occ)
{
	return RO->RMagic_.Attacks[Magic::ROffset[sq] + _pext_u64(occ, RO->RMagic_.Mask[sq])];
}
#else
inline uint64 BishopAttacks(int sq, const uint64& occ)
{
	return RO->BMagic_.attacks_[Magic::BOffset[sq] + (((RO->BMagic_.masks_[sq] & occ) * Magic::BMagic[sq]) >> Magic::BShift[sq])];
}
inline uint64 RookAttacks(int sq, const uint64& occ)
{
	return RO->RMagic_.attacks_[Magic::ROffset[sq] + (((RO->RMagic_.masks_[sq] & occ) * Magic::RMagic[sq]) >> Magic::RShift[sq])];
}
#endif
INLINE uint64 QueenAttacks(int sq, const uint64& occ)
{
	return BishopAttacks(sq, occ) | RookAttacks(sq, occ);
}

#define kingAttacks(sq) KAtt[sq]
#define rookAttacks RookAttacks
#define bishopAttacks BishopAttacks
#define knightAttacks(sq) NAtt[sq]
#define pawnAttacks(turn, sq) PAtt[turn][sq]
#define popcount pop1
inline int poplsb(uint64* bb)
{
	int retval = lsb(*bb);
	*bb &= *bb - 1;
	return retval;
}
#include "pyrrhic/tbprobe.cpp"
#undef popcount
#undef pawnAttacks
#undef knightAttacks
#undef bishopAttacks
#undef rookAttacks
#undef kingAttacks
using namespace std;	// only after Pyrrhic


// helper to divide intermediate quantities to form scores
// note that straight integer division (a la Gull) creates an attractor at 0
// we support this, especially for weights inherited from Gull which have not been tuned for Roc
template<int DEN, int SINK = DEN> struct Div_
{
	constexpr int operator()(int x) const
	{
		constexpr int shift = std::numeric_limits<int>::max() / (2 * DEN);
		constexpr int shrink = (SINK - DEN) / 2;
		const int y = x > 0 ? Max(0, x - shrink) : Min(0, x + shrink);
		return (y + DEN * shift) / DEN - shift;
	}
};

namespace PstW
{
	struct Weights_
	{
		struct Phase_
		{
			array<int, 4> quad_;
			array<int, 4> linear_;
			array<int, 2> quadMixed_;
		} op_, md_, eg_, cl_;
	};

	constexpr Weights_ Pawn = {
		{ { -48, -275, 165, 0 },{ -460, -357, -359, 437 },{ 69, -28 } },
		{ { -85, -171, 27, 400 },{ -160, -133, 93, 1079 },{ 13, -6 } },
		{ { -80, -41, -85, 782 },{ 336, 303, 295, 1667 },{ -35, 13 } },
		{ { 2, 13, 11, 23 },{ 6, 14, 37, -88 },{ 14, -2 } } };
	constexpr Weights_ Knight = {
		{ { -134, 6, -12, -72 },{ -680, -343, -557, 1128 },{ -32, 14 } },
		{ { -315, -123, -12, -90 },{ -449, -257, -390, 777 },{ -24, -3 } },
		{ { -501, -246, -12, -107 },{ 61, -274, -357, 469 },{ -1, -16 } },
		{ { -12, -5, -2, -22 },{ 96, 69, -64, -23 },{ -5, -8 } } };
	constexpr Weights_ Bishop = {
		{ { -123, -62, 54, -116 },{ 24, -486, -350, -510 },{ 8, -58 } },
		{ { -168, -49, 24, -48 },{ -323, -289, -305, -254 },{ -7, -21 } },
		{ { -249, -33, 4, -14 },{ -529, -232, -135, 31 },{ -32, 0 } },
		{ { 4, -10, 9, -13 },{ 91, -43, -34, 29 },{ -13, -10 } } };
	constexpr Weights_ Rook = {
		{ { -260, 12, -49, 324 },{ -777, -223, 245, 670 },{ -7, -25 } },
		{ { -148, -88, -9, 165 },{ -448, -278, -63, 580 },{ -7, 0 } },
		{ { 13, -149, 14, 46 },{ -153, -225, -246, 578 },{ -6, 16 } },
		{ { 0, 8, -15, 8 },{ -32, -29, 10, -51 },{ -6, -23 } } };
	constexpr Weights_ Queen = {
		{ { -270, -18, -19, -68 }, { -520, 444, 474, -186 }, { 18, -6 } },
		{ { -114, -209, 21, -103 }, { -224, -300, 73, 529 }, { -13, 1 } },
		{ { 2, -341, 58, -160 }, { 40, -943, -171, 1328 }, { -34, 27 } },
		{ { -3, -26, 9, 5 }, { -43, -18, -107, 60 }, { 5, 12 } } };
	constexpr Weights_ King = {
		{ { -266, -694, -12, 170 }, { 1077, 3258, 20, -186 }, { -18, 3 } },
		{ { -284, -451, -31, 43 }, { 230, 1219, -425, 577 }, { -1, 5 } },
		{ { -334, -157, -67, -93 }, { -510, -701, -863, 1402 }, { 37, -8 } },
		{ { 22, 14, -16, 0 }, { 7, 70, 40,  78 }, { 9, -3 } } };
}

constexpr std::array<std::array<packed_t, 64>, 16> MakePst()
{
	constexpr std::array<sint8, 8> DistC = { 3, 2, 1, 0, 0, 1, 2, 3 };
	constexpr std::array<sint8, 8> RankR = { -3, -2, -1, 0, 1, 2, 3, 4 };

	std::array<std::array<packed_t, 64>, 16> retval = {};
	for (int i = 0; i < 64; ++i)
	{
		int r = RankOf(i);
		int f = FileOf(i);
		int d = f > r ? f - r : r - f;
		int e = f + r > 7 ? f + r - 7 : 7 - f - r;
		array<int, 4> distL = { DistC[f], DistC[r],  RankR[d] + RankR[e], RankR[r] };
		array<int, 4> distQ = { DistC[f] * DistC[f], DistC[r] * DistC[r], RankR[d] * RankR[d] + RankR[e] * RankR[e], RankR[r] * RankR[r] };
		array<int, 2> distM = { DistC[f] * DistC[r], DistC[f] * RankR[r] };
		array<const PstW::Weights_*, 6> weights = { &PstW::Pawn, &PstW::Knight, &PstW::Bishop, &PstW::Rook, &PstW::Queen, &PstW::King };
		for (int j = 2; j < 16; j += 2)
		{
			int index = PieceType[j];
			const PstW::Weights_& src = *weights[index];
			int op = 0, md = 0, eg = 0, cl = 0;
			for (int k = 0; k < 2; ++k)
			{
				op += src.op_.quadMixed_[k] * distM[k];
				md += src.md_.quadMixed_[k] * distM[k];
				eg += src.eg_.quadMixed_[k] * distM[k];
				cl += src.cl_.quadMixed_[k] * distM[k];
			}
			for (int k = 0; k < 4; ++k)
			{
				op += src.op_.quad_[k] * distQ[k] + src.op_.linear_[k] * distL[k];
				md += src.md_.quad_[k] * distQ[k] + src.md_.linear_[k] * distL[k];
				eg += src.eg_.quad_[k] * distQ[k] + src.eg_.linear_[k] * distL[k];
				cl += src.cl_.quad_[k] * distQ[k] + src.cl_.linear_[k] * distL[k];
			}
			// Regularize(&op, &md, &eg);
			Div_<64> d64;
			retval[j][i] = Pack(d64(op), d64(md), d64(eg), d64(cl));
		}
	}

	retval[WhiteKnight][56] -= Pack(100 * CP_EVAL, 0);
	retval[WhiteKnight][63] -= Pack(100 * CP_EVAL, 0);
	// now for black
	for (int i = 0; i < 64; ++i)
		for (int j = 3; j < 16; j += 2)
		{
			auto src = retval[j - 1][63 - i];
			retval[j][i] = Pack(-Opening(src), -Middle(src), -Endgame(src), -Closed(src));
		}

	return retval;
}
constexpr std::array<std::array<packed_t, 64>, 16> PstVals = MakePst();

INLINE packed_t Pst(int piece, int sq)
{
	return PstVals[piece][sq];
};

INLINE int* AddMove(int* list, int from, int to, int flags, int score)
{
	*list = ((from) << 6) | (to) | (flags) | (score);
	return ++list;
}
INLINE int* AddCapturePP(int* list, int att, int vic, int from, int to)
{
	return AddMove(list, from, to, 0, MvvLva[att][vic]);
}
INLINE int* AddCaptureP(int* list, const Board_& board, int piece, int from, int to)
{
	return AddCapturePP(list, piece, board.PieceAt(to), from, to);
}
INLINE int* AddCaptureP(int* list, const Board_& board, int piece, int from, int to, uint8 min_vic)
{
	return AddCapturePP(list, piece, Max(min_vic, board.PieceAt(to)), from, to);
}
INLINE int* AddCapture(int* list, const Board_& board, int from, int to)
{
	return AddCaptureP(list, board, board.PieceAt(from), from, to);
}

INLINE uint16 JoinFlag(uint16 move)
{
	return (move & FlagCastling) ? 1 : 0;
}
INLINE uint16& HistoryScore(State_* state, int join, int piece, int from, int to)
{
	return state->historyVals_[piece][to][join];
}
INLINE int HistoryMerit(uint16 hs)
{
	return hs / (1 | ((hs & 0x00FF) << 1));
}
INLINE int HistoryP(State_* state, int join, int piece, int from, int to)
{
	return HistoryMerit(HistoryScore(state, join, piece, from, to)) << 16;
}
INLINE int History(State_* state, int join, int from, int to)
{
	return HistoryP(state, join, state->board_.PieceAt(from), from, to);
}
INLINE uint16& HistoryM(State_* state, int move)
{
	return HistoryScore(state, JoinFlag(move), state->board_.PieceAt(From(move)), From(move), To(move));
}
INLINE int HistoryInc(int depth)
{
	return Square(Min((depth) >> 1, 8));
}
INLINE void HistoryBad(uint16* hist, int inc)
{
	if ((*hist & 0x00FF) >= 256 - inc)
		*hist = ((*hist & 0xFEFE) >> 1);
	*hist += inc;
}
INLINE void HistoryBad(State_* state, int move, int depth)
{
	HistoryBad(&HistoryM(state, move), HistoryInc(depth));
}
INLINE void HistoryGood(uint16* hist, int inc)
{
	HistoryBad(hist, inc);
	*hist += inc << 8;
}
INLINE void HistoryGood(State_* state, int move, int depth)
{
	HistoryGood(&HistoryM(state, move), HistoryInc(depth));
}
INLINE int* AddHistoryP(State_* state, int* list, int piece, int from, int to, int flags)
{
	return AddMove(list, from, to, flags, HistoryP(state, JoinFlag(flags), piece, from, to));
}
INLINE int* AddHistoryP(State_* state, int* list, int piece, int from, int to, int flags, uint8 p_min)
{
	return AddMove(list, from, to, flags, max(int(p_min) << 16, HistoryP(state, JoinFlag(flags), piece, from, to)));
}

INLINE sint16& DeltaScore(State_* state, int piece, int from, int to)
{
	return state->deltaVals_[(piece << 12) | (from << 6) | to];
}
INLINE sint16& Delta(State_* state, int from, int to)
{
	return DeltaScore(state, state->board_.PieceAt(from), from, to);
}
INLINE sint16& DeltaM(State_* state, int move)
{
	return Delta(state, From(move), To(move));
}
INLINE int* AddCDeltaP(State_* state, int* list, int margin, int piece, int from, int to, int flags)
{
	return DeltaScore(state, piece, from, to) < margin
			? list
			: AddMove(list, from, to, flags, (DeltaScore(state, piece, from, to) + 0x4000) << 16);
}

#ifdef CPU_TIMING
int CpuTiming = 0, UciMaxDepth = 0, UciMaxKNodes = 0, UciBaseTime = 1000, UciIncTime = 5;
int GlobalTime[2] = { 0, 0 };
int GlobalInc[2] = { 0, 0 };
int GlobalTurn = 0;
constexpr sint64 CyclesPerMSec = 3400000;
#endif
constexpr int Aspiration = 1, LargePages = 1;
constexpr int TimeSingTwoMargin = 20;
constexpr int TimeSingOneMargin = 30;
constexpr int TimeNoPVSCOMargin = 60;
constexpr int TimeNoChangeMargin = 70;
constexpr int TimeRatio = 120;
constexpr int PonderRatio = 120;
constexpr int InfoLag = 5000;
constexpr int InfoDelay = 1000;
time_point StartTime, InfoTime, CurrTime;
uint16 SMoves[256];

jmp_buf Jump, ResetJump;
HANDLE StreamHandle;

INLINE int ExclSingle(int depth)
{
	return 8 * CP_SEARCH;
}
INLINE int ExclDouble(int depth)
{
	return 16 * CP_SEARCH;
}

// EVAL

const sint8 DistC[8] = { 3, 2, 1, 0, 0, 1, 2, 3 };
const sint8 RankR[8] = { -3, -2, -1, 0, 1, 2, 3, 4 };

constexpr uint16 SeeValue[16] = { 0, 0, 360, 360, 1300, 1300, 1300, 1300, 1300, 1300, 2040, 2040, 3900, 3900, 30000, 30000 };
constexpr array<int, 5> Phase = { 0, SeeValue[4], SeeValue[6], SeeValue[10], SeeValue[12] };
constexpr int PhaseMin = 2 * Phase[3] + Phase[1] + Phase[2];
constexpr int PhaseMax = 16 * Phase[0] + 3 * Phase[1] + 3 * Phase[2] + 4 * Phase[3] + 2 * Phase[4];

#define V(x) (x)

template<class T_> constexpr auto Av(const T_& x, int width, int row, int column) -> decltype(x[0])
{
	return x[row * width + column];
}
template<class T_> constexpr auto TrAv(const T_& x, int w, int r, int c) -> decltype(x[0])
{
	return x[(r * (2 * w - r + 1)) / 2 + c];
}

template<int N> constexpr array<packed_t, N / 4> PackAll(const array<int, N>& src)
{
	const int M = N / 4;
	array<packed_t, M> dst;
	for (int ii = 0; ii < M; ++ii)
		dst[ii] = Pack(src[4 * ii], src[4 * ii + 1], src[4 * ii + 2], src[4 * ii + 3]);
	return dst;
}



// EVAL WEIGHTS

// pawn, knight, bishop, rook, queen, pair
constexpr array<int, 6> MatLinear = { 39, -11, -14, 86, -15, -1 };
constexpr int MatWinnable = 1;

// T(pawn), pawn, knight, bishop, rook, queen
const int MatQuadMe[21] = { // tuner: type=array, var=1000, active=0
	NULL, 0, 0, 0, 0, 0,
	-33, 17, -23, -155, -247,
	15, 296, -105, -83,
	-162, 327, 315,
	-861, -1013,
	NULL
};
const int MatQuadOpp[15] = { // tuner: type=array, var=1000, active=0
	0, 0, 0, 0, 0,
	-14, -96, -20, -278,
	35, 39, 49,
	9, -2,
	75
};
const int BishopPairQuad[9] = { // tuner: type=array, var=1000, active=0
	-38, 164, 99, 246, -84, -57, -184, 88, -186
};
constexpr array<int, 6> MatClosed = { -20, 22, -33, 18, -2, 26 };

namespace Values
{
	static const packed_t MatRB = Pack(52, 0, -52, 0);
	static const packed_t MatRN = Pack(40, 2, -36, 0);
	static const packed_t MatQRR = Pack(32, 40, 48, 0);
	static const packed_t MatQRB = Pack(16, 20, 24, 0);
	static const packed_t MatQRN = Pack(20, 28, 36, 0);
	static const packed_t MatQ3 = Pack(-12, -22, -32, 0);
	static const packed_t MatBBR = Pack(-10, 20, 64, 0);
	static const packed_t MatBNR = Pack(6, 21, 20, 0);
	static const packed_t MatNNR = Pack(0, -12, -24, 0);
	static const packed_t MatM = Pack(4, 8, 12, 0);
	static const packed_t MatPawnOnly = Pack(0, 0, 0, -50);
}

// coefficient (Linear, Log, Locus) * phase (4)
constexpr array<int, 12> MobCoeffsKnight = { 1281, 857, 650, 27, 2000, 891, 89, -175, 257, 206, 0, 163 };
constexpr array<int, 12> MobCoeffsBishop = { 1484, 748, 558, 127, 1687, 1644, 1594, -565, 0, 337, 136, 502 };
constexpr array<int, 12> MobCoeffsRook = { 1096, 887, 678, 10, -565, 248, 1251, -5, 74, 72, 45, -12 };
constexpr array<int, 12> MobCoeffsQueen = { 597, 876, 1152, -7, 1755, 324, -1091, -9, 78, 100, 17, -12 };
constexpr int N_LOCUS = 22;

// file type (3) * distance from 2d rank/open (5)
constexpr array<int, 15> ShelterValue = {  // tuner: type=array, var=26, active=0
	8, 36, 44, 0, 0,	// h-pawns
	48, 72, 44, 0, 8,	// g
	96, 28, 32, 0, 0	// f
};

enum
{
	StormHofValue,
	StormHofScale,
	StormOfValue,
	StormOfScale
};
constexpr array<int, 4> ShelterMod = { 0, 0, 88, 0 };

namespace StormValues
{
	constexpr std::array<sint16, 4> Blocked = { 3, 11, 30, 58 };
	constexpr std::array<sint16, 4> ShelterAtt = { 6, 25, 71, 143 };
	constexpr std::array<sint16, 4> Connected = { 17, 53, 126, 236 };
	constexpr std::array<sint16, 4> Open = { 12, 34, 73, 128 };
	constexpr std::array<sint16, 4> Free = { 0, 4, 15, 34 };
}

namespace PasserValues
{
	// not much point in using 3 parameters for 4 degrees of freedom
	constexpr array<packed_t, 7> Candidate = { 0ull, 0ull, 0ull, Pack(10, 10, 0, 0), Pack(26, 24, 5, 0), Pack(49, 42, 17, 0), Pack(79, 64, 37, 0) };	// 3-wide group where our pawns outnumber his
	constexpr array<packed_t, 7> General = { 0ull, 0ull, 0ull, Pack(6, 4, 3, 14), Pack(31, 16, 6, 11), Pack(56, 48, 18, 7), Pack(81, 91, 36, 4) };
	constexpr array<packed_t, 7> Protected = { 0ull, 0ull, 0ull, Pack(0, 5, 28, 11), Pack(23, 53, 66, 26), Pack(91, 138, 148, 10), Pack(174, 242, 261, 0) };	// supported by our pawn
	constexpr array<packed_t, 7> Outside = { 0ull, 0ull, 0ull, Pack(20, 18, 10, 3), Pack(54, 40, 20, 0), Pack(87, 76, 21, 0), Pack(120, 123, 16, 0) };	// is easternmost/westernmost of all pawns
	constexpr array<packed_t, 7> Movable = { 0ull, 0ull, 0ull, Pack(21, 18, 19, 21), Pack(58, 51, 37, 20), Pack(103, 113, 61, 15), Pack(154, 189, 89, 11) };	// can be pushed now
	constexpr array<packed_t, 7> Clear = { 0ull, 0ull, 0ull, Pack(10, 11, 12, 0), Pack(30, 33, 36, 0), Pack(68, 74, 80, 0), Pack(121, 131, 142, 0) };	// no opponent pieces in path
	constexpr array<packed_t, 7> Connected = { 0ull, 0ull, 0ull, Pack(12, 10, 11, 0), Pack(30, 29, 30, 0), Pack(57, 66, 56, 13), Pack(92, 112, 79, 36) }; // clear && directly beside another passer
	constexpr array<packed_t, 7> Free = { 0ull, 0ull, 0ull, Pack(53, 49, 72, 0), Pack(95, 124, 166, 0), Pack(116, 274, 378, 3), Pack(121, 468, 672, 6) };	// clear && no sq
	constexpr array<packed_t, 7> Supported = { 0ull, 0ull, 0ull, Pack(41, 36, 33, 5), Pack(90, 84, 77, 2), Pack(141, 157, 172, 0), Pack(194, 246, 297, 0) };	// clear && directly backed by major
}

// type (2: att, def) * scaling (2: linear, log) 
constexpr array<int, 4> PasserAttDefQuad = { // tuner: type=array, var=500, active=0
	764, 204, 332, 76
};
constexpr array<int, 4> PasserAttDefLinear = { // tuner: type=array, var=500, active=0
	2536, 16, 932, 264
};
constexpr array<int, 4> PasserAttDefConst = { // tuner: type=array, var=500, active=0
	0, 0, 0, 0
};
enum { PasserOnePiece, PasserOpKingControl, PasserOpMinorControl, PasserOpRookBlock };
// case(4) * phase(3 -- no opening)
constexpr array<int, 12> PasserSpecial = { // tuner: type=array, var=100, active=0
	26, 52, 0
};
namespace Values
{
	constexpr packed_t PasserOpRookBlock =
		Pack(0, Av(PasserSpecial, 3, ::PasserOpRookBlock, 0), Av(PasserSpecial, 3, ::PasserOpRookBlock, 1), Av(PasserSpecial, 3, ::PasserOpRookBlock, 2));
}

namespace Values
{
	constexpr packed_t IsolatedOpen = Pack(36, 28, 19, 1);
	constexpr packed_t IsolatedClosed = Pack(40, 21, 1, 12);
	constexpr packed_t IsolatedBlocked = Pack(-40, -20, -3, -3);
	constexpr packed_t IsolatedDoubledOpen = Pack(0, 10, 45, 3);
	constexpr packed_t IsolatedDoubledClosed = Pack(27, 27, 36, 8);

	constexpr packed_t UpBlocked = Pack(18, 45, 31, -6);
	constexpr packed_t PasserTarget = Pack(-16, -36, -38, 22);
	constexpr packed_t PasserTarget2 = Pack(-3, -10, -39, 9);
	constexpr packed_t ChainRoot = Pack(7, -3, -3, -14);

	constexpr packed_t BackwardOpen = Pack(77, 63, 42, -8);
	constexpr packed_t BackwardClosed = Pack(21, 11, 12, -1);

	constexpr packed_t DoubledOpen = Pack(12, 6, 0, 0);
	constexpr packed_t DoubledClosed = Pack(4, 2, 0, 0);

	constexpr packed_t RookHof = Pack(32, 16, 0, 0);
	constexpr packed_t RookHofWeakPAtt = Pack(8, 4, 0, 0);
	constexpr packed_t RookOf = Pack(44, 38, 32, 0);
	constexpr packed_t RookOfOpen = Pack(-4, 2, 8, 0);
	constexpr packed_t RookOfMinorFixed = Pack(-4, -4, -4, 0);
	constexpr packed_t RookOfMinorHanging = Pack(56, 26, -4, 0);
	constexpr packed_t RookOfKingAtt = Pack(20, 0, -20, 0);
	constexpr packed_t Rook7th = Pack(-20, -10, 0, 0);
	constexpr packed_t Rook7thK8th = Pack(-24, 4, 32, 0);
	constexpr packed_t Rook7thDoubled = Pack(-28, 48, 124, 0);

	constexpr packed_t TacticalQueenPawn = Pack(4, 1, 3, 3);
	constexpr packed_t TacticalQueenMinor = Pack(53, 20, 69, -7);
	constexpr packed_t TacticalRookPawn = Pack(6, 11, 37, 22);
	constexpr packed_t TacticalRookMinor = Pack(29, 29, 66, 10);
	constexpr packed_t TacticalBishopPawn = Pack(0, 28, 35, 30);
	constexpr packed_t TacticalB2N = Pack(26, 59, 71, 30);
	constexpr packed_t TacticalN2B = Pack(89, 78, 74, 20);	

	constexpr packed_t Threat = Pack(79, 64, 45, -3);
	constexpr packed_t ThreatDouble = Pack(164, 106, 48, 0);

	constexpr packed_t KingDefKnight = Pack(8, 4, 0, 0);
	constexpr packed_t KingDefQueen = Pack(16, 8, 0, 0);

	constexpr packed_t PawnChainLinear = Pack(44, 40, 36, 0);
	constexpr packed_t PawnChain = Pack(36, 26, 16, 0);
	constexpr packed_t PawnBlocked = Pack(0, 18, 36, 0);
	constexpr packed_t PawnRestrictsK = Pack(23, 9, 1, 45);

	constexpr packed_t BishopPawnBlock = Pack(0, 6, 14, 6);
	constexpr packed_t BishopOutpostNoMinor = Pack(60, 60, 45, 0);

	constexpr packed_t KnightOutpost = Pack(40, 36, 24, 0);
	constexpr packed_t KnightOutpostProtected = Pack(41, 31, 0, 0);
	constexpr packed_t KnightOutpostPawnAtt = Pack(44, 38, 18, 0);
	constexpr packed_t KnightOutpostNoMinor = Pack(41, 31, 0, 0);
	constexpr packed_t KnightPawnSpread = Pack(0, 4, 15, -10);
	constexpr packed_t KnightPawnGap = Pack(0, 2, 5, 0);

	constexpr packed_t QueenPawnPin = Pack(34, 44, 42, 59);
	constexpr packed_t QueenSelfPin = Pack(88, 232, -45, 130);
	constexpr packed_t QueenWeakPin = Pack(86, 108, 72, 56);
	constexpr packed_t RookPawnPin = Pack(121, 39, 1, 39);
	constexpr packed_t RookSelfPin = Pack(25, 170, 71, 165);
	constexpr packed_t RookWeakPin = Pack(68, 153, 146, 108);
	constexpr packed_t RookThreatPin = Pack(632, 716, 614, -190);
	constexpr packed_t BishopPawnPin = Pack(58, 130, 106, 46);
	constexpr packed_t BishopSelfPin = Pack(233, 249, 122, 52);
	constexpr packed_t StrongPin = Pack(-16, 136, 262, -22);
	constexpr packed_t BishopThreatPin = Pack(342, 537, 629, -34);

	constexpr packed_t QKingRay = Pack(17, 26, 33, -2);
	constexpr packed_t RKingRay = Pack(-14, 15, 42, 0);
	constexpr packed_t BKingRay = Pack(43, 14, -9, -1);
}

constexpr array<int, 12> KingAttackWeight = {  // tuner: type=array, var=51, active=0
	65, 79, 50, 58, 70, 94, 137, 191, 16, 192, 256, 64 };
constexpr uint16 KingAttackThreshold = 48;

constexpr array<uint64, 2> Outpost = { 0x00007E7E3C000000ull, 0x0000003C7E7E0000ull };
constexpr array<int, 2> PushW = { 7, -9 };
constexpr array<int, 2> Push = { 8, -8 };
constexpr array<int, 2> PushE = { 9, -7 };

constexpr uint32 KingNAttack1 = Pack(1, KingAttackWeight[0]);
constexpr uint32 KingNAttack = Pack(2, KingAttackWeight[1]);
constexpr uint32 KingBAttack1 = Pack(1, KingAttackWeight[2]);
constexpr uint32 KingBAttack = Pack(2, KingAttackWeight[3]);
constexpr uint32 KingRAttack1 = Pack(1, KingAttackWeight[4]);
constexpr uint32 KingRAttack = Pack(2, KingAttackWeight[5]);
constexpr uint32 KingQAttack1 = Pack(1, KingAttackWeight[6]);
constexpr uint32 KingQAttack = Pack(2, KingAttackWeight[7]);
constexpr uint32 KingPAttack = Pack(2, 0);
constexpr uint32 KingPRestrict = Pack(2, 58);
constexpr uint32 KingAttack = Pack(1, 0);
constexpr uint32 KingPAttackInc = Pack(0, KingAttackWeight[8]);
constexpr uint32 KingAttackSquare = KingAttackWeight[9];
constexpr uint32 KingNoMoves = KingAttackWeight[10];
constexpr uint32 KingShelterQuad = KingAttackWeight[11];	// a scale factor, not a score amount

template<int N> array<uint16, N> CoerceUnsigned(const array<int, N>& src)
{
	array<uint16, N> retval;
	for (int ii = 0; ii < N; ++ii)
		retval[ii] = static_cast<uint16>(max(0, src[ii]));
	return retval;
}
constexpr array<uint16, 16> XKingAttackScale = { 0, 1, 1, 2, 4, 5, 8, 12, 15, 19, 23, 28, 34, 39, 39, 39 };

// tuner: stop

// END EVAL WEIGHTS

#define log_msg(...)
#define error_msg(format, ...)                                              \
    do {                                                                \
        log_msg("error_msg: " format "\n", ##__VA_ARGS__);                      \
        fprintf(stderr, "error_msg: " format "\n", ##__VA_ARGS__);          \
        abort();                                                        \
    } while (false)

// data sharing for multithreading
void delete_object(void *addr, size_t size)
{
	if (!UnmapViewOfFile(addr))
		error_msg("failed to unmap object (%d)", GetLastError());
}

// SMP

// Windows threading routines
constexpr size_t PAGE_SIZE = 4096;
constexpr int PIPE_BUF = 4096;
constexpr int PATH_MAX = 4096;
inline size_t size_to_page(size_t size)
{
	return ((size - 1) / PAGE_SIZE) * PAGE_SIZE + PAGE_SIZE;
}
int get_num_cpus()
{
	SYSTEM_INFO sysinfo;
	GetSystemInfo(&sysinfo);
	return sysinfo.dwNumberOfProcessors;
}

string object_name(const char *basename, int id, int idx)
{
	return "Local\\Roc" + to_string(id) + basename + to_string(idx);
}

static DWORD forward_input(void* param)
{
	char buf[4 * PIPE_BUF];
	HANDLE in = GetStdHandle(STD_INPUT_HANDLE);
	HANDLE out = (HANDLE)param;
	while (true)
	{
		DWORD len;
		if (!ReadFile(in, buf, sizeof(buf), &len, NULL))
			error_msg("failed to read input (%d)", GetLastError());
		if (len == 0)
		{
			CloseHandle(out);
			return 0;
		}

		DWORD ptr = 0;
		while (ptr < len)
		{
			DWORD writelen;
			if (!WriteFile(out, buf + ptr, len - ptr, &writelen, NULL))
				error_msg("failed to forward input (%d)", GetLastError());
			ptr += writelen;
		}

		FlushFileBuffers(out);
	}
}

struct AspirationState_
{
	int depth_, alpha_, beta_, delta_;
};
constexpr AspirationState_ ASPIRATION_INIT = { 2, -200, 200, 50 };

struct RootScores_
{
	struct Record_
	{
		uint16 depth_, move_;
		score_t lower_, upper_;
	};
	vector<Record_> results_;

	void Add(uint16 move, score_t score, uint16 depth, score_t alpha, score_t beta)
	{
		if (score <= alpha)
			return;	// nothing learned
		if (depth >= results_.size())
			results_.resize(depth + 1, { 0, 0, -MateValue, -MateValue });
		if (score >= results_[depth].lower_)
		{
			results_[depth] = { depth, move, score, score < beta ? score : MateValue };
			if (TheShare.depth_ < depth)
				TheShare.depth_ = depth;
		}
	}
	void clear() { results_.clear(); }
	bool empty() const 
	{ 
		for (auto r : results_)
			if (r.move_)
				return false;
		return true;
	}
	Record_ best() const
	{
		for (auto r = results_.rbegin(); r != results_.rend(); ++r)
		{
			if (r->move_)
				return *r;
		}
		return { 0, 0, -MateValue, -MateValue };
	}
};

constexpr int MAX_PV_LEN = 124;  // cannot exceed MAX_HEIGHT
struct ThreadOwn_
{
	uint16 iThread_;
	AspirationState_ window_;
	RootScores_ results_;
	vector<int> rootList_;	// may be ordered different from RootList

	vector<int> pvRefDepth_;
	int lastTime_;
};

void SetRootMoves(ThreadOwn_* info)
{
	info->rootList_ = RootList;
	size_t n = RootList.size();
	if (info->iThread_)
	{	// shuffle late moves somewhat; this has no measurable effect on Elo
		for (size_t ii = 2; ii + 1 < n; ++ii)
		{
			size_t peek = (info->iThread_ + ii) % Min<size_t>(Min(ii, n - ii), 8);
			swap(info->rootList_[ii], info->rootList_[ii + peek]);
		}
	}
	info->rootList_.push_back(0);
	info->pvRefDepth_.clear();
}


constexpr size_t HASH_CLUSTER = 4;
size_t HashClusters(int megabytes)
{
	return Max(1 << 16, megabytes << 20) / (HASH_CLUSTER * sizeof(GEntry));
}

struct Settings_
{
	int nThreads = 1;
	int tbMinDepth = 7;
	size_t nHashClusters = HashClusters(16);
	int contempt = 8;
	int wobble = 0;
	unsigned parentPid = numeric_limits<unsigned>::max();
	string tbPath;
} SETTINGS;


vector<GEntry> TheHash(SETTINGS.nHashClusters * HASH_CLUSTER);
INLINE GEntry* HashStart(uint64 key)
{
	size_t iCluster = High32(key) % SETTINGS.nHashClusters;
	return &TheHash[iCluster * HASH_CLUSTER];
}
void ResizeHash(int megabytes)
{
	SETTINGS.nHashClusters = HashClusters(megabytes);
	TheHash.resize(SETTINGS.nHashClusters * HASH_CLUSTER);
	std::fill(TheHash.begin(), TheHash.end(), NullEntry);
}

vector<GPVEntry> ThePVHash(N_PV_HASH);
vector<GPawnEntry> ThePawnHash(N_PAWN_HASH);


void move_to_string(int move, char string[])
{
	assert(move);
	int pos = 0;
	string[pos++] = ((move >> 6) & 7) + 'a';
	string[pos++] = ((move >> 9) & 7) + '1';
	string[pos++] = (move & 7) + 'a';
	string[pos++] = ((move >> 3) & 7) + '1';
	if (IsPromotion(move))
	{
		if ((move & 0xF000) == FlagPQueen)
			string[pos++] = 'q';
		else if ((move & 0xF000) == FlagPKnight)
			string[pos++] = 'n';
		else if ((move & 0xF000) == FlagPRook)
			string[pos++] = 'r';
		else if ((move & 0xF000) == FlagPBishop)
			string[pos++] = 'b';
	}
	string[pos] = 0;
}

int move_from_string(const State_& state, char string[])
{
	int from, to, move;
	from = ((string[1] - '1') * 8) + (string[0] - 'a');
	to = ((string[3] - '1') * 8) + (string[2] - 'a');
	move = (from << 6) | to;
	if (state().square[from] >= WhiteKing && abs(to - from) == 2)
		move |= FlagCastling;
	if (T(state[0].ep_square) && to == state[0].ep_square)
		move |= FlagEP;
	if (string[4] != 0)
	{
		if (string[4] == 'q')
			move |= FlagPQueen;
		else if (string[4] == 'n')
			move |= FlagPKnight;
		else if (string[4] == 'r')
			move |= FlagPRook;
		else if (string[4] == 'b')
			move |= FlagPBishop;
	}
	return move;
}

INLINE int lsb(uint64 x);
INLINE int msb(uint64 x);
INLINE int popcnt(uint64 x);
INLINE int MSBZ(const uint64& x)
{
	return x ? msb(x) : 63;
}
INLINE int LSBZ(const uint64& x)
{
	return x ? lsb(x) : 0;
}
template<bool me> int NB(const uint64& x)
{
	return me ? msb(x) : lsb(x);
}
template<bool me> int NBZ(const uint64& x)
{
	return me ? MSBZ(x) : LSBZ(x);
}

template<int me> inline uint64 PAtts(uint64 p)
{
	uint64 temp = Shift<me>(p);
	return ((temp & 0xFEFEFEFEFEFEFEFE) >> 1) | ((temp & 0x7F7F7F7F7F7F7F7F) << 1);
}

INLINE uint8 FileOcc(uint64 occ)
{
	uint64 t = occ;
	t |= t >> 32;
	t |= t >> 16;
	t |= t >> 8;
	return static_cast<uint8>(t & 0xFF);
}

constexpr std::array<int, 256> MakeSpanWidth()
{
	std::array<int, 256> retval;
	retval[0] = 0;
	for (int i = 0; i < 256; ++i)
		retval[i] = msb_c(i) - lsb_c(i);
	return retval;
}
constexpr std::array<int, 256> MakeSpanGap()
{
	std::array<int, 256> retval;
	retval[0] = 0;
	for (int i = 1; i < 256; ++i)
	{
		retval[i] = 0;
		for (int j = 0, last = 9; j < 8; ++j)
		{
			if (i & Bit(j))
				last = j;
			else
				retval[i] = max(retval[i], j - 1 - last);
		}
	}
	return retval;
}
constexpr std::array<int, 256> SpanWidth = MakeSpanWidth(), SpanGap = MakeSpanGap();


INLINE int FileSpan(const uint64& occ)
{
	return SpanWidth[FileOcc(occ)];
}


bool IsIllegal(const State_& state, int move)
{
	int me = state.current_->turn;
	const Board_& board = state();
	return ((HasBit(state[0].xray[opp], From(move)) && F(Bit(To(move)) & FullLine[lsb(board.King(me))][From(move)])) ||
		(IsEP(move) && T(Line[RankOf(From(move))] & board.King(me)) && T(Line[RankOf(From(move))] & board.Major(opp)) &&
			T(RookAttacks(lsb(board.King(me)), board.PieceAll() ^ Bit(From(move)) ^ Bit(state[0].ep_square - Push[me])) & board.Major(opp))));
};
INLINE bool IsCheck(const State_& state, bool me)
{
	return T(state[0].att[(me) ^ 1] & state().King(me));
};
INLINE bool IsRepetition(const State_& state, int margin, int move)
{
	return margin > 0
		&& state[0].ply >= 2
		&& (state.Height() > 1 && state[1].move == ((To(move) << 6) | From(move)))
		&& F(state().PieceAt(To(move)))
		&& F((move) & 0xF000);
};

uint16 Rand16()
{
	static uint64 seed = 1;
	seed = (seed * 6364136223846793005ull) + 1442695040888963407ull;
	return static_cast<uint16>((seed >> 32) & 0xFFFF);
}

inline uint32 Rand32()
{
	return static_cast<uint32>(Rand16()) << 16 | Rand16();
}

uint64 Rand64()
{
	return static_cast<uint64>(Rand32()) << 32 | Rand32();
}

constexpr uint64 REF_TURN_MASK = 1, REF_CHECK_MASK = 2;
INLINE Ref1_& FindRef1(State_* state, uint64_t hash_delta)
{
	return state->ref1_[hash_delta % N_REF_1];
}
INLINE const Ref1_& FindRef1(const State_& state, uint64_t hash_delta)
{
	return state.ref1_[hash_delta % N_REF_1];
}

template<bool CHECK> inline uint64 HashDelta(const State_& state, int height = 1)
{
	if (state.Height() < height)
		return 0;
	uint64 hash_delta = state.current_->key ^ (state.current_ - 1)->key;
	if (state.current_->turn)
		hash_delta ^= REF_TURN_MASK;
	if (CHECK)
		hash_delta ^= REF_CHECK_MASK;
	return hash_delta;
}

template<bool CHECK> INLINE void UpdateRef(State_* state, int ref_move)
{
	uint64 hashDelta = HashDelta<CHECK>(*state);
	if (!hashDelta)
		return;
	auto& dst = FindRef1(state, hashDelta);
	if (dst.moves_[0] == ref_move)
		dst.moves_[1] = ref_move;	// looks weird but works
	else
		dst.moves_[0] = ref_move;
}

template<bool me, bool CHECK> array<uint16, N_REF_TRY> Refutations(const State_& state)
{
	array<uint16, N_REF_TRY> retval = {};
	int ii = 0;
	auto append = [&](uint16 move)
		{
			if (!is_legal<me>(state, move) || IsIllegal(state, move))
				return false;
			retval[ii] = move;
			return ii == N_REF_TRY;
		};
	if (uint64 delta = HashDelta<CHECK>(state))
	{
		for (auto move : FindRef1(state, delta).moves_)
			append(move);
	}
	return retval;
}


// DEBUG debug cry for help
static int debugLine;
static bool boardExists = 0;
static bool debugWK = 1;
static bool debugBK = 1;
static std::ofstream SHOUT("C:\\dev\\debug.txt");
constexpr int TheMemorySize = 200;
struct MemEntry_
{
	PlyState_ d_;
	Board_ b_;
	int line_;
};
array<MemEntry_, TheMemorySize> TheImages;
thread_local int TheImageLoc = 0;

struct MoveScope_
{
	MoveScope_() {
		boardExists = 1;
	}
	~MoveScope_() {
		boardExists = 0;
	}
};
void AccessViolation(const State_& state, uint64 seed)	// any nonzero input should fail
{
	cout << (Str(state[0].patt[(seed >> 32) | (seed << 32)]));
}
void UpdateDebug(const State_& state, int line)
{
	debugLine = line;
	//AccessViolation(boardExists && !King(0));
	//AccessViolation(boardExists && !King(1));
	TheImages[TheImageLoc].b_ = state();
	TheImages[TheImageLoc].d_ = state[0];
	TheImages[TheImageLoc].line_ = line;
	if (++TheImageLoc == TheMemorySize)
		TheImageLoc = 0;
}


constexpr std::array<std::array<uint64, 64>, 2> MakeBishopForward()
{
	std::array<std::array<uint64, 64>, 2> retval = PWay;
	for (int i = 0; i < 64; ++i)
	{
		for (int j = 0; j < 64; j++)
		{
			for (int me = 0; me < 2; ++me)
			{
				retval[me][i] = PWay[me][i];
				if ((PWay[1 ^ me][j] | Bit(j)) & BMask[i] & Forward[me][RankOf(i)])
					retval[me][i] |= Bit(j);
			}
		}
	}
	return retval;
}
constexpr std::array<std::array<uint64, 64>, 2> MakePCone()
{
	std::array<std::array<uint64, 64>, 2> retval = PWay;
	for (int i = 0; i < 64; ++i)
	{
		for (int j = 0; j < 64; j++)
		{
			for (int me = 0; me < 2; ++me)
			{
				retval[me][i] = PWay[me][i];
				if (FileOf(i) > 0)
					retval[me][i] |= PWay[me][i - 1];
				if (FileOf(i) < 7)
					retval[me][i] |= PWay[me][i + 1];
			}
		}
	}
	return retval;
}
constexpr std::array<std::array<uint64, 64>, 2> MakePSupport()
{
	std::array<std::array<uint64, 64>, 2> retval;
	for (int i = 0; i < 64; ++i)
	{
		retval[0][i] = retval[1][i] = 0;
		for (int j = 0; j < 64; ++j)
		{
			if (i == j)
				continue;
			int fDiff = FileOf(i) - FileOf(j);
			if (fDiff != 1 && fDiff != -1)
				continue;
			if (RankOf(j) >= RankOf(i))
				retval[1][i] |= Bit(j);
			if (RankOf(j) <= RankOf(i))
				retval[0][i] |= Bit(j);
		}
	}
	return retval;
}
constexpr std::array<std::array<uint64, 64>, 2> BishopForward = MakeBishopForward(), PCone = MakePCone(), PSupport = MakePSupport();

//#define MOVING MoveScope_ debugMoveScope; UpdateDebug(debugLine);
//#define HI UpdateDebug(__LINE__);
//#define BYE UpdateDebug(__LINE__);
//#define MOVING UpdateDebug(__LINE__);
#define HI
#define BYE
#define MOVING

void init_misc(CommonData_* data)
{
	data->TurnKey = Rand64();
	for (int i = 0; i < 8; ++i) data->EPKey[i] = Rand64();
	for (int i = 0; i < 16; ++i) data->CastleKey[i] = Rand64();
	for (int i = 0; i < 16; ++i)
		for (int j = 0; j < 64; ++j)
			data->PieceKey[i][j] = i ? Rand64() : 0;
	for (int i = 0; i < 16; ++i)
		data->LogDist[i] = (int)(10.0 * log(1.01 + i));
}

constexpr std::array<int, 16> ListBits(uint64 u)
{
	std::array<int, 16> retval = { 0 };
	for (int j = 0; T(u); Cut_c(u), ++j)
		retval[j] = lsb_c(u);
	return retval;
}

constexpr uint64 XBMagicAttacks(const std::array<std::array<uint64, 64>, 64>& between, int i, uint64 occ)
{
	uint64 att = 0;
	for (uint64 u = BMask[i]; T(u); Cut_c(u))
		if (auto l = lsb_c(u); F(between[i][l] & occ))
			att |= between[i][l] | Bit(l);
	return att;
}

constexpr uint64 XRMagicAttacks(const std::array<std::array<uint64, 64>, 64>& between, int i, uint64 occ)
{
	uint64 att = 0;
	for (uint64 u = RMask[i]; T(u); Cut_c(u))
		if (auto l = lsb_c(u); F(between[i][l] & occ))
			att |= between[i][l] | Bit(l);
	return att;
}


Magic::Magic_ MakeBMagic()
{
	Magic::Magic_ retval;
	retval.attacks_.resize(B_MAGIC_SIZE);
	for (int i = 0; i < 64; ++i)
	{
		retval.masks_[i] = BMask[i] & Interior;
		array<int, 16> bit_list = ListBits(retval.masks_[i]);
		int bits = 64 - Magic::BShift[i];
		for (int j = 0; j < Bit(bits); ++j)
		{
			uint64 u = 0;
			for (int k = 0; k < bits; ++k)
				if (Odd(j >> k))
					u |= Bit(bit_list[k]);
			int index = static_cast<int>(Magic::BOffset[i] + ((Magic::BMagic[i] * u) >> Magic::BShift[i]));
			retval.attacks_[index] = XBMagicAttacks(Between, i, u);
		}
	}
	return retval;
}
Magic::Magic_ MakeRMagic()
{
	Magic::Magic_ retval;
	retval.attacks_.resize(R_MAGIC_SIZE);
	for (int i = 0; i < 64; ++i)
	{
		retval.masks_[i] = RMask[i];
		if (FileOf(i) > 0)
			retval.masks_[i] &= ~File[0];
		if (RankOf(i) > 0)
			retval.masks_[i] &= ~Line[0];
		if (FileOf(i) < 7)
			retval.masks_[i] &= ~File[7];
		if (RankOf(i) < 7)
			retval.masks_[i] &= ~Line[7];

		array<int, 16> bit_list = ListBits(retval.masks_[i]);
		int bits = 64 - Magic::RShift[i];
		for (int j = 0; j < Bit(bits); ++j)
		{
			uint64 u = 0;
			for (int k = 0; k < bits; ++k)
				if (Odd(j >> k))
					u |= Bit(bit_list[k]);
			int index = static_cast<int>(Magic::ROffset[i] + ((Magic::RMagic[i] * u) >> Magic::RShift[i]));
			retval.attacks_[index] = XRMagicAttacks(Between, i, u);
		}
	}
	return retval;
}
//constexpr Magic::Magic_<B_MAGIC_SIZE> BMagic = MakeBMagic();
//constexpr Magic::Magic_<R_MAGIC_SIZE> RMagic = MakeRMagic();


void gen_kpk(CommonData_* data)
{
	int turn, wp, wk, bk, to, cnt, old_cnt, un;
	uint64 bwp, bwk, bbk, u;
	typedef array<array<array<uint8, 64>, 64>, 64> kpkgen_e;
	vector<kpkgen_e> Kpk_gen(2);

	cnt = 0;
	old_cnt = 1;
start:
	if (cnt == old_cnt)
		goto end;
	old_cnt = cnt;
	cnt = 0;
	for (turn = 0; turn < 2; ++turn)
	{
		for (wp = 0; wp < 64; ++wp)
		{
			for (wk = 0; wk < 64; ++wk)
			{
				for (bk = 0; bk < 64; ++bk)
				{
					if (Kpk_gen[turn][wp][wk][bk])
						continue;
					++cnt;
					if (wp < 8 || wp >= 56)
						goto set_draw;
					if (wp == wk || wk == bk || bk == wp)
						goto set_draw;
					bwp = Bit(wp);
					bwk = Bit(wk);
					bbk = Bit(bk);
					if (PAtt[White][wp] & bbk)
					{
						if (turn == White)
							goto set_draw;
						else if (F(KAtt[wk] & bwp))
							goto set_draw;
					}
					un = 0;
					if (turn == Black)
					{
						u = KAtt[bk] & (~(KAtt[wk] | PAtt[White][wp]));
						if (F(u))
							goto set_draw;
						for (; T(u); Cut(u))
						{
							to = lsb(u);
							if (Kpk_gen[turn ^ 1][wp][wk][to] == 1)
								goto set_draw;
							else if (Kpk_gen[turn ^ 1][wp][wk][to] == 0)
								++un;
						}
						if (F(un))
							goto set_win;
					}
					else
					{
						for (u = KAtt[wk] & (~(KAtt[bk] | bwp)); T(u); Cut(u))
						{
							to = lsb(u);
							if (Kpk_gen[turn ^ 1][wp][to][bk] == 2)
								goto set_win;
							else if (Kpk_gen[turn ^ 1][wp][to][bk] == 0)
								++un;
						}
						to = wp + 8;
						if (to != wk && to != bk)
						{
							if (to >= 56)
							{
								if (F(KAtt[to] & bbk))
									goto set_win;
								if (KAtt[to] & bwk)
									goto set_win;
							}
							else
							{
								if (Kpk_gen[turn ^ 1][to][wk][bk] == 2)
									goto set_win;
								else if (Kpk_gen[turn ^ 1][to][wk][bk] == 0)
									++un;
								if (to < 24)
								{
									to += 8;
									if (to != wk && to != bk)
									{
										if (Kpk_gen[turn ^ 1][to][wk][bk] == 2)
											goto set_win;
										else if (Kpk_gen[turn ^ 1][to][wk][bk] == 0)
											++un;
									}
								}
							}
						}
						if (F(un))
							goto set_draw;
					}
					continue;
				set_draw:
					Kpk_gen[turn][wp][wk][bk] = 1;
					continue;
				set_win:
					Kpk_gen[turn][wp][wk][bk] = 2;
					continue;
				}
			}
		}
	}
	if (cnt)
		goto start;
end:
	for (turn = 0; turn < 2; ++turn)
	{
		for (wp = 0; wp < 64; ++wp)
		{
			for (wk = 0; wk < 64; ++wk)
			{
				data->Kpk[turn][wp][wk] = 0;
				for (bk = 0; bk < 64; ++bk)
				{
					if (Kpk_gen[turn][wp][wk][bk] == 2)
						data->Kpk[turn][wp][wk] |= Bit(bk);
				}
			}
		}
	}
}

void Regularize(int* op, int* md, int* eg)
{
	if (*op * *eg >= 0)
		return;
	const int adj = Min(abs(*op), Min(abs(*md), abs(*eg))) * (*op + *eg > 0 ? 1 : -1);
	*op += adj;
	*eg += adj;
	*md -= adj;
}

// helper to divide intermediate quantities to form scores
// note that straight integer division (a la Gull) creates an attractor at 0
// we support this, especially for weights inherited from Gull which have not been tuned for Roc
template<class T_> void init_mobility
	(const array<int, 12>& coeffs,
	 T_* mob)
{
	// ordering of coeffs is (linear*4, log*4, locus*4)
	auto m1 = [&](int phase, int pop)->sint16
	{
		double val = pop * (coeffs[phase] - coeffs[phase + 8]) + log(1.0 + pop) * coeffs[phase + 4];
		return static_cast<sint16>(val / 64.0);
	};
	auto m2 = [&](int pop)->packed_t
	{
		return Pack(m1(0, pop), m1(1, pop), m1(2, pop), m1(3, pop));
	};
	auto l1 = [&](int phase, int pop)->sint16
	{
		return static_cast<sint16>(pop * coeffs[phase + 8] / double(N_LOCUS));
	};
	auto l2 = [&](int pop)->packed_t
	{
		return Pack(l1(0, pop), l1(1, pop), l1(2, pop), l1(3, pop));
	};

	const auto p_max = (*mob)[0].size();
	for (int pop = 0; pop < p_max; ++pop)
	{
		(*mob)[0][pop] = m2(pop);
		(*mob)[1][pop] = l2(pop);
	}
}


uint64 within(int loc, int dist)
{
	uint64 retval = 0ull;
	for (int i = 0; i < 64; ++i)
		if (Dist(i, loc) <= dist)
			retval |= Bit(i);
	return retval;
}

void init_eval(CommonData_* data)
{
	init_mobility(MobCoeffsKnight, &data->MobKnight);
	init_mobility(MobCoeffsBishop, &data->MobBishop);
	init_mobility(MobCoeffsRook, &data->MobRook);
	init_mobility(MobCoeffsQueen, &data->MobQueen);
	for (int me = 0; me < 2; ++me)
	{
		data->LocusK[me] = MakeLoci(Locus::KDist, N_LOCUS);
		data->LocusQ[me] = MakeLoci(Locus::MinorDist_(me, QMask, 7.0, 4.0, 1.6, 0.0), N_LOCUS);
		data->LocusR[me] = MakeLoci(Locus::RDist_(3.0, 4.0), N_LOCUS);
		data->LocusB[me] = MakeLoci(Locus::MinorDist_(me, BMask, 9.0, 5.0, 1.6, 0.0), N_LOCUS);
		data->LocusN[me] = MakeLoci(Locus::MinorDist_(me, NAtt, 2.0, 1.0, 1.6, 0.0), N_LOCUS);
	}

	for (int i = 0; i < 3; ++i)
		for (int j = 7; j >= 0; --j)
		{
			data->Shelter[i][j] = 0;
			for (int k = 1; k < Min(j, 5); ++k)
				data->Shelter[i][j] += Av(ShelterValue, 5, i, k - 1);
			if (!j)  // no pawn in file
				data->Shelter[i][j] = data->Shelter[i][7] + Av(ShelterValue, 5, i, 4);
		}

	for (int i = 0; i < 8; ++i)
	{
		int im2 = Max(i - 2, 0);
		auto attdef = [&](int k) { return PasserAttDefQuad[k] * im2*im2 + PasserAttDefLinear[k] * im2 + PasserAttDefConst[k]; };
		data->PasserAtt[i] = attdef(0);
		data->PasserDef[i] = attdef(2);
		data->PasserAttLog[i] = attdef(1);
		data->PasserDefLog[i] = attdef(3);
	}
}

// all these special-purpose endgame evaluators

template<bool me> uint16 krbkrx(const State_& state)
{
	if (state().King(opp) & Interior)
		return 1;
	return 16;
}

template<bool me> uint16 kpkx(const State_& state)
{
	uint64 u = me == White ? RO->Kpk[state[0].turn][lsb(state().Pawn(White))][lsb(state().King(White))] & Bit(lsb(state().King(Black)))
		: RO->Kpk[state[0].turn ^ 1][63 - lsb(state().Pawn(Black))][63 - lsb(state().King(Black))] & Bit(63 - lsb(state().King(White)));
	return T(u) ? 32 : T(state().Piece(opp) ^ state().King(opp));
}

template<bool me> uint16 knpkx(const State_& state)
{
	if (state().Pawn(me) & OwnLine<me>(6) & (File[0] | File[7]))
	{
		int sq = lsb(state().Pawn(me));
		if (KAtt[sq] & state().King(opp) & (OwnLine<me>(6) | OwnLine<me>(7)))
			return 0;
		if (state().PieceAt(sq + Push[me]) == IKing[me] && (KAtt[lsb(state().King(me))] & KAtt[lsb(state().King(opp))] & OwnLine<me>(7)))
			return 0;
	}
	else if (state().Pawn(me) & OwnLine<me>(5) & (File[0] | File[7]))
	{
		int sq = lsb(state().Pawn(me)), to = sq + Push[me];
		if (state().PieceAt(sq + Push[me]) == IPawn[opp])
		{
			if (KAtt[to] & state().King(opp) & OwnLine<me>(7))
				return 0;
			if ((KAtt[to] & KAtt[lsb(state().King(opp))] & OwnLine<me>(7)) && (!(NAtt[to] & state().Knight(me)) || state[0].turn == opp))
				return 0;
		}
	}
	return 32;
}

template<bool me> uint16 krpkrx(const State_& state)
{
	int mul = 32;
	int sq = lsb(state().Pawn(me));
	int rrank = OwnRank<me>(sq);
	int o_king = lsb(state().King(opp));
	int o_rook = lsb(state().Rook(opp));
	int m_king = lsb(state().King(me));
	int add_mat = T(state().Piece(opp) ^ state().King(opp) ^ state().Rook(opp));
	int clear = F(add_mat) || F((PWay[opp][sq] | PIsolated[FileOf(sq)]) & Forward[opp][RankOf(sq + Push[me])] & (state().Piece(opp) ^ state().King(opp) ^ state().Rook(opp)));

	if (!clear)
		return 32;
	if (!add_mat && !(state().Pawn(me) & (File[0] | File[7])))
	{
		int m_rook = lsb(state().Rook(me));
		if (OwnRank<me>(o_king) < OwnRank<me>(m_rook) && OwnRank<me>(m_rook) < rrank && OwnRank<me>(m_king) >= rrank - 1 &&
			OwnRank<me>(m_king) > OwnRank<me>(m_rook) &&
			((KAtt[m_king] & state().Pawn(me)) || (MY_TURN(state) && abs(FileOf(sq) - FileOf(m_king)) <= 1 && abs(rrank - OwnRank<me>(m_king)) <= 2)))
			return 127;
		if (KAtt[m_king] & state().Pawn(me))
		{
			if (rrank >= 4)
			{
				if ((FileOf(sq) < FileOf(m_rook) && FileOf(m_rook) < FileOf(o_king)) || (FileOf(sq) > FileOf(m_rook) && FileOf(m_rook) > FileOf(o_king)))
					return 127;
			}
			else if (rrank >= 2)
			{
				if (!(state().Pawn(me) & (File[1] | File[6])) && rrank + abs(FileOf(sq) - FileOf(m_rook)) > 4 &&
					((FileOf(sq) < FileOf(m_rook) && FileOf(m_rook) < FileOf(o_king)) || (FileOf(sq) > FileOf(m_rook) && FileOf(m_rook) > FileOf(o_king))))
					return 127;
			}
		}
	}

	if (PWay[me][sq] & state().King(opp))
	{
		if (state().Pawn(me) & (File[0] | File[7]))
			mul = Min(mul, add_mat << 3);
		if (rrank <= 3)
			mul = Min(mul, add_mat << 3);
		if (rrank == 4 && OwnRank<me>(m_king) <= 4 && OwnRank<me>(o_rook) == 5 && T(state().King(opp) & (OwnLine<me>(6) | OwnLine<me>(7))) &&
			(!MY_TURN(state) || F(PAtt[me][sq] & RookAttacks(lsb(state().Rook(me)), state().PieceAll()) & (~KAtt[o_king]))))
			mul = Min(mul, add_mat << 3);
		if (rrank >= 5 && OwnRank<me>(o_rook) <= 1 && (!MY_TURN(state) || IsCheck(state, me) || Dist(m_king, sq) >= 2))
			mul = Min(mul, add_mat << 3);
		if (T(state().King(opp) & (File[1] | File[2] | File[6] | File[7])) && T(state().Rook(opp) & OwnLine<me>(7)) && T(Between[o_king][o_rook] & (File[3] | File[4])) &&
			F(state().Rook(me) & OwnLine<me>(7)))
			mul = Min(mul, add_mat << 3);
		return mul;
	}
	else if (rrank == 6 && (state().Pawn(me) & (File[0] | File[7])) && ((PSupport[me][sq] | PWay[opp][sq]) & state().Rook(opp)) && OwnRank<me>(o_king) >= 6)
	{
		int dist = abs(FileOf(sq) - FileOf(o_king));
		if (dist <= 3)
			mul = Min(mul, add_mat << 3);
		if (dist == 4 && ((PSupport[me][o_king] & state().Rook(me)) || state[0].turn == opp))
			mul = Min(mul, add_mat << 3);
	}

	if (KAtt[o_king] & PWay[me][sq] & OwnLine<me>(7))
	{
		if (rrank <= 4 && OwnRank<me>(m_king) <= 4 && OwnRank<me>(o_rook) == 5)
			mul = Min(mul, add_mat << 3);
		if (rrank == 5 && OwnRank<me>(o_rook) <= 1 && !MY_TURN(state) || (F(KAtt[m_king] & PAtt[me][sq] & (~KAtt[o_king])) && (IsCheck(state, me) || Dist(m_king, sq) >= 2)))
			mul = Min(mul, add_mat << 3);
	}

	if (T(PWay[me][sq] & state().Rook(me)) && T(PWay[opp][sq] & state().Rook(opp)))
	{
		if (state().King(opp) & (File[0] | File[1] | File[6] | File[7]) & OwnLine<me>(6))
			mul = Min(mul, add_mat << 3);
		else if ((state().Pawn(me) & (File[0] | File[7])) && (state().King(opp) & (OwnLine<me>(5) | OwnLine<me>(6))) && abs(FileOf(sq) - FileOf(o_king)) <= 2 &&
			FileOf(sq) != FileOf(o_king))
			mul = Min(mul, add_mat << 3);
	}

	if (abs(FileOf(sq) - FileOf(o_king)) <= 1 && abs(FileOf(sq) - FileOf(o_rook)) <= 1 && OwnRank<me>(o_rook) > rrank && OwnRank<me>(o_king) > rrank)
		mul = Min(mul, (state().Pawn(me) & (File[3] | File[4])) ? 12 : 16);

	return mul;
}

template<bool me> uint16 krpkbx(const State_& state)
{
	if (!(state().Pawn(me) & OwnLine<me>(5)))
		return 32;
	int sq = lsb(state().Pawn(me));
	if (!(PWay[me][sq] & state().King(opp)))
		return 32;
	int diag_sq = NB<me>(BMask[sq + Push[me]]);
	if (OwnRank<me>(diag_sq) > 1)
		return 32;
	uint64 mdiag = FullLine[sq + Push[me]][diag_sq] | Bit(sq + Push[me]) | Bit(diag_sq);
	int check_sq = NB<me>(BMask[sq - Push[me]]);
	uint64 cdiag = FullLine[sq - Push[me]][check_sq] | Bit(sq - Push[me]) | Bit(check_sq);
	if ((mdiag | cdiag) & (state().Piece(opp) ^ state().King(opp) ^ state().Bishop(opp)))
		return 32;
	if (cdiag & state().Bishop(opp))
		return 0;
	if ((mdiag & state().Bishop(opp)) && (state[0].turn == opp || !(state().King(me) & PAtt[opp][sq + Push[me]])))
		return 0;
	return 32;
}

template<bool me> uint16 kqkp(const State_& state)
{
	if (F(KAtt[lsb(state().King(opp))] & state().Pawn(opp) & OwnLine<me>(1) & (File[0] | File[2] | File[5] | File[7])))
		return 32;
	if (PWay[opp][lsb(state().Pawn(opp))] & (state().King(me) | state().Queen(me)))
		return 32;
	if (state().Pawn(opp) & Boundary)
		return 1;
	else
		return 4;
}

template<bool me> uint16 kqkrpx(const State_& state)
{
	int rsq = lsb(state().Rook(opp));
	uint64 pawns = KAtt[lsb(state().King(opp))] & PAtt[me][rsq] & state().Pawn(opp) & Interior & OwnLine<me>(6);
	if (pawns && OwnRank<me>(lsb(state().King(me))) <= 4)
		return 0;
	return 32;
}

template<bool me> uint16 krkpx(const State_& state)
{
	if (T(KAtt[lsb(state().King(opp))] & state().Pawn(opp) & OwnLine<me>(1)) & F(PWay[opp][NB<me>(state().Pawn(opp))] & state().King(me)))
		return 0;
	return 32;
}

template<bool me> uint16 krppkrpx(const State_& state)
{
	if (auto passer = state[0].passer & state().Pawn(me))
	{
		if (Single(passer))
		{
			int sq = lsb(passer);
			if (PWay[me][sq] & state().King(opp) & (File[0] | File[1] | File[6] | File[7]))
			{
				int opp_king = lsb(state().King(opp));
				if (KAtt[opp_king] & state().Pawn(opp))
				{
					int king_file = FileOf(opp_king);
					if (!((~(File[king_file] | PIsolated[king_file])) & state().Pawn(me)))
						return 1;
				}
			}
		}
		return 32;
	}
	if (F((~(PWay[opp][lsb(state().King(opp))] | PSupport[me][lsb(state().King(opp))])) & state().Pawn(me)))
		return 0;
	return 32;
}

template<bool me> uint16 krpppkrppx(const State_& state)
{
	if (T(state[0].passer & state().Pawn(me)) || F((KAtt[lsb(state().Pawn(opp))] | KAtt[msb(state().Pawn(opp))]) & state().Pawn(opp)))
		return 32;
	if (int kOpp = lsb(state().King(opp)); F((~(PWay[opp][kOpp] | PSupport[me][kOpp])) & state().Pawn(me)))
		return 0;
	return 32;
}

template<bool me> uint16 kbpkbx(const State_& state)
{
	int sq = lsb(state().Pawn(me));
	uint64 u;
	if (T(state().Piece(ILight[me])) != T(state().Piece(ILight[opp])))
	{
		if (OwnRank<me>(sq) <= 4)
			return 0;
		if (T(PWay[me][sq] & state().King(opp)) && OwnRank<me>(sq) <= 5)
			return 0;
		for (u = state().Bishop(opp); T(u); Cut(u))
		{
			if (OwnRank<me>(lsb(u)) <= 4 && T(BishopAttacks(lsb(u), state().PieceAll()) & PWay[me][sq]))
				return 0;
			if (state[0].turn == opp && T(BishopAttacks(lsb(u), state().PieceAll()) & state().Pawn(me)))
				return 0;
		}
	}
	else if (T(PWay[me][sq] & state().King(opp)) && T(state().King(opp) & LightArea) != T(state().Bishop(me) & LightArea))
		return 0;
	return 32;
}

template<bool me> uint16 kbpknx(const State_& state)
{
	uint64 u;
	if (T(PWay[me][lsb(state().Pawn(me))] & state().King(opp)) && T(state().King(opp) & LightArea) != T(state().Bishop(me) & LightArea))
		return 0;
	if (state[0].turn == opp)
		for (u = state().Knight(opp); T(u); Cut(u))
			if (NAtt[lsb(u)] & state().Pawn(me))
				return 0;
	return 32;
}

template<bool me> uint16 kbppkbx(const State_& state)
{
	int sq1 = NB<me>(state().Pawn(me));
	int sq2 = NB<opp>(state().Pawn(me));
	int o_king = lsb(state().King(opp));
	int o_bishop = lsb(state().Bishop(opp));

	if (FileOf(sq1) == FileOf(sq2))
	{
		if (OwnRank<me>(sq2) <= 3)
			return 0;
		if (T(PWay[me][sq2] & state().King(opp)) && OwnRank<me>(sq2) <= 5)
			return 0;
	}
	else if (PIsolated[FileOf(sq1)] & state().Pawn(me))
	{
		if (T(state().King(opp) & LightArea) != T(state().Bishop(me) & LightArea))
		{
			if (HasBit(KAtt[o_king] | state().King(opp), sq2 + Push[me]) && HasBit(BishopAttacks(o_bishop, state().PieceAll()), sq2 + Push[me]) &&
				HasBit(KAtt[o_king] | state().King(opp), (sq2 & 0xF8) | FileOf(sq1)) && HasBit(BishopAttacks(o_bishop, state().PieceAll()), (sq2 & 0xFFFFFFF8) | FileOf(sq1)))
				return 0;
		}
	}
	return 32;
}

template<bool me> uint16 krppkrx(const State_& state)
{
	int sq1 = NB<me>(state().Pawn(me));	// trailing pawn
	int sq2 = NB<opp>(state().Pawn(me));	// leading pawn

	if ((state().Piece(opp) ^ state().King(opp) ^ state().Rook(opp)) & Forward[me][RankOf(sq1 - Push[me])])
		return 32;
	if (FileOf(sq1) == FileOf(sq2))
	{
		if (T(PWay[me][sq2] & state().King(opp)))
			return 16;
	}
	else if (T(PIsolated[FileOf(sq2)] & state().Pawn(me)) && T((File[0] | File[7]) & state().Pawn(me)) && T(state().King(opp) & Shift<me>(state().Pawn(me))))
	{
		if (OwnRank<me>(sq2) == 5 && OwnRank<me>(sq1) == 4 && T(state().Rook(opp) & (OwnLine<me>(5) | OwnLine<me>(6))))
			return 10;
		else if (OwnRank<me>(sq2) < 5)
			return 16;
	}
	int r2 = lsb(state().Rook(opp)), rf = FileOf(r2);
	const uint64 mask = West[rf] & state().King(me) ? West[rf] : East[rf];
	if (mask & (state().Rook(me) | state().Pawn(me)))
		return 32;
	return 16;
}


template<bool me> bool eval_stalemate(GEvalInfo& EI, const State_& state)
{
	bool retval = F(state().NonPawnKing(opp)) 
			&& state[0].turn == opp 
			&& F(state[0].att[me] & state().King(opp))
			&& F(KAtt[EI.king[opp]] & (~(state[0].att[me] | state().Piece(opp)))) 
			&& F(state[0].patt[opp] & state().Piece(me)) 
			&& F(Shift<opp>(state().Pawn(opp)) & (~EI.occ));
	if (retval)
		EI.mul = 0;
	return retval;
}

template<bool me> void eval_pawns_only(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	using WATCH = NoWatch_;	// tuner can't see KpkValue, o well
	int number = pop(state().Pawn(me));
	int kOpp = lsb(state().King(opp));
	int sq = FileOf(kOpp) <= 3 ? (me ? 0 : 56) : (me ? 7 : 63);

	if (F(state().Pawn(me) & (~PWay[opp][sq])))
	{
		if ((KAtt[sq] | Bit(sq)) & state().King(opp))
			EI.mul = 0;
		else if ((KAtt[sq] & KAtt[kOpp] & OwnLine<me>(7)) && state().PieceAt(sq - Push[me]) == IPawn[opp] && state().PieceAt(sq - 2 * Push[me]) == IPawn[me])
			EI.mul = 0;
	}
	else if ((state().King(opp) & OwnLine<me>(6) | OwnLine<me>(7)) && abs(FileOf(sq) - FileOf(kOpp)) <= 3 && !(state().Pawn(me) & (~PSupport[me][sq])) &&
		(state().Pawn(me) & OwnLine<me>(5) & Shift<opp>(state().Pawn(opp))))
		EI.mul = 0;
	if (number == 1)
	{
		EI.mul = min(EI.mul, kpkx<me>(state));
		if (state().Piece(opp) == state().King(opp) && EI.mul == 32)
			IncV(state[0].score, KpkValue);
	}
}

template<bool me> void eval_single_bishop(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	int number = pop(state().Pawn(me));
	int kOpp = lsb(state().King(opp));
	int sq = state().Piece(ILight[me]) ? (me ? 0 : 63) : (me ? 7 : 56);
	if (F(state().Pawn(me) & (~PWay[opp][sq])))
	{
		if ((KAtt[sq] | Bit(sq)) & state().King(opp))
			EI.mul = 0;
		else if ((KAtt[sq] & KAtt[kOpp] & OwnLine<me>(7)) && state().PieceAt(sq - Push[me]) == IPawn[opp] && state().PieceAt(sq - 2 * Push[me]) == IPawn[me])
			EI.mul = 0;
	}
	else if ((state().King(opp) & OwnLine<me>(6) | OwnLine<me>(7)) 
			&& abs(FileOf(sq) - FileOf(kOpp)) <= 3 
			&& !(state().Pawn(me) & (~PSupport[me][sq])) 
			&& (state().Pawn(me) & OwnLine<me>(5) & Shift<opp>(state().Pawn(opp))))
		EI.mul = 0;

	if (number == 1)
	{
		sq = lsb(state().Pawn(me));
		if ((state().Pawn(me) & (File[1] | File[6]) & OwnLine<me>(5)) 
				&& state().PieceAt(sq + Push[me]) == IPawn[opp] 
				&& ((PAtt[me][sq + Push[me]] | PWay[me][sq + Push[me]]) & state().King(opp)))
			EI.mul = 0;
	}
	if (state().Bishop(opp) && Single(state().Bishop(opp)) && T(state().Piece(ILight[me])) != T(state().Piece(ILight[opp])))
	{
		int pcnt = 0;
		if (T(state().King(opp) & LightArea) == T(state().Bishop(opp) & LightArea))
		{
			uint64 u;
			for (u = state().Pawn(me); u; Cut(u))
			{
				if (pcnt >= 2)
					break;
				++pcnt;
				int sq = lsb(u);
				if (!(PWay[me][sq] & (PAtt[me][EI.king[opp]] | PAtt[opp][EI.king[opp]])))
				{
					if (!(PWay[me][sq] & state().Pawn(opp)))
						break;
					int bsq = lsb(state().Bishop(opp));
					uint64 att = BishopAttacks(bsq, EI.occ);
					if (!(att & PWay[me][sq] & state().Pawn(opp)))
						break;
					if (!(BishopForward[me][bsq] & att & PWay[me][sq] & state().Pawn(opp)) && pop(FullLine[lsb(att & PWay[me][sq] & state().Pawn(opp))][bsq] & att) <= 2)
						break;
				}
			}
			if (!u)
			{
				EI.mul = 0;
				return;
			}
		}

		// check for partial block
		if (pcnt <= 2 && Multiple(state().Pawn(me)) && !state().Pawn(opp) && !(state().Pawn(me) & Boundary) && EI.mul)
		{
			int sq1 = lsb(state().Pawn(me)), sq2 = msb(state().Pawn(me));
			int fd = abs(FileOf(sq2) - FileOf(sq1));
			if (fd >= 5)
				EI.mul = 32;
			else if (fd >= 4)
				EI.mul = 26;
			else if (fd >= 3)
				EI.mul = 20;
		}
		if ((KAtt[EI.king[opp]] | state[0].patt[opp]) & state().Bishop(opp))
		{
			uint64 push = Shift<me>(state().Pawn(me));
			if (!(push & (~(state().Piece(opp) | state[0].att[opp]))) && (state().King(opp) & (state().Piece(ILight[opp]) ? LightArea : DarkArea)))
			{
				EI.mul = Min<uint16>(EI.mul, 8);
				int bsq = lsb(state().Bishop(opp));
				uint64 att = BishopAttacks(bsq, EI.occ);
				uint64 prp = (att | KAtt[EI.king[opp]]) & state().Pawn(opp) & (state().Piece(ILight[opp]) ? LightArea : DarkArea);
				uint64 patt = ShiftW<opp>(prp) | ShiftE<opp>(prp);
				if ((KAtt[EI.king[opp]] | patt) & state().Bishop(opp))
				{
					uint64 double_att = (KAtt[EI.king[opp]] & patt) | (patt & att) | (KAtt[EI.king[opp]] & att);
					if (!(push & (~(state().King(opp) | state().Bishop(opp) | prp | double_att))))
					{
						EI.mul = 0;
						return;
					}
				}
			}
		}
	}
	if (number == 1)
	{
		if (state().Bishop(opp))
			EI.mul = Min(EI.mul, kbpkbx<me>(state));
		else if (state().Knight(opp))
			EI.mul = Min(EI.mul, kbpknx<me>(state));
	}
	else if (number == 2 && T(state().Bishop(opp)))
		EI.mul = Min(EI.mul, kbppkbx<me>(state));
}

template<bool me> void eval_np(GEvalInfo& EI, const State_& state, pop_func_t)
{
	assert(state().Knight(me) && Single(state().Knight(me)) && state().Pawn(me) && Single(state().Pawn(me)));
	EI.mul = Min(EI.mul, knpkx<me>(state));
}
template<bool me> void eval_knppkbx(GEvalInfo& EI, const State_& state, pop_func_t)
{
	assert(state().Knight(me) && Single(state().Knight(me)) && Multiple(state().Pawn(me)) && state().Bishop(opp) && Single(state().Bishop(opp)));
	static const uint64 AB = File[0] | File[1], ABC = AB | File[2];
	static const uint64 GH = File[6] | File[7], FGH = GH | File[5];
	if (F(state().Pawn(me) & ~AB) && T(state().King(opp) & ABC))
	{
		uint64 back = Forward[opp][RankOf(lsb(state().King(opp)))];
		if (T(back & state().Pawn(me)))
			EI.mul = Min<uint16>(EI.mul, T(state().King(me) & AB & ~back) ? 24 : 8);
	}
	if (F(state().Pawn(me) & ~GH) && T(state().King(opp) & FGH))
	{
		uint64 back = Forward[opp][RankOf(lsb(state().King(opp)))];
		if (T(back & state().Pawn(me)))
			EI.mul = Min<uint16>(EI.mul, T(state().King(me) & GH & ~back) ? 24 : 8);
	}
}

template<bool me> inline void check_forced_stalemate(uint16* mul, const State_& state, int kloc)
{
	if (F(KAtt[kloc] & ~state[0].att[me])
		&& F(Shift<opp>(state().Pawn(opp)) & ~state().PieceAll()))
		*mul -= (3 * *mul) / 4;
}
template<bool me> INLINE void check_forced_stalemate(uint16* mul, const State_& state)
{
	check_forced_stalemate<me>(mul, state, lsb(state().King(opp)));
}

template<bool me> void eval_krbkrx(GEvalInfo& EI, const State_& state, pop_func_t)
{
	assert(state().Rook(me) && Single(state().Rook(me)) && state().Bishop(me) && Single(state().Bishop(me)) && state().Rook(opp) && Single(state().Rook(opp)));
	EI.mul = Min(EI.mul, krbkrx<me>(state));
	check_forced_stalemate<me>(&EI.mul, state);
}
template<bool me> void eval_krkpx(GEvalInfo& EI, const State_& state, pop_func_t)
{
	assert(state().Rook(me) && Single(state().Rook(me)) && F(state().Pawn(me)) && state().Pawn(opp));
	EI.mul = Min(EI.mul, krkpx<me>(state));
}
template<bool me> void eval_krpkrx(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	assert(state().Rook(me) && Single(state().Rook(me)) && state().Pawn(me) && Single(state().Pawn(me)) && state().Rook(opp) && Single(state().Rook(opp)));
	uint16 new_mul = krpkrx<me>(state);
	EI.mul = (new_mul <= 32 ? Min(EI.mul, new_mul) : new_mul);
	check_forced_stalemate<me>(&EI.mul, state);
}
template<bool me> void eval_krpkbx(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	assert(state().Rook(me) && Single(state().Rook(me)) && state().Pawn(me) && Single(state().Pawn(me)) && state().Bishop(opp));
	EI.mul = Min(EI.mul, krpkbx<me>(state));
}
template<bool me> void eval_krppkrx(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	EI.mul = Min(EI.mul, krppkrx<me>(state));
	check_forced_stalemate<me>(&EI.mul, state);
}
template<bool me> void eval_krppkrpx(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	eval_krppkrx<me>(EI, state, pop);
	EI.mul = Min(EI.mul, krppkrpx<me>(state));
	check_forced_stalemate<me>(&EI.mul, state);
}
template<bool me> void eval_krpppkrppx(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	EI.mul = Min(EI.mul, krpppkrppx<me>(state));
	check_forced_stalemate<me>(&EI.mul, state);
}

template<bool me> void eval_kqkpx(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	EI.mul = Min(EI.mul, kqkp<me>(state));
	check_forced_stalemate<me>(&EI.mul, state);
}
template<bool me> void eval_kqkrpx(GEvalInfo& EI, const State_& state, pop_func_t pop)
{
	EI.mul = Min(EI.mul, kqkrpx<me>(state));
	check_forced_stalemate<me>(&EI.mul, state);
}


void calc_material(int index, GMaterial& material)
{
	using WATCH = NoWatch_;

	array<int, 2> pawns, knights, light, dark, rooks, queens, bishops, major, minor, tot, count, mat, mul, closed;
	int i = index;
	queens[White] = i % 3;
	i /= 3;
	queens[Black] = i % 3;
	i /= 3;
	rooks[White] = i % 3;
	i /= 3;
	rooks[Black] = i % 3;
	i /= 3;
	light[White] = i % 2;
	i /= 2;
	light[Black] = i % 2;
	i /= 2;
	dark[White] = i % 2;
	i /= 2;
	dark[Black] = i % 2;
	i /= 2;
	knights[White] = i % 3;
	i /= 3;
	knights[Black] = i % 3;
	i /= 3;
	pawns[White] = i % 9;
	i /= 9;
	pawns[Black] = i % 9;
	for (int me = 0; me < 2; ++me)
	{
		bishops[me] = light[me] + dark[me];
		major[me] = rooks[me] + queens[me];
		minor[me] = bishops[me] + knights[me];
		tot[me] = 3 * minor[me] + 5 * rooks[me] + 9 * queens[me];
		count[me] = major[me] + minor[me] + pawns[me];
		mat[me] = mul[me] = 32;
	}
	int score = (SeeValue[WhitePawn] + Av(MatLinear, 0, 0, 0)) * (pawns[White] - pawns[Black])
		+ (SeeValue[WhiteKnight] + Av(MatLinear, 0, 0, 1)) * (knights[White] - knights[Black])
		+ (SeeValue[WhiteLight] + Av(MatLinear, 0, 0, 2)) * (bishops[White] - bishops[Black])
		+ (SeeValue[WhiteRook] + Av(MatLinear, 0, 0, 3)) * (rooks[White] - rooks[Black])
		+ (SeeValue[WhiteQueen] + Av(MatLinear, 0, 0, 4)) * (queens[White] - queens[Black])
		+ (50 * CP_EVAL + Av(MatLinear, 0, 0, 5)) * ((bishops[White] / 2) - (bishops[Black] / 2));
	for (int me = 0; me < 2; ++me)
	{
		if (pawns[me] > pawns[opp] && queens[me] >= queens[opp] &&
			((major[me] > major[opp] && major[me] + minor[me] >= major[opp] + minor[opp]) || (major[me] == major[opp] && minor[me] > minor[opp])))
			score += (me ? -1 : 1) * MatWinnable;
	}

	int phase = Phase[PieceType[WhitePawn]] * (pawns[White] + pawns[Black])
		+ Phase[PieceType[WhiteKnight]] * (knights[White] + knights[Black])
		+ Phase[PieceType[WhiteLight]] * (bishops[White] + bishops[Black])
		+ Phase[PieceType[WhiteRook]] * (rooks[White] + rooks[Black])
		+ Phase[PieceType[WhiteQueen]] * (queens[White] + queens[Black]);
	material.phase = Min((Max(phase - PhaseMin, 0) * MAX_PHASE) / (PhaseMax - PhaseMin), MAX_PHASE);

	packed_t special = 0;
	for (int me = 0; me < 2; ++me)
	{
		if (queens[me] == queens[opp])
		{
			if (rooks[me] - rooks[opp] == 1)
			{
				if (knights[me] == knights[opp] && bishops[opp] - bishops[me] == 1)
					IncV(special, Values::MatRB);
				else if (bishops[me] == bishops[opp] && knights[opp] - knights[me] == 1)
					IncV(special, Values::MatRN);
				else if (knights[me] == knights[opp] && bishops[opp] - bishops[me] == 2)
					DecV(special, Values::MatBBR);
				else if (bishops[me] == bishops[opp] && knights[opp] - knights[me] == 2)
					DecV(special, Values::MatNNR);
				else if (bishops[opp] - bishops[me] == 1 && knights[opp] - knights[me] == 1)
					DecV(special, Values::MatBNR);
			}
			else if (rooks[me] == rooks[opp])
			{
				if (minor[me] - minor[opp] == 1)
					IncV(special, Values::MatM);
				else if (minor[me] == minor[opp] && pawns[me] > pawns[opp])
					IncV(special, Values::MatPawnOnly);
			}
		}
		else if (queens[me] - queens[opp] == 1)
		{
			if (rooks[opp] - rooks[me] == 2 && minor[opp] - minor[me] == 0)
				IncV(special, Values::MatQRR);
			else if (rooks[opp] - rooks[me] == 1 && knights[opp] == knights[me] && bishops[opp] - bishops[me] == 1)
				IncV(special, Values::MatQRB);
			else if (rooks[opp] - rooks[me] == 1 && knights[opp] - knights[me] == 1 && bishops[opp] == bishops[me])
				IncV(special, Values::MatQRN);
			else if ((major[opp] + minor[opp]) - (major[me] + minor[me]) >= 2)
				IncV(special, Values::MatQ3);
		}
	}
	score += (Opening(special) * material.phase + Endgame(special) * (MAX_PHASE - (int)material.phase)) / MAX_PHASE;

	array<int, 2> quad = { 0, 0 };
	auto mqm = [&](int i, int j) { return TrAv(MatQuadMe, 6, i, j); };
	auto mqo = [&](int i, int j) { return TrAv(MatQuadOpp, 5, i, j); };
	for (int me = 0; me < 2; me++)
	{
		quad[me] += T(pawns[me]) * (pawns[me] * mqm(0, 0) + knights[me] * mqm(0, 1) + bishops[me] * mqm(0, 2) + rooks[me] * mqm(0, 3) + queens[me] * mqm(0, 4));
		quad[me] += pawns[me] * (pawns[me] * mqm(1, 0) + knights[me] * mqm(1, 1) + bishops[me] * mqm(1, 2) + rooks[me] * mqm(1, 3) + queens[me] * mqm(1, 4));
		quad[me] += knights[me] * (knights[me] * mqm(2, 0) + bishops[me] * mqm(2, 1) + rooks[me] * mqm(2, 2) + queens[me] * mqm(2, 3));
		quad[me] += bishops[me] * (bishops[me] * mqm(3, 0) + rooks[me] * mqm(3, 1) + queens[me] * mqm(3, 2));
		quad[me] += rooks[me] * (rooks[me] * mqm(4, 0) + queens[me] * mqm(4, 1));

		quad[me] += T(pawns[me]) * (knights[opp] * mqo(0, 0) + bishops[opp] * mqo(0, 1) + rooks[opp] * mqo(0, 2) + queens[opp] * mqo(0, 3));
		quad[me] += pawns[me] * (knights[opp] * mqo(1, 0) + bishops[opp] * mqo(1, 1) + rooks[opp] * mqo(1, 2) + queens[opp] * mqo(1, 3));
		quad[me] += knights[me] * (bishops[opp] * mqo(2, 0) + rooks[opp] * mqo(2, 1) + queens[opp] * mqo(2, 2));
		quad[me] += bishops[me] * (rooks[opp] * mqo(3, 0) + queens[opp] * mqo(3, 1));
		quad[me] += rooks[me] * queens[opp] * mqo(4, 0);

		if (light[me] * dark[me])
			quad[me] += pawns[me] * Av(BishopPairQuad, 0, 0, 0)
			+ knights[me] * Av(BishopPairQuad, 0, 0, 1)
			+ rooks[me] * Av(BishopPairQuad, 0, 0, 2)
			+ queens[me] * Av(BishopPairQuad, 0, 0, 3)
			+ pawns[opp] * Av(BishopPairQuad, 0, 0, 4)
			+ knights[opp] * Av(BishopPairQuad, 0, 0, 5)
			+ bishops[opp] * Av(BishopPairQuad, 0, 0, 6)
			+ rooks[opp] * Av(BishopPairQuad, 0, 0, 7)
			+ queens[opp] * Av(BishopPairQuad, 0, 0, 8);

		closed[me] = pawns[me] * Av(MatClosed, 0, 0, 0)
			+ knights[me] * Av(MatClosed, 0, 0, 1)
			+ bishops[me] * Av(MatClosed, 0, 0, 2)
			+ rooks[me] * Av(MatClosed, 0, 0, 3)
			+ queens[me] * Av(MatClosed, 0, 0, 4)
			+ light[me] * dark[me] * Av(MatClosed, 0, 0, 5);
	}
	score += ((quad[White] - quad[Black]) * CP_EVAL) / 100;

	for (int me = 0; me < 2; ++me)
	{
		if (tot[me] - tot[opp] <= 3)
		{
			if (!pawns[me])
			{
				if (tot[me] <= 3)
					mul[me] = 0;
				if (tot[me] == tot[opp] && major[me] == major[opp] && minor[me] == minor[opp])
					mul[me] = major[me] + minor[me] <= 2 ? 0 : (major[me] + minor[me] <= 3 ? 16 : 32);
				else if (minor[me] + major[me] <= 2)
				{
					if (bishops[me] < 2)
						mat[me] = (bishops[me] && rooks[me]) ? 8 : 1;
					else if (bishops[opp] + rooks[opp] >= 1)
						mat[me] = 1;
					else
						mat[me] = 32;
				}
				else if (tot[me] - tot[opp] < 3 && minor[me] + major[me] - minor[opp] - major[opp] <= 1)
					mat[me] = 4;
				else if (minor[me] + major[me] <= 3)
					mat[me] = 8 * (1 + bishops[me]);
				else
					mat[me] = 8 * (2 + bishops[me]);
			}
			if (pawns[me] <= 1)
			{
				mul[me] = Min(28, mul[me]);
				if (rooks[me] == 1 && queens[me] + minor[me] == 0 && rooks[opp] == 1)
					mat[me] = Min(23, mat[me]);
			}
		}
		if (!major[me])
		{
			if (!minor[me])
			{
				if (!tot[me] && pawns[me] < pawns[opp])
					DecV(score, (pawns[opp] - pawns[me]) * SeeValue[WhitePawn]);
			}
			else if (minor[me] == 1)
			{
				if (pawns[me] <= 1 && minor[opp] >= 1)
					mat[me] = 1;
				if (bishops[me] == 1)
				{
					if (minor[opp] == 1)
					{
						if (knights[opp] == 1)
							mul[me] += 8;
						else if (light[me] != light[opp])
						{
							mul[me] = Min(mul[me], 15);
							if (pawns[me] - pawns[opp] <= 1)
								mul[me] = Min(mul[me], 11);
						}
					}
				}
				else
				{	// I have only knight
					if (knights[opp] == 0 && bishops[opp] == 1)
						mul[me] += 9;
				}
			}
			else if (!pawns[me] && knights[me] == 2 && !bishops[me])
				mat[me] = (!tot[opp] && pawns[opp]) ? 6 : 0;
		}

		if (!mul[me])
			mat[me] = 0;
		if (mat[me] <= 1 && tot[me] != tot[opp])
			mul[me] = Min(mul[me], 8);
	}
	if (bishops[White] == 1 && bishops[Black] == 1 && light[White] != light[Black])
	{
		mul[White] = Min(mul[White], 20 + 3 * knights[Black] + major[Black]);
		mul[Black] = Min(mul[Black], 20 + 3 * knights[White] + major[White]);
	}
	else if (!minor[White] && !minor[Black] && major[White] == 1 && major[Black] == 1 && rooks[White] == rooks[Black])
	{
		for (int me = 0; me < 2; ++me)
			mul[me] = Min(mul[me], 24);
	}
	if (queens[White] == 1 && queens[Black] == 1 && !rooks[White] && !rooks[Black] && !knights[White] && !knights[Black] && bishops[White] == bishops[Black])
	{
		for (int me = 0; me < 2; ++me)
			mul[me] = Min(mul[me], 26);
	}
	for (int me = 0; me < 2; ++me)
		material.mul[me] = mul[me];
	material.score = (score * mat[score > 0 ? White : Black]) / 32;
	material.closed = Closed(special) + closed[White] - closed[Black]; // *mat[score > 0 ? White : Black]) / 32;
	material.eval = { nullptr, nullptr };
	for (int me = 0; me < 2; ++me)
	{
		if (F(major[me] + minor[me]))
			material.eval[me] = TEMPLATE_ME(eval_pawns_only);
		else if (F(major[me]) && minor[me] == 1)
		{
			if (bishops[me])
				material.eval[me] = pawns[me] ? TEMPLATE_ME(eval_single_bishop) : eval_unwinnable;
			else if (pawns[me] == 2 && bishops[opp] == 1)
				material.eval[me] = TEMPLATE_ME(eval_knppkbx);
			else if (pawns[me] <= 1)
				material.eval[me] = pawns[me] ? TEMPLATE_ME(eval_np) : eval_unwinnable;
		}
		else if (!pawns[me] && !queens[me] && rooks[me] == 1 && !knights[me] && bishops[me] == 1 && rooks[opp] == 1 && !minor[opp] && !queens[opp])
			material.eval[me] = TEMPLATE_ME(eval_krbkrx);
		else if (F(minor[me]) && major[me] == 1)
		{
			if (rooks[me])
			{
				if (F(pawns[me]) && T(pawns[opp]))
					material.eval[me] = TEMPLATE_ME(eval_krkpx);
				else if (rooks[opp] == 1)
				{
					if (pawns[me] == 1)
						material.eval[me] = TEMPLATE_ME(eval_krpkrx);
					else if (pawns[me] == 2)
						material.eval[me] = F(pawns[opp]) ? TEMPLATE_ME(eval_krppkrx) : TEMPLATE_ME(eval_krppkrpx);
					else if (pawns[me] == 3 && T(pawns[opp]))
						material.eval[me] = TEMPLATE_ME(eval_krpppkrppx);
				}
				else if (pawns[me] == 1 && T(bishops[opp]))
					material.eval[me] = TEMPLATE_ME(eval_krpkbx);
			}
			else if (F(pawns[me]) && T(pawns[opp]))
			{
				if (tot[opp] == 0 && pawns[opp] == 1)
					material.eval[me] = TEMPLATE_ME(eval_kqkpx);
				else if (rooks[opp])
					material.eval[me] = TEMPLATE_ME(eval_kqkrpx);
			}
		}
		else if (major[opp] + minor[opp] == 0)
			material.eval[me] = eval_null;	// just force the stalemate check
	}
}

void init_material(CommonData_* dst)
{
	dst->material_.resize(TotalMat);
	memset(&dst->material_[0], 0, TotalMat * sizeof(GMaterial));
	for (int index = 0; index < TotalMat; ++index)
		calc_material(index, dst->material_[index]);
}

void init_data(CommonData_* dst)
{
	init_misc(dst);
	dst->BMagic_ = MakeBMagic();
	dst->RMagic_ = MakeRMagic();
	gen_kpk(dst);
	init_eval(dst);
	init_material(dst);
}

packed_t eval_pst(const Board_& board)
{
	packed_t retval = 0;
	for (int i = 0; i < 64; ++i)
		if (auto p = board.PieceAt(i))
			retval += Pst(p, i);
	return retval;
}

void setup_board(std::array<uint8, 64> squares, State_* state)
{
	int i;

	PlyState_* current = state->current_;
	Board_* board = &state->board_;
	current->material = 0;
	board->square = squares;
	current->pst = eval_pst(*board);
	current->key = RO->PieceKey[0][0];
	if (current->turn)
		current->key ^= RO->TurnKey;
	current->key ^= RO->CastleKey[current->castle_flags];
	if (current->ep_square)
		current->key ^= RO->EPKey[FileOf(current->ep_square)];
	current->pawn_key = 0;
	current->pawn_key ^= RO->CastleKey[current->castle_flags];
	for (i = 0; i < 16; ++i) 
		board->Piece(i) = 0;
	for (i = 0; i < 64; ++i)
	{
		if (auto p = squares[i])
		{
			board->Piece(p) |= Bit(i);
			board->Piece(p & 1) |= Bit(i);
			current->key ^= RO->PieceKey[p][i];
			if (p < WhiteKnight)
				current->pawn_key ^= RO->PieceKey[p][i];
			if (p < WhiteKing)
				current->material += MatCode[p];
			else
				current->pawn_key ^= RO->PieceKey[p][i];
		}
	}
	if (popcnt(board->Piece(WhiteKnight)) > 2 || popcnt(board->Piece(WhiteLight)) > 1 || popcnt(board->Piece(WhiteDark)) > 1 || popcnt(board->Piece(WhiteRook)) > 2 || popcnt(board->Piece(WhiteQueen)) > 2 ||
		popcnt(board->Piece(BlackKnight)) > 2 || popcnt(board->Piece(BlackLight)) > 1 || popcnt(board->Piece(BlackDark)) > 1 || popcnt(board->Piece(BlackRook)) > 2 || popcnt(board->Piece(BlackQueen)) > 2)
		current->material |= FlagUnusualMaterial;
	current->capture = 0;
	current->killer = {};
	current->ply = 0;
	state->hashHist_.push_back(current->key);
}

const char* get_board(const char* fen, State_* state)
{
	int pos, i, j;
	unsigned char c;

	state->current_ = &state->stack_[0];
	memset(&state->board_, 0, sizeof(Board_));
	memset(state->current_, 0, sizeof(PlyState_));
	pos = 0;
	c = fen[pos];
	while (c == ' ') c = fen[++pos];
	for (i = 56; i >= 0; i -= 8)
	{
		for (j = 0; j <= 7;)
		{
			if (c <= '8')
				j += c - '0';
			else
			{
				state->board_.PieceAt(i + j) = PieceFromChar[c];
				if (Even(SDiagOf(i + j)) && (state->board_.PieceAt(i + j) / 2) == 3)
					state->board_.PieceAt(i + j) += 2;
				++j;
			}
			c = fen[++pos];
		}
		c = fen[++pos];
	}
	if (c == 'b')
		state->current_->turn = 1;
	c = fen[++pos];
	c = fen[++pos];
	if (c == '-')
		c = fen[++pos];
	if (c == 'K')
	{
		state->current_->castle_flags |= CanCastle_OO;
		c = fen[++pos];
	}
	if (c == 'Q')
	{
		state->current_->castle_flags |= CanCastle_OOO;
		c = fen[++pos];
	}
	if (c == 'k')
	{
		state->current_->castle_flags |= CanCastle_oo;
		c = fen[++pos];
	}
	if (c == 'q')
	{
		state->current_->castle_flags |= CanCastle_ooo;
		c = fen[++pos];
	}
	c = fen[++pos];
	if (c != '-')
	{
		auto turn = state->current_->turn;
		i = c + fen[++pos] * 8 - 489;
		j = i ^ 8;
		if (state->board_.PieceAt(i) != 0)
			i = 0;
		else if (state->board_.PieceAt(j) != (3 - turn))
			i = 0;
		else if (state->board_.PieceAt(j - 1) != (turn + 2) && state->board_.PieceAt(j + 1) != (turn + 2))
			i = 0;
		state->current_->ep_square = i;
	}
	setup_board(state->board_.square, state);
	return fen + pos;
}

void init_search(ThreadOwn_* info, State_* state, bool clear_hash, bool clear_board)
{
	for (int ip = 0; ip < 16; ++ip)
		for (int it = 0; it < 64; ++it)
		{
			state->historyVals_[ip][it][0] = (1 << 8) | 2;
			state->historyVals_[ip][it][1] = (1 << 8) | 2;
		}

	state->ClearStack();
	TheShare.depth_ = 0;
	TheShare.firstMove_ = true;
	if (clear_hash)
	{
		TheShare.date_ = 1;
		fill(TheHash.begin(), TheHash.end(), NullEntry);
		fill(ThePVHash.begin(), ThePVHash.end(), NullPVEntry);
		fill(state->deltaVals_.begin(), state->deltaVals_.end(), 0);
		fill(state->ref1_.begin(), state->ref1_.end(), Ref1_{});
	}
	if (clear_board)
		get_board("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", state);
	state->nodes_ = 0;
	state->tbHits_ = 0;
	state->selDepth_ = 0;
	info->results_.clear();
	info->lastTime_ = 0;
	memset(&state->searchInfo_, 0, sizeof(SearchInfo_));
	SetRootMoves(info);
}

INLINE GEntry* probe_hash(const PlyState_& current)
{
	GEntry* start = HashStart(current.key);
	for (GEntry* Entry = start; Entry < start + HASH_CLUSTER; ++Entry)
		if (Low32(current.key) == Entry->key)
		{
			Entry->date = TheShare.date_;
			return Entry;
		}
	return nullptr;
}

INLINE GPVEntry* probe_pv_hash(const PlyState_& current)
{
	GPVEntry* start = &ThePVHash[High32(current.key) & PV_HASH_MASK];
	for (GPVEntry* PVEntry = start; PVEntry < start + PV_CLUSTER; ++PVEntry)
		if (Low32(current.key) == PVEntry->key)
		{
			PVEntry->date = TheShare.date_;
			return PVEntry;
		}
	return nullptr;
}

bool IsValid(const Board_& board)
{
	for (int me = 0; me < 2; ++me)
	{
		if (F(board.King(me)) || Multiple(board.King(me)))
			return false;
		if (board.bb[me] ^ board.King(me) ^ board.Bishop(me) ^ board.Queen(me) ^ board.Rook(me) ^ board.Knight(me) ^ board.Pawn(me))
			return false;
	}
	return true;
}

template<bool me> void do_move(State_* state, int move)
{
	MOVING
	assert(IsValid(state->board_));
	GEntry* Entry;
	GPawnEntry* PawnEntry;
	int from, to, piece, capture;
	PlyState_* current = state->current_;
	PlyState_* next = state->current_ + 1;
	Board_* board = &state->board_;
	uint64 u, mask_from, mask_to;

	to = To(move);
	next->ep_square = 0;
	capture = board->PieceAt(to);
	from = From(move);
	piece = board->PieceAt(from);
	board->PieceAt(from) = 0;
	board->PieceAt(to) = piece;
	next->piece = piece;
	mask_from = Bit(from);
	mask_to = Bit(to);
	board->Piece(piece) ^= mask_from;
	board->Piece(me) ^= mask_from;
	board->Piece(piece) |= mask_to;
	board->Piece(me) |= mask_to;
	next->castle_flags = current->castle_flags;
	next->turn = opp;
	const auto& pKey = RO->PieceKey[piece];
	next->capture = capture;
	next->pst = current->pst + Pst(piece, to) - Pst(piece, from);
	next->key = current->key ^ pKey[to] ^ pKey[from];
	next->pawn_key = current->pawn_key;

	if (T(capture))
	{
		board->Piece(capture) ^= mask_to;
		board->Piece(opp) ^= mask_to;
		next->pst -= Pst(capture, to);
		next->key ^= RO->PieceKey[capture][to];
		if (capture == IPawn[opp])
			next->pawn_key ^= RO->PieceKey[IPawn[opp]][to];
		next->material = current->material - MatCode[capture];
		if (T(current->material & FlagUnusualMaterial) && capture >= WhiteKnight)
		{
			if (popcnt(board->Piece(WhiteQueen)) <= 2 && popcnt(board->Piece(BlackQueen)) <= 2 && popcnt(board->Piece(WhiteLight)) <= 1 && popcnt(board->Piece(BlackLight)) <= 1 &&
				popcnt(board->Piece(WhiteDark)) <= 1 && popcnt(board->Piece(BlackDark)) <= 1 && popcnt(board->Piece(WhiteKnight)) <= 2 && popcnt(board->Piece(BlackKnight)) <= 2 &&
				popcnt(board->Piece(WhiteRook)) <= 2 && popcnt(board->Piece(BlackRook)) <= 2)
				next->material ^= FlagUnusualMaterial;
		}
		if (piece == IPawn[me])
		{
			if (IsPromotion(move))
			{
				piece = Promotion<me>(move);
				board->PieceAt(to) = piece;
				next->material += MatCode[piece] - MatCode[IPawn[me]];
				if (IsBishop(piece) ? T(board->Piece(piece)) : Multiple(board->Piece(piece)))
					next->material |= FlagUnusualMaterial;
				board->Pawn(me) ^= mask_to;
				board->Piece(piece) |= mask_to;
				next->pst += Pst(piece, to) - Pst(IPawn[me], to);
				next->key ^= pKey[to] ^ RO->PieceKey[piece][to];
				next->pawn_key ^= pKey[from];
			}
			else
				next->pawn_key ^= pKey[from] ^ pKey[to];

			PawnEntry = &state->pawnHash_[next->pawn_key & PAWN_HASH_MASK];
			prefetch(PawnEntry);
		}
		else if (piece >= WhiteKing)
		{
			next->pawn_key ^= pKey[from] ^ pKey[to];
			PawnEntry = &state->pawnHash_[next->pawn_key & PAWN_HASH_MASK];
			prefetch(PawnEntry);
		}
		else if (capture < WhiteKnight)
		{
			PawnEntry = &state->pawnHash_[next->pawn_key & PAWN_HASH_MASK];
			prefetch(PawnEntry);
		}

		if (current->castle_flags && (piece >= WhiteRook || capture >= WhiteRook))
		{
			next->castle_flags &= UpdateCastling[to] & UpdateCastling[from];
			next->key ^= RO->CastleKey[current->castle_flags] ^ RO->CastleKey[next->castle_flags];
			next->pawn_key ^= RO->CastleKey[current->castle_flags] ^ RO->CastleKey[next->castle_flags];
		}
		if (F(next->material & FlagUnusualMaterial))
			prefetch(&RO->material_[next->material]);
		if (current->ep_square)
			next->key ^= RO->EPKey[FileOf(current->ep_square)];
		next->ply = 0;
	}
	else
	{
		next->ply = current->ply + 1;
		next->material = current->material;
		if (piece == IPawn[me])
		{
			next->ply = 0;
			next->pawn_key ^= pKey[to] ^ pKey[from];
			if (IsEP(move))
			{
				board->PieceAt(to ^ 8) = 0;
				u = Bit(to ^ 8);
				next->key ^= RO->PieceKey[IPawn[opp]][to ^ 8];
				next->pawn_key ^= RO->PieceKey[IPawn[opp]][to ^ 8];
				next->pst -= Pst(IPawn[opp], to ^ 8);
				board->Pawn(opp) &= ~u;
				board->Piece(opp) &= ~u;
				next->material -= MatCode[IPawn[opp]];
			}
			else if (IsPromotion(move))
			{
				piece = Promotion<me>(move);
				board->PieceAt(to) = piece;
				next->material += MatCode[piece] - MatCode[IPawn[me]];
				if (IsBishop(piece) ? T(board->Piece(piece)) : Multiple(board->Piece(piece)))
					next->material |= FlagUnusualMaterial;
				board->Pawn(me) ^= mask_to;
				board->Piece(piece) |= mask_to;
				next->pst += Pst(piece, to) - Pst(IPawn[me], to);
				next->key ^= RO->PieceKey[piece][to] ^ pKey[to];
				next->pawn_key ^= pKey[to];
			}
			else if ((to ^ from) == 16)
			{
				if (PAtt[me][(to + from) >> 1] & board->Pawn(opp))
				{
					next->ep_square = (to + from) >> 1;
					next->key ^= RO->EPKey[FileOf(next->ep_square)];
				}
			}
			PawnEntry = &state->pawnHash_[next->pawn_key & PAWN_HASH_MASK];
			prefetch(PawnEntry);
		}
		else
		{
			if (piece >= WhiteRook)
			{
				if (current->castle_flags)
				{
					next->castle_flags &= UpdateCastling[to] & UpdateCastling[from];
					next->key ^= RO->CastleKey[current->castle_flags] ^ RO->CastleKey[next->castle_flags];
					next->pawn_key ^= RO->CastleKey[current->castle_flags] ^ RO->CastleKey[next->castle_flags];
				}
				if (piece >= WhiteKing)
				{
					next->pawn_key ^= pKey[to] ^ pKey[from];
					PawnEntry = &state->pawnHash_[next->pawn_key & PAWN_HASH_MASK];
					prefetch(PawnEntry);
				}
			}

			if (IsCastling(piece, move))
			{
				next->ply = 0;
				int rold = to + ((to & 4) ? 1 : -2);
				int rnew = to + ((to & 4) ? -1 : 1);
				mask_to |= Bit(rnew);
				board->PieceAt(rold) = 0;
				board->PieceAt(rnew) = IRook[me];
				board->Piece(IRook[me]) ^= Bit(rold);
				board->Piece(me) ^= Bit(rold);
				board->Piece(IRook[me]) |= Bit(rnew);
				board->Piece(me) |= Bit(rnew);
				next->pst += Pst(IRook[me], rnew) - Pst(IRook[me], rold);
				next->key ^= RO->PieceKey[IRook[me]][rnew] ^ RO->PieceKey[IRook[me]][rold];
			}
		}

		if (current->ep_square)
			next->key ^= RO->EPKey[FileOf(current->ep_square)];
	}	// end F(Capture)

	next->key ^= RO->TurnKey;
	Entry = HashStart(next->key);
	prefetch(Entry);
	state->hashHist_.push_back(next->key);
	next->move = move;
	next->gen_flags = 0;
	state->current_ = next;
	++state->nodes_;
	assert(IsValid(*board));
	BYE
}
INLINE void do_move(State_* state, bool me, int move)
{
	if (me)
		do_move<true>(state, move);
	else
		do_move<false>(state, move);
}

template<bool me> void undo_move(State_* state, int move)
{
	MOVING
	const int from = From(move), to = To(move);
	uint64 bFrom = Bit(from), bTo = Bit(to);
	int piece;
	PlyState_* current = state->current_;
	Board_* board = &state->board_;

	if (IsPromotion(move))
	{
		board->Piece(board->PieceAt(to)) ^= bTo;
		piece = IPawn[me];
	}
	else
		piece = board->PieceAt(to);
	board->PieceAt(from) = piece;
	board->Piece(piece) |= bFrom;
	board->Piece(me) |= bFrom;
	board->Piece(piece) &= ~bTo;
	board->Piece(me) ^= bTo;
	board->PieceAt(to) = current->capture;
	if (current->capture)
	{
		board->Piece(current->capture) |= bTo;
		board->Piece(opp) |= bTo;
	}
	else
	{
		if (IsCastling(piece, move))
		{
			bool isQS = FileOf(to) == 2;
			const int rold = to + (isQS ? -2 : 1);
			const int rnew = to + (isQS ? 1 : -1);
			board->PieceAt(rnew) = 0;
			board->PieceAt(rold) = IRook[me];
			board->Rook(me) ^= Bit(rnew);
			board->Piece(me) ^= Bit(rnew);
			board->Rook(me) |= Bit(rold);
			board->Piece(me) |= Bit(rold);
		}
		else if (IsEP(move))
		{
			int xLoc = to ^ 8;
			board->PieceAt(xLoc) = IPawn[opp];
			board->Piece(opp) |= Bit(xLoc);
			board->Pawn(opp) |= Bit(xLoc);
		}
	}
	--state->current_;
	state->hashHist_.pop_back();
	BYE
}
INLINE void undo_move(State_* state, bool me, int move)
{
	if (me)
		undo_move<true>(state, move);
	else
		undo_move<false>(state, move);
}

void do_null(State_* state)
{
	PlyState_* current = state->current_;
	PlyState_* next = state->current_ + 1;

	next->key = current->key ^ RO->TurnKey;
	GEntry* Entry = HashStart(next->key);
	prefetch(Entry);
	next->pawn_key = current->pawn_key;
	next->eval_key = 0;
	next->turn = current->turn ^ 1;
	next->material = current->material;
	next->pst = current->pst;
	next->ply = 0;
	next->castle_flags = current->castle_flags;
	next->ep_square = 0;
	next->capture = 0;
	if (current->ep_square)
		next->key ^= RO->EPKey[FileOf(current->ep_square)];
	next->att[White] = current->att[White];
	next->att[Black] = current->att[Black];
	next->patt[White] = current->patt[White];
	next->patt[Black] = current->patt[Black];
	next->dbl_att[White] = current->dbl_att[White];
	next->dbl_att[Black] = current->dbl_att[Black];
	next->xray[White] = current->xray[White];
	next->xray[Black] = current->xray[Black];
	state->hashHist_.push_back(next->key);
	next->threat = current->threat;
	next->passer = current->passer;
	next->score = -current->score;
	next->move = 0;
	next->gen_flags = 0;
	state->current_ = next;
	++state->nodes_;
}

void undo_null(State_* state)
{
	--state->current_;
	state->hashHist_.pop_back();
}

struct ScopedMove_
{
	State_* state_;
	int move_;
	ScopedMove_(State_* state, int move) : state_(state), move_(move)
	{
		if (state_->current_->turn)
			do_move<1>(state_, move);
		else
			do_move<0>(state_, move);
	}
	~ScopedMove_()
	{
		if (state_->current_->turn ^ 1)
			undo_move<1>(state_, move_);
		else
			undo_move<0>(state_, move_);
	}
};

typedef struct
{
	uint64 patt[2], double_att[2];
	int king[2];
	packed_t score;
} GPawnEvalInfo;

template<bool me, class POP, class WATCH> INLINE void eval_pawns(GPawnEntry* PawnEntry, GPawnEvalInfo& PEI, const State_& state)
{
	constexpr array<array<uint64, 2>, 2> RFileBlockMask = { array<uint64, 2>({0x0202000000000000, 0x8080000000000000}), array<uint64, 2>({0x0202, 0x8080}) };
	POP pop;
	const Board_& board = state();
	int kf = FileOf(PEI.king[me]);
	int kr = RankOf(PEI.king[me]);
	int start, inc;
	if (kf <= 3)
	{
		start = Max(kf - 1, 0);
		inc = 1;
	}
	else
	{
		start = Min(kf + 1, 7);
		inc = -1;
	}
	int shelter = 0, sScale = 0;
	uint64 mpawns = board.Pawn(me) & Forward[me][me ? Min(kr + 1, 7) : Max(kr - 1, 0)];
	for (int file = start, i = 0; i < 3; file += inc, ++i)
	{
		shelter += RO->Shelter[i][OwnRank<me>(NBZ<me>(mpawns & File[file]))];
		if (board.Pawn(opp) & File[file])
		{
			int oppP = NB<me>(board.Pawn(opp) & File[file]);
			int rank = OwnRank<opp>(oppP);
			if (rank < 6)
			{
				if (rank >= 3)
					shelter += StormValues::Blocked[rank - 3];
				if (uint64 u = (PIsolated[FileOf(oppP)] & Forward[opp][RankOf(oppP)] & board.Pawn(me)))
				{
					int meP = NB<opp>(u);
					uint64 att_sq = PAtt[me][meP] & PWay[opp][oppP];  // may be zero
					if (abs(kf - FileOf(meP)) <= 1
						&& (!(PEI.double_att[me] & att_sq) || (state[0].patt[opp] & att_sq))
						&& F(PWay[opp][meP] & board.Pawn(me))
						&& (!(board.PawnAll() & PWay[opp][oppP] & Forward[me][RankOf(meP)])))
					{
						if (rank >= 3)
						{
							shelter += StormValues::ShelterAtt[rank - 3];
							if (HasBit(PEI.patt[opp], oppP + Push[opp]))
								shelter += StormValues::Connected[rank - 3];
							if (!(PWay[opp][oppP] & board.PawnAll()))
								shelter += StormValues::Open[rank - 3];
						}
						if (rank <= 4 && !(PCone[me][oppP] & board.King(opp)))
							shelter += StormValues::Free[rank - 1];
					}
				}
			}
		}
		else
		{
			if (i > 0 || T((File[file] | File[file + inc]) & (board.Rook(opp) | board.Queen(opp))) || T(RFileBlockMask[me][inc > 0] & ~(board.Pawn(opp) | board.King(opp))))
			{
				if (F(board.Pawn(me) & File[file]))
				{
					shelter += ShelterMod[StormOfValue];
					sScale += ShelterMod[StormOfScale];
				}
				else
				{
					shelter += ShelterMod[StormHofValue];
					sScale += ShelterMod[StormHofScale];
				}
			}
		}
	}
	PawnEntry->shelter[me] = shelter + (shelter * sScale) / 64;

	PawnEntry->passer[me] = 0;
	uint64 b;
	for (uint64 u = board.Pawn(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		int rank = RankOf(sq);
		int rrank = OwnRank<me>(sq);
		int file = FileOf(sq);
		uint64 way = PWay[me][sq];
		int next = board.PieceAt(sq + Push[me]);

		int isolated = !(board.Pawn(me) & PIsolated[file]);
		int doubled = T(board.Pawn(me) & (File[file] ^ b));
		int open = !(board.PawnAll() & way);

		if (isolated)
		{
			if (open)
				DecV(PEI.score, Values::IsolatedOpen);
			else
				DecV(PEI.score, Values::IsolatedClosed);
			if (F(open) && next == IPawn[opp])
				DecV(PEI.score, Values::IsolatedBlocked);
			if (doubled)
			{
				if (open)
					DecV(PEI.score, Values::IsolatedDoubledOpen);
				else
					DecV(PEI.score, Values::IsolatedDoubledClosed);
			}
		}
		else
		{
			if (doubled)
			{
				if (open)
					DecV(PEI.score, Values::DoubledOpen);
				else
					DecV(PEI.score, Values::DoubledClosed);
			}
			if (rrank >= 3 && (b & (File[2] | File[3] | File[4] | File[5])) && next != IPawn[opp] && (PIsolated[file] & Line[rank] & board.Pawn(me)))
			{
				IncVMultiple(PEI.score, rrank - 4, Values::PawnChainLinear);
				IncV(PEI.score, Values::PawnChain);
			}
		}
		int backward = 0;
		if (!(PSupport[me][sq] & board.Pawn(me)))
		{
			if (isolated)
				backward = 1;
			else if (uint64 v = (board.PawnAll() | PEI.patt[opp]) & way)
				if (OwnRank<me>(NB<me>(PEI.patt[me] & way)) > OwnRank<me>(NB<me>(v)))
					backward = 1;
		}
		if (backward)
		{
			if (open)
				DecV(PEI.score, Values::BackwardOpen);
			else
				DecV(PEI.score, Values::BackwardClosed);
		}
		else
		{
			NOTICE(rrank);
			if (open && (F(board.Pawn(opp) & PIsolated[file]) || pop(board.Pawn(me) & PIsolated[file]) >= pop(board.Pawn(opp) & PIsolated[file])))
				IncV(PEI.score, PasserValues::Candidate[rrank]);  // IDEA: more precise pawn counting for the case of, say,
														  // white e5 candidate with black pawn on f5 or f4...
		}

		if (F(PEI.patt[me] & b) && next == IPawn[opp])  // unprotected and can't advance
		{
			DecV(PEI.score, Values::UpBlocked);
			if (backward)
			{
				if (rrank <= 2)
				{
					DecV(PEI.score, Values::PasserTarget);
					if (rrank <= 1)
						DecV(PEI.score, Values::PasserTarget2);
				}	// Gull 3 was thinking of removing this term, because fitted weight is negative

				for (uint64 v = PAtt[me][sq] & board.Pawn(me); v; Cut(v)) if ((PSupport[me][lsb(v)] & board.Pawn(me)) == b)
				{
					DecV(PEI.score, Values::ChainRoot);
					break;
				}
			}
		}
		if (open && F(PCone[me][sq] & board.Pawn(opp)))
		{
			PawnEntry->passer[me] |= (uint8)(1 << file);
			if (rrank < 3) 
				 continue;
			//if (!(state[0].material & FlagUnusualMaterial))
			//{
			//	int deficit = (me ? 1 : -1) * Material[state[0].material].imbalance;
			//	if (rrank <= deficit) continue;
			//}
			NOTICE(rrank);
			IncV(PEI.score, PasserValues::General[rrank]);
			if (PEI.patt[me] & b)
				IncV(PEI.score, PasserValues::Protected[rrank]);
			if (F(board.Pawn(opp) & West[file]) || F(board.Pawn(opp) & East[file]))
				IncV(PEI.score, PasserValues::Outside[rrank]);
			// IDEA: average the distance with the distance to the promotion square? or just use the latter?
			int dist_att = Dist(PEI.king[opp], sq + Push[me]);
			int dist_def = Dist(PEI.king[me], sq + Push[me]);
			int value = dist_att * RO->PasserAtt[rrank] + RO->LogDist[dist_att] * RO->PasserAttLog[rrank]
				- dist_def * RO->PasserDef[rrank] - RO->LogDist[dist_def] * RO->PasserDefLog[rrank];  // IDEA -- incorporate side-to-move in closer-king check?
			// IDEA -- scale down rook pawns?
			IncV(PEI.score, Pack(0, value / 256));
		}
	}
	if (T(board.Rook(opp)) && !((kf * kr) % 7))
	{
		const uint64 kAdj = KAtt[PEI.king[me]];
		// look for opp pawns restricting K mobility
		if (PEI.patt[opp] & kAdj)
		{
			// find out which one it is
			for (uint64 u = board.Pawn(opp); T(u); u ^= b)
			{
				int sq = lsb(u);
				b = Bit(sq);
				if ((PAtt[opp][sq] & kAdj) && HasBit(board.Pawn(me), sq + Push[opp]))
					DecV(PEI.score, Values::PawnRestrictsK);
			}
		}
	}

	uint64 files = board.Pawn(me) | (board.Pawn(me) >> 32);
	files |= files >> 16;
	files = (files | (files >> 8)) & 0xFF;
	int file_span = (files ? (msb(files) - lsb(files)) : 0);

	PawnEntry->draw[me] = (7 - file_span) * Max(5 - pop(files), 0);
}

template<class POP, class WATCH> INLINE void eval_pawn_structure(const GEvalInfo& EI, GPawnEntry* PawnEntry, const State_& state)
{
	GPawnEvalInfo PEI;
	for (int i = 0; i < sizeof(GPawnEntry) / sizeof(int); ++i)
		*(((int*)PawnEntry) + i) = 0;
	PawnEntry->key = state[0].pawn_key;

	PEI.patt[White] = state[0].patt[White];
	PEI.patt[Black] = state[0].patt[Black];
	PEI.double_att[White] = ShiftW<White>(state().Pawn(White)) & ShiftE<White>(state().Pawn(White));
	PEI.double_att[Black] = ShiftW<Black>(state().Pawn(Black)) & ShiftE<Black>(state().Pawn(Black));
	PEI.king[White] = EI.king[White];
	PEI.king[Black] = EI.king[Black];
	PEI.score = 0;

	eval_pawns<White, POP, WATCH>(PawnEntry, PEI, state);
	eval_pawns<Black, POP, WATCH>(PawnEntry, PEI, state);

	PawnEntry->score = PEI.score;
}

template<bool me, class WATCH> INLINE void eval_queens_xray(GEvalInfo& EI, const State_& state)
{
	const Board_& board = state();
	uint64 u, b;
	for (u = board.Queen(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		uint64 att = QueenAttacks(sq, EI.occ);
		state[0].dbl_att[me] |= att & state[0].att[me];
		state[0].att[me] |= att;
		if (QMask[sq] & board.King(opp))
			if (uint64 v = Between[EI.king[opp]][sq] & EI.occ)
				if (Single(v))
				{
					state[0].xray[me] |= v;
					(RMask[sq] & board.King(opp) ? EI.rray : EI.bray) |= v;
					int square = lsb(v);
					int piece = board.PieceAt(square);
					int katt = 0;
					if (piece == IPawn[me])
					{
						if (!board.PieceAt(square + Push[me]))
							IncV(EI.score, Values::QueenPawnPin);
					}
					else if ((piece & 1) == me)
					{
						IncV(EI.score, Values::QueenSelfPin);
						katt = 1;
					}
					else if (piece != IPawn[opp] && !(((BMask[sq] & board.Bishop(opp)) | (RMask[sq] & board.Rook(opp)) | board.Queen(opp)) & v))
					{
						IncV(EI.score, Values::QueenWeakPin);
						if (!(state[0].patt[opp] & v))
							katt = 1;
					}
					if (katt && !(att & EI.area[opp]))
						EI.king_att[me] += KingAttack;
				}
				else if (F(v & ~board.Minor(opp)))
					IncV(EI.score, Values::QKingRay);
	}
}

template<bool me, class POP, class WATCH> INLINE void eval_queens(GEvalInfo& EI, const State_& state)
{
	POP pop;
	const Board_& board = state();
	for (uint64 b, u = board.Queen(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		uint64 att = QueenAttacks(sq, EI.occ);

		if (uint64 a = att & EI.area[opp] & ~(state[0].patt[opp] & state[0].dbl_att[opp]))
		{
			EI.king_att[me] += Single(a) ? KingQAttack1 : KingQAttack;
			for (uint64 v = att & EI.area[opp]; T(v); Cut(v))
				if (FullLine[sq][lsb(v)] & att & ((board.Rook(me) & RMask[sq]) | (board.Bishop(me) & BMask[sq])))
					EI.king_att[me]++;
		}
		uint64 control = att & EI.free[me];
		NOTICE(pop(control));
		IncV(EI.score, RO->MobQueen[0][pop(control)]);
		IncV(EI.score, RO->MobQueen[1][pop(control & RO->LocusQ[me][EI.king[opp]])]);
		if (control & board.Pawn(opp))
			IncV(EI.score, Values::TacticalQueenPawn);
		if (control & board.Minor(opp))
			IncV(EI.score, Values::TacticalQueenMinor);
		if (att & EI.area[me])
			IncV(EI.score, Values::KingDefQueen);
	}
}

template<bool me, class WATCH> INLINE void eval_rooks_xray(GEvalInfo& EI, const State_& state)
{
	const Board_& board = state();
	for (uint64 b, u = board.Rook(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		uint64 att = RookAttacks(sq, EI.occ);
		state[0].dbl_att[me] |= att & state[0].att[me];
		state[0].att[me] |= att;
		if (RMask[sq] & board.King(opp))
			if (uint64 v = Between[EI.king[opp]][sq] & EI.occ)
				if (Single(v))
				{
					state[0].xray[me] |= v;
					EI.rray |= v;
					int square = lsb(v);
					int piece = board.PieceAt(square);
					int katt = 0;
					if (piece == IPawn[me])
					{
						if (!board.PieceAt(square + Push[me]))
							IncV(EI.score, Values::RookPawnPin);
					}
					else if ((piece & 1) == me)
					{
						IncV(EI.score, Values::RookSelfPin);
						katt = 1;
					}
					else if (piece != IPawn[opp])
					{
						if (piece < WhiteRook)
						{
							IncV(EI.score, Values::RookWeakPin);
							if (!(state[0].patt[opp] & v))
								katt = 1;
						}
						else if (piece >= WhiteQueen)
							IncV(EI.score, Values::RookThreatPin);
					}
					if (katt && F(att & EI.area[opp]))
						EI.king_att[me] += KingAttack;
				}
				else if (F(v & ~board.Minor(opp) & ~board.Queen(opp)))
					IncV(EI.score, Values::RKingRay);
	}
}

template<bool me, class POP, class WATCH> INLINE void eval_rooks(GEvalInfo& EI, const State_& state)
{
	POP pop;
	const Board_& board = state();
	for (uint64 b, u = board.Rook(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		uint64 att = RookAttacks(sq, EI.occ);
		if (uint64 a = att & EI.area[opp] & ~(state[0].patt[opp] & state[0].dbl_att[opp]))
		{
			EI.king_att[me] += Single(a) ? KingRAttack1 : KingRAttack;
			for (uint64 v = att & EI.area[opp]; T(v); Cut(v))
				if (FullLine[sq][lsb(v)] & att & board.Major(me))
					EI.king_att[me]++;
		}
		state[0].threat |= att & board.Queen(opp);
		uint64 control = att & EI.free[me];
		NOTICE(pop(control));
		IncV(EI.score, RO->MobRook[0][pop(control)]);
		IncV(EI.score, RO->MobRook[1][pop(control & RO->LocusR[me][EI.king[opp]])]);
		if (control & board.Pawn(opp))
			IncV(EI.score, Values::TacticalRookPawn);
		if (control & board.Minor(opp))
			IncV(EI.score, Values::TacticalRookMinor);

		if (!(PWay[me][sq] & board.Pawn(me)))
		{
			IncV(EI.score, Values::RookHof);
			int force = T(PWay[opp][sq] & att & board.Major(me)) ? 2 : 1;
			if (!(PWay[me][sq] & board.Pawn(opp)))
			{
				IncV(EI.score, Values::RookOf);
				if (uint64 target = att & PWay[me][sq] & board.Minor(opp))
				{
					if (!(state[0].patt[opp] & target))
					{
						IncVMultiple(EI.score, force, Values::RookOfMinorHanging);
						if (PWay[me][sq] & board.King(opp))
							IncVMultiple(EI.score, force, Values::RookOfKingAtt);
					}
				}
			}
			else if (uint64 attP = att & PWay[me][sq] & board.Pawn(opp))
			{
				int square = lsb(attP);
				if (!(PSupport[opp][square] & board.Pawn(opp)))
					IncVMultiple(EI.score, force, Values::RookHofWeakPAtt);
			}
		}
		if ((b & OwnLine<me>(6)) && ((board.King(opp) | board.Pawn(opp)) & (OwnLine<me>(6) | OwnLine<me>(7))))
		{
			IncV(EI.score, Values::Rook7th);
			if (board.King(opp) & OwnLine<me>(7))
				IncV(EI.score, Values::Rook7thK8th);
			if (board.Major(me) & att & OwnLine<me>(6))
				IncV(EI.score, Values::Rook7thDoubled);
		}
	}
}

template<bool me, class WATCH> INLINE void eval_bishops_xray(GEvalInfo& EI, const State_& state)
{
	const Board_& board = state();
	for (uint64 b, u = board.Bishop(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		uint64 att = BishopAttacks(sq, EI.occ);
		state[0].dbl_att[me] |= att & state[0].att[me];
		state[0].att[me] |= att;
		if (BMask[sq] & board.King(opp))
			if (uint64 v = Between[EI.king[opp]][sq] & EI.occ)
				if (Single(v))  // pin or discovery threat
				{
					state[0].xray[me] |= v;
					EI.bray |= v;
					int square = lsb(v);
					int piece = board.PieceAt(square);
					int katt = 0;
					if (piece == IPawn[me])
					{
						if (!board.PieceAt(square + Push[me]))
							IncV(EI.score, Values::BishopPawnPin);
					}
					else if ((piece & 1) == me)
					{
						IncV(EI.score, Values::BishopSelfPin);
						katt = 1;
					}
					else if (piece != IPawn[opp])
					{
						if (piece < WhiteLight)
						{
							IncV(EI.score, Values::StrongPin);
							if (!(state[0].patt[opp] & v))
								katt = 1;
						}
						else if (piece >= WhiteRook)
							IncV(EI.score, Values::BishopThreatPin);
					}
					if (katt && F(att & EI.area[opp]))
						EI.king_att[me] += KingAttack;
				}
				else if (F(v & ~(board.Knight(opp) | board.Major(opp))))
					IncV(EI.score, Values::BKingRay);
	}
}

template<bool me, class POP, class WATCH> INLINE void eval_bishops(GEvalInfo& EI, const State_& state)
{
	POP pop;
	const Board_& board = state();
	for (uint64 b, u = board.Bishop(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		uint64 att = BishopAttacks(sq, EI.occ);
		if (uint64 a = att & EI.area[opp] & ~(state[0].patt[opp] & state[0].dbl_att[opp]))
			EI.king_att[me] += Single(a) ? KingBAttack1 : KingBAttack;
		uint64 control = att & EI.free[me];
		NOTICE(pop(control));
		IncV(EI.score, RO->MobBishop[0][pop(control)]);
		IncV(EI.score, RO->MobBishop[1][pop(control & RO->LocusB[me][EI.king[opp]])]);
		if (control & board.Pawn(opp))
			IncV(EI.score, Values::TacticalBishopPawn);
		if (control & board.Knight(opp))
			IncV(EI.score, Values::TacticalB2N);
		state[0].threat |= att & board.Major(opp);
		if (T(b & Outpost[me])
			&& F(board.Knight(opp))
			&& T(state[0].patt[me] & b)
			&& F(board.Pawn(opp) & PIsolated[FileOf(sq)] & Forward[me][RankOf(sq)])
			&& F(board.Piece((T(b & LightArea) ? WhiteLight : WhiteDark) | opp)))
			IncV(EI.score, Values::BishopOutpostNoMinor);
	}
}

template<bool me> INLINE void eval_knights_xray(GEvalInfo& EI, const State_& state)
{
	const Board_& board = state();
	for (uint64 u = board.Knight(me); T(u); Cut(u))
	{
		uint64 att = NAtt[lsb(u)];
		state[0].dbl_att[me] |= state[0].att[me] & att;
		state[0].att[me] |= att;
	}
}

template<bool me, class POP, class WATCH> INLINE packed_t eval_knights(GEvalInfo& EI, const State_& state)
{
	POP pop;
	const Board_& board = state.board_;
	packed_t eval = 0;
	for (uint64 b, u = board.Knight(me); T(u); u ^= b)
	{
		int sq = lsb(u);
		b = Bit(sq);
		uint64 att = NAtt[sq];
		if (uint64 a = att & EI.area[opp] & ~(state[0].patt[opp] & state[0].dbl_att[opp]))
			EI.king_att[me] += Single(a) ? KingNAttack1 : KingNAttack;
		state[0].threat |= att & board.Major(opp);
		uint64 control = att & EI.free[me];
		NOTICE(pop(control));
		IncV(EI.score, RO->MobKnight[0][pop(control)]);
		IncV(EI.score, RO->MobKnight[1][pop(control & RO->LocusN[me][EI.king[opp]])]);
		if (control & board.Bishop(opp))
			IncV(EI.score, Values::TacticalN2B);
		if (att & EI.area[me])
			IncV(EI.score, Values::KingDefKnight);
		if ((b & Outpost[me]) && !(board.Pawn(opp) & PIsolated[FileOf(sq)] & Forward[me][RankOf(sq)]))
		{
			IncV(EI.score, Values::KnightOutpost);
			if (state[0].patt[me] & b)
			{
				IncV(EI.score, Values::KnightOutpostProtected);
				if (att & EI.free[me] & board.Pawn(opp))
					IncV(EI.score, Values::KnightOutpostPawnAtt);
				if (F(board.Knight(opp) | board.Piece((T(b & LightArea) ? WhiteLight : WhiteDark) | opp)))
					IncV(EI.score, Values::KnightOutpostNoMinor);
			}
		}
	}

	return eval;
}

// weight constants
constexpr array<uint16, 16> KingAttackScale = { 0, 1, 1, 2, 4, 5, 8, 12, 15, 19, 23, 28, 33, 37, 39, 39 };
constexpr array<int, 8> KingCenterShift = { -5, -4, 5, 1 };	

template<bool me, class POP, class WATCH> INLINE void eval_king(GEvalInfo& EI, const State_& state)
{
	POP pop;
	const Board_& board = state();
	uint16 cnt = Min<uint16>(15, Pick16<1>(EI.king_att[me]));
	uint16 score = Pick16<2>(EI.king_att[me]);
	if (cnt >= 2 && T(board.Queen(me)))
	{
		score += (EI.pawnEval_.shelter[opp] * KingShelterQuad) / 64;
		if (uint64 u = state[0].att[me] & EI.area[opp] & (~state[0].att[opp]))
			score += pop(u) * KingAttackSquare;
		if (!(KAtt[EI.king[opp]] & (~(board.Piece(opp) | state[0].att[me]))))
			score += KingNoMoves;
	}
	int adjusted = ((score * KingAttackScale[cnt]) >> 3) + EI.pawnEval_.shelter[opp];
	int kf = FileOf(EI.king[opp]), kr = OwnRank<opp>(EI.king[opp]);
	if (kf > 3)
		kf = 7 - kf;
	if (kr < 3)
		adjusted += (adjusted * (3 - kr) * KingCenterShift[kf]) / 160;
	if (!board.Queen(me))
		adjusted = (adjusted * KingSafetyNoQueen) / 16;
	// add a correction for defense-in-depth
	if (adjusted > 1)
	{
		uint64 holes = RO->LocusK[me][EI.king[opp]] & ~state[0].att[opp];
		int nHoles = pop(holes);
		int nIncursions = pop(holes & state[0].att[me]);
		uint64 personnel = board.NonPawnKing(opp);
		uint64 guards = RO->LocusK[me][EI.king[opp]] & personnel;
		uint64 awol = personnel ^ guards;
		int nGuards = pop(guards) + pop(guards & board.Queen(opp));
		int nAwol = pop(awol) + pop(awol & board.Queen(opp));
		adjusted += (adjusted * (max(0, nAwol - nGuards) + max(0, 3 * nIncursions + nHoles - 10))) / 32;
	}

	static constexpr array<int, 4> PHASE = { 23, 19, 3, -2 };
	int op = ((PHASE[0] + kr) * adjusted) / 32;
	int md = (PHASE[1] * adjusted) / 32;
	int eg = (PHASE[2] * adjusted) / 32;
	int cl = (PHASE[3] * adjusted) / 32;
	NOTICE(cnt);
	IncV(EI.score, Pack(op, md, eg, cl));
}

template<bool me, class POP, class WATCH> INLINE void eval_passer(GEvalInfo& EI, const State_& state)
{
	const Board_& board = state();
	bool sr_me = board.Rook(me) && !board.Minor(me) && !board.Queen(me) && Single(board.Rook(me));
	bool sr_opp = board.Rook(opp) && !board.Minor(opp) && !board.Queen(opp) && Single(board.Rook(opp));

	for (uint8 u = EI.pawnEval_.passer[me]; T(u); u &= (u - 1))
	{
		int file = lsb(u);
		int sq = NB<opp>(File[file] & board.Pawn(me));  // most advanced in this file
		int rank = OwnRank<me>(sq);
		state[0].passer |= Bit(sq);
		if (rank <= 2)
			continue;
		if (!board.PieceAt(sq + Push[me]))
			IncV(EI.score, PasserValues::Movable[rank]);
		uint64 way = PWay[me][sq];
		int connected = 0, supported = 0, hooked = 0, unsupported = 0, free = 0;
		if (!(way & board.Piece(opp)))
		{
			IncV(EI.score, PasserValues::Clear[rank]);
			if (PWay[opp][sq] & board.Major(me))
			{
				int square = NB<opp>(PWay[opp][sq] & board.Major(me));
				if (F(Between[sq][square] & EI.occ))
					supported = 1;
			}
			if (PWay[opp][sq] & board.Major(opp))
			{
				int square = NB<opp>(PWay[opp][sq] & board.Major(opp));
				if (F(Between[sq][square] & EI.occ))
					hooked = 1;
			}
			for (uint64 v = PAtt[me][sq - Push[me]] & board.Pawn(me); T(v); Cut(v))
			{
				int square = lsb(v);
				if (F(board.Pawn(opp) & (VLine[square] | PIsolated[FileOf(square)]) & Forward[me][RankOf(square)]))
					++connected;
			}
			if (connected)
			{
				IncVMultiple(EI.score, 7 + min(file, 7 - file), PasserValues::Connected[rank]);
			}
			if (!hooked && !(state[0].att[opp] & way))
			{
				IncV(EI.score, PasserValues::Free[rank]);
				free = 1;
			}
			else
			{
				uint64 attacked = state[0].att[opp] | (hooked ? way : 0);
				if (supported || (!hooked && connected) || (!(board.Major(me) & way) && !(attacked & (~state[0].att[me]))))
					IncV(EI.score, PasserValues::Supported[rank]);
				else
					unsupported = 1;
			}
		}

		if (sr_me)
		{
			if (rank == 6 && T(way & board.Rook(me)))
				DecV(EI.score, Values::PasserOpRookBlock);
		}
	}
}


template<bool me, class POP, class WATCH> INLINE void eval_pieces(GEvalInfo& EI, const State_& state)
{
	POP pop;
	uint64 threat = state[0].att[opp] & (~state[0].att[me]) & state().Piece(me);
	state[0].threat |= threat;
	if (Multiple(threat))
	{
		DecV(EI.score, Values::ThreatDouble);
		DecV(EI.score, (pop(threat) - 2) * Values::Threat);
	}
	else if (threat)
		DecV(EI.score, Values::Threat);
}

template<class POP, class WATCH> void eval_unusual_material(GEvalInfo& EI, const State_& state)
{
	POP pop;
	const Board_& board = state();
	state[0].score = Endgame(EI.score)
		+ SeeValue[WhitePawn] * (pop(board.Pawn(White)) - pop(board.Pawn(Black)))
		+ SeeValue[WhiteKnight] * (pop(board.Minor(White)) - pop(board.Minor(Black)))
		+ SeeValue[WhiteRook] * (pop(board.Rook(White)) - pop(board.Rook(Black)))
		+ SeeValue[WhiteQueen] * (pop(board.Queen(White)) - pop(board.Queen(Black)));
}

template<int me, class POP> int closure_x(const State_& state)
{
	POP pop;
	const Board_& board = state();
	int run = 0;
	uint64 mine = board.Pawn(me);
	int np = pop(mine);
	uint64 keep = ~(mine | board.Pawn(opp));	// hard stop if we run into a pawn
	uint64 soft = (state[0].patt[opp] | board.Piece(opp)) & ~mine;
	keep &= ~Shift<me>(soft);// if we run into a piece or pawn capture, count 1 then stop
	for (; ;)
	{
		mine = keep & Shift<me>(mine);
		if (F(mine))
			break;
		run += pop(mine);
	}
	return 2 * np - run;
}

template<class POP> int closure(const State_& state)
{
	// closure_x can return up to 16; we want to return about -128 to +128
	return 4 * (closure_x<0, POP>(state) + closure_x<1, POP>(state));
}

template<bool me, class WATCH> void eval_xray(GEvalInfo& EI, const State_& state)
{
	EI.king_att[me] = 0;
	if (uint64 pa = state[0].patt[me] & EI.area[opp])
	{
		EI.king_att[me] = KingAttack + (Multiple(pa) ? KingPAttackInc : 0);
		if (uint64 oppKing = state().King(opp); T(oppKing & Boundary))
			if (Shift<me>(state().Pawn(opp)) & oppKing)
				if (uint64 restrictingPawn = Shift<opp>(Shift<opp>(oppKing)) & state().Pawn(me))
					if (T(state[0].patt[me] & restrictingPawn) || F(state[0].patt[opp] & restrictingPawn))
						EI.king_att[me] += KingPRestrict;
	}
	state[0].xray[me] = 0;
	eval_queens_xray<me, WATCH>(EI, state);
	eval_rooks_xray<me, WATCH>(EI, state);
	eval_bishops_xray<me, WATCH>(EI, state);
	eval_knights_xray<me>(EI, state);
}

template<bool me, class POP, class WATCH> void eval_sequential(GEvalInfo& EI, const State_& state)
{
	const Board_& board = state();
	EI.free[me] = board.Queen(opp) | board.King(opp) | (~(state[0].patt[opp] | board.Pawn(me) | board.King(me)));
	DecV(EI.score, POP()(Shift<opp>(EI.occ) & board.Pawn(me)) * Values::PawnBlocked);
	eval_queens<me, POP, WATCH>(EI, state);
	EI.free[me] |= board.Rook(opp);
	eval_rooks<me, POP, WATCH>(EI, state);
	EI.free[me] |= board.Minor(opp);
	eval_bishops<me, POP, WATCH>(EI, state);
	eval_knights<me, POP, WATCH>(EI, state);
}

template<class POP> struct PhasedScore_
{
	const GMaterial& mat_;
	int clx_;
	PhasedScore_(const State_& state, const GMaterial& mat) : mat_(mat), clx_(closure<POP>(state)) {}
	int operator()(packed_t score)
	{
		int phase = mat_.phase, op = Opening(score), eg = Endgame(score), md = Middle(score), cl = Closed(score);
		int retval;
		if (mat_.phase > MIDDLE_PHASE)
			retval = (op * (phase - MIDDLE_PHASE) + md * (MAX_PHASE - phase)) / PHASE_M2M;
		else
			retval = (md * phase + eg * (MIDDLE_PHASE - phase)) / MIDDLE_PHASE;
		retval += static_cast<sint16>((clx_ * (Min<int>(phase, MIDDLE_PHASE) * cl + MIDDLE_PHASE * mat_.closed)) / 8192);	// closure is capped at 128, phase at 64
		return retval;
	}
};


template<class POP, class WATCH> void evaluation(State_* state)
{
	POP pop;
	GEvalInfo EI;
	const Board_& board = state->board_;
	PlyState_* current = state->current_;

	if (current->eval_key == current->key)
		return;
	current->eval_key = current->key;

	EI.king[White] = lsb(board.King(White));
	EI.king[Black] = lsb(board.King(Black));
	EI.occ = board.PieceAll();
	current->att[White] = current->patt[White] = ShiftW<White>(board.Pawn(White)) | ShiftE<White>(board.Pawn(White));
	current->att[Black] = current->patt[Black] = ShiftW<Black>(board.Pawn(Black)) | ShiftE<Black>(board.Pawn(Black));
	current->dbl_att[White] = ShiftW<White>(board.Pawn(White)) & ShiftE<White>(board.Pawn(White));
	current->dbl_att[Black] = ShiftW<Black>(board.Pawn(Black)) & ShiftE<Black>(board.Pawn(Black));
	EI.area[White] = (KAtt[EI.king[White]] | board.King(White)) & ((~current->patt[White]) | current->patt[Black]);
	EI.area[Black] = (KAtt[EI.king[Black]] | board.King(Black)) & ((~current->patt[Black]) | current->patt[White]);
	current->passer = 0;
	current->threat = (current->patt[White] & board.NonPawn(Black)) | (current->patt[Black] & board.NonPawn(White));
	EI.score = current->pst;
	if (F(current->material & FlagUnusualMaterial))
		EI.material = &RO->material_[current->material];
	else
		EI.material = nullptr;

	eval_xray<White, WATCH>(EI, *state);
	eval_xray<Black, WATCH>(EI, *state);
	eval_sequential<White, POP, WATCH>(EI, *state);
	eval_sequential<Black, POP, WATCH>(EI, *state);

	EI.pawnEntry_ = &state->pawnHash_[current->pawn_key & PAWN_HASH_MASK];
	if (current->pawn_key == EI.pawnEntry_->key)
		EI.pawnEval_ = *EI.pawnEntry_;
	else
	{
		EI.pawnEntry_ = nullptr;
		eval_pawn_structure<POP, WATCH>(EI, &EI.pawnEval_, *state);
		state->pawnHash_[current->pawn_key & PAWN_HASH_MASK] = EI.pawnEval_;
	}
	EI.score += EI.pawnEval_.score;

	eval_king<White, POP, WATCH>(EI, *state);
	eval_king<Black, POP, WATCH>(EI, *state);
	current->att[White] |= KAtt[EI.king[White]];
	current->att[Black] |= KAtt[EI.king[Black]];

	eval_passer<White, POP, WATCH>(EI, *state);
	eval_pieces<White, POP, WATCH>(EI, *state);
	eval_passer<Black, POP, WATCH>(EI, *state);
	eval_pieces<Black, POP, WATCH>(EI, *state);

	if (current->material & FlagUnusualMaterial)
	{
		eval_unusual_material<POP, WATCH>(EI, *state);
		current->score = (current->score * CP_SEARCH) / CP_EVAL;
	}
	else
	{
		const GMaterial& mat = *EI.material;
		PhasedScore_<POP> value(*state, mat);
		current->score = mat.score + value(EI.score);
		
		// apply contempt before drawishness
		if (SETTINGS.contempt > 0)
		{
			int maxContempt = (mat.phase * SETTINGS.contempt * CP_EVAL) / 64;
			int mySign = F(state->stack_[0].turn) ? 1 : -1;
			if (current->score * mySign > 2 * maxContempt)
				current->score += mySign * maxContempt;
			else if (current->score * mySign > 0)
				current->score += current->score / 2;
		}

		if (current->ply >= PliesToEvalCut)
			current->score /= 2;
		const int drawCap = DrawCapConstant + (DrawCapLinear * abs(current->score)) / 64;  // drawishness of pawns can cancel this much of the score
		if (current->score > 0)
		{
			EI.mul = mat.mul[White];
			if (mat.eval[White] && !eval_stalemate<White>(EI, *state))
				mat.eval[White](EI, *state, pop.Imp());
			else if (EI.mul <= 32)
			{
				EI.mul = Min<uint16>(EI.mul, 37 - value.clx_ / 8);
				if (T(current->passer & board.Pawn(White)) && T(current->passer & board.Pawn(Black)))
				{
					int rb = OwnRank<Black>(lsb(current->passer & board.Pawn(Black))), rw = OwnRank<White>(msb(current->passer & board.Pawn(White)));
					if (rb > rw)
						EI.mul = Min<uint16>(EI.mul, 43 - Square(rb) / 2);
				}
			}

			current->score -= (Min<int>(current->score, drawCap) * EI.pawnEval_.draw[White]) / 64;
		}
		else if (current->score < 0)
		{
			EI.mul = mat.mul[Black];
			if (mat.eval[Black] && !eval_stalemate<Black>(EI, *state))
				mat.eval[Black](EI, *state, pop.Imp());
			else if (EI.mul <= 32)
			{
				EI.mul = Min<uint16>(EI.mul, 37 - value.clx_ / 8);
				if (T(current->passer & board.Pawn(White)) && T(current->passer & board.Pawn(Black)))
				{
					int rb = OwnRank<Black>(lsb(current->passer & board.Pawn(Black))), rw = OwnRank<White>(msb(current->passer & board.Pawn(White)));
					if (rw > rb)
						EI.mul = Min<uint16>(EI.mul, 43 - Square(rw) / 2);
				}
			}
			current->score += (Min<int>(-current->score, drawCap) * EI.pawnEval_.draw[Black]) / 64;
		}
		else
			EI.mul = Min(EI.material->mul[White], EI.material->mul[Black]);
		current->score = (current->score * EI.mul * CP_SEARCH) / (32 * CP_EVAL);
	}
	if (current->turn)
		current->score = -current->score;
	if (F(current->capture) && T(current->move) && F(current->move & 0xE000) && state->Height() > 0)
	{
		sint16& delta = DeltaScore(state, current->piece, From(current->move), To(current->move));
		const sint16 observed = -current->score - (current - 1)->score;
		if (observed >= delta)
			delta = observed;
		else
			delta -= DeltaDecrement;
	}
}

INLINE void evaluate(State_* state)
{
	evaluation<pop1_, NoWatch_>(state);	// assume we have hardware popcount
}

template<bool me> bool is_legal(const State_& state, int move)
{
	const Board_& board = state();
	uint64 u, occ;

	int from = From(move), to = To(move);
	int piece = board.square[from], capture = board.square[to];
	if (piece == 0)
		return 0;
	if ((piece & 1) != state[0].turn)
		return 0;
	if (capture)
	{
		if ((capture & 1) == (piece & 1))
			return 0;
		if (capture >= WhiteKing)
			return 0;
	}
	occ = board.PieceAll();
	u = Bit(to);
	if (piece >= WhiteLight && piece < WhiteKing)
	{
		if ((QMask[from] & u) == 0)
			return 0;
		if (Between[from][to] & occ)
			return 0;
	}
	if (IsEP(move))
	{
		if (piece >= WhiteKnight)
			return 0;
		if (state[0].ep_square != to)
			return 0;
		return 1;
	}
	if (IsCastling(piece, move) && board.square[from] < WhiteKing)
		return 0;
	if (IsPromotion(move) && board.square[from] >= WhiteKnight)
		return 0;
	if (piece == IPawn[me])
	{
		if (HasBit(u, from + Push[me]))
		{
			if (capture)
				return 0;
			if (T(u & OwnLine<me>(7)) && !IsPromotion(move))
				return 0;
			return 1;
		}
		else if (to == (from + 2 * Push[me]))
		{
			if (capture)
				return 0;
			if (board.PieceAt(to - Push[me]))
				return 0;
			if (F(u & OwnLine<me>(3)))
				return 0;
			return 1;
		}
		else if (u & PAtt[me][from])
		{
			if (capture == 0)
				return 0;
			if (T(u & OwnLine<me>(7)) && !IsPromotion(move))
				return 0;
			return 1;
		}
		else
			return 0;
	}
	else if (piece == IKing[me])
	{
		if (me == White)
		{
			if (IsCastling(piece, move))
			{
				if (u & 0x40)
				{
					if (F(state[0].castle_flags & CanCastle_OO))
						return 0;
					if (occ & 0x60)
						return 0;
					if (state[0].att[Black] & 0x70)
						return 0;
				}
				else
				{
					if (F(state[0].castle_flags & CanCastle_OOO))
						return 0;
					if (occ & 0xE)
						return 0;
					if (state[0].att[Black] & 0x1C)
						return 0;
				}
				return 1;
			}
		}
		else
		{
			if (IsCastling(piece, move))
			{
				if (u & 0x4000000000000000)
				{
					if (F(state[0].castle_flags & CanCastle_oo))
						return 0;
					if (occ & 0x6000000000000000)
						return 0;
					if (state[0].att[White] & 0x7000000000000000)
						return 0;
				}
				else
				{
					if (F(state[0].castle_flags & CanCastle_ooo))
						return 0;
					if (occ & 0x0E00000000000000)
						return 0;
					if (state[0].att[White] & 0x1C00000000000000)
						return 0;
				}
				return 1;
			}
		}
		if (F(KAtt[from] & u))
			return 0;
		if (state[0].att[opp] & u)
			return 0;
		return 1;
	}
	piece = (piece >> 1) - 2;
	if (piece == 0)
	{
		if (u & NAtt[from])
			return 1;
		else
			return 0;
	}
	else
	{
		if (piece <= 2)
		{
			if (BMask[from] & u)
				return 1;
		}
		else if (piece == 3)
		{
			if (RMask[from] & u)
				return 1;
		}
		else
			return 1;
		return 0;
	}
}
INLINE bool is_legal(const State_& state, int move)
{
	return state.current_->turn ? is_legal<1>(state, move) : is_legal<0>(state, move);
}

template<bool me> bool is_check(const State_& state, int move)
{  // doesn't detect castling and ep checks
	const Board_& board = state();

	int from = From(move), to = To(move);
	uint64 king = board.King(opp);
	int king_sq = lsb(king), piece = board.PieceAt(from);
	if (HasBit(state[0].xray[me], from) && !HasBit(FullLine[king_sq][from], to))
		return true;
	if (piece < WhiteKnight)
	{
		if (PAtt[me][to] & king)
			return true;
		if (HasBit(OwnLine<me>(7), to) && T(king & OwnLine<me>(7)) && F(Between[to][king_sq] & board.PieceAll()))
			return true;
	}
	else if (piece < WhiteLight)
	{
		if (NAtt[to] & king)
			return true;
	}
	else if (piece < WhiteRook)
	{
		if (BMask[to] & king)
			if (F(Between[king_sq][to] & board.PieceAll()))
				return true;
	}
	else if (piece < WhiteQueen)
	{
		if (RMask[to] & king)
			if (F(Between[king_sq][to] & board.PieceAll()))
				return true;
	}
	else if (piece < WhiteKing)
	{
		if (QMask[to] & king)
			if (F(Between[king_sq][to] & board.PieceAll()))
				return true;
	}
	return false;
}

template<bool me> bool draw_in_pv(State_* state)
{
	if (state->Height() >= MAX_HEIGHT - 2)
		return true;
	if (state->current_->ply >= 100)
		return true;
	for (int i = 4; i <= state->current_->ply; i += 2)
		if (state->hashHist_[state->hashHist_.size() - 1 - i] == state->current_->key)
			return true;
	if (GPVEntry* PVEntry = probe_pv_hash(*state->current_))
	{
		if (!PVEntry->value)
			return true;
		if (int move = PVEntry->move)
		{
			do_move<me>(state, move);
			bool value = draw_in_pv<opp>(state);
			undo_move<me>(state, move);
			return value;
		}
	}
	return false;
}

INLINE int HashMerit(int date, uint8 depth)
{
	return 7 * date + depth;
}
inline int HashMerit(const GEntry& entry)
{
	return HashMerit(entry.date, Max<int>(entry.high_depth, entry.low_depth));
}
INLINE int HashMerit(const GPVEntry& entry)
{
	return HashMerit(entry.date, entry.depth);
}

void hash_high_update(GEntry* Entry, int value, int depth)
{
	Entry->date = TheShare.date_;
	if (depth > Entry->high_depth || (depth == Entry->high_depth && value < Entry->high))
	{
		if (Entry->low <= value)
		{
			Entry->high_depth = depth;
			Entry->high = value;
		}
		else if (Entry->low_depth < depth)
		{
			Entry->high_depth = depth;
			Entry->high = value;
			Entry->low = value;
			Entry->low_depth = Entry->high_depth > 8 ? Min<uint8>(Entry->high_depth - 8, Entry->low_depth) : 0;
			Entry->move = 0;
		}
	}
}

void hash_high(const PlyState_& current, int value, int depth, bool force_update)
{
	int i;
	GEntry* best, *Entry;

	// search for an old entry to overwrite
	int minMerit = force_update ? 0x700000 : HashMerit(TheShare.date_, depth);
	for (i = 0, best = Entry = HashStart(current.key); i < HASH_CLUSTER; ++i, ++Entry)
	{
		if (Entry->key == Low32(current.key))
		{
			hash_high_update(Entry, value, depth);
			return;
		}
		int merit = HashMerit(*Entry);
		if (merit < minMerit)
		{
			minMerit = merit;
			best = Entry;
		}
	}
	best->date = TheShare.date_;
	best->key = Low32(current.key);
	best->high = value;
	best->high_depth = depth;
	best->low = 0;
	best->low_depth = 0;
	best->move = 0;
	return;
}

// POSTPONED -- can hash_low return something more useful than its input?
int hash_low_update(GEntry* Entry, int move, int value, int depth)
{
	Entry->date = TheShare.date_;
	if (depth > Entry->low_depth || (depth == Entry->low_depth && value > Entry->low))
	{
		if (move)
			Entry->move = move;
		if (Entry->high >= value)
		{
			Entry->low_depth = depth;
			Entry->low = value;
		}
		else if (Entry->high_depth < depth)
		{
			Entry->low_depth = depth;
			Entry->low = value;
			Entry->high = value;
			Entry->high_depth = depth > 8 ? Min<uint8>(depth - 8, Entry->high_depth) : 0;
		}
	}
	else if (F(Entry->move))
		Entry->move = move;
	return value;
}

int hash_low(const PlyState_& current, int move, int value, int depth, bool force_update)
{
	int i;
	GEntry* best, *Entry;

	int minMerit = force_update ? 0x700000 : HashMerit(TheShare.date_, depth);
	move &= 0xFFFF;
	for (i = 0, best = Entry = HashStart(current.key); i < HASH_CLUSTER; ++i, ++Entry)
	{
		if (Entry->key == Low32(current.key))
			return hash_low_update(Entry, move, value, depth);
		int merit = HashMerit(*Entry);
		if (merit < minMerit)
		{
			minMerit = merit;
			best = Entry;
		}
	}
	best->date = TheShare.date_;
	best->key = Low32(current.key);
	best->high = 0;
	best->high_depth = 0;
	best->low = value;
	best->low_depth = depth;
	best->move = move;
	return value;
}

void hash_exact(const PlyState_& current, int move, int value, int depth, int exclusion, int ex_depth, int knodes)
{
	GPVEntry* best;
	GPVEntry* PVEntry;
	int i;

	int minMerit = 0x70000000;
	for (i = 0, best = PVEntry = &ThePVHash[High32(current.key) & PV_HASH_MASK]; i < PV_CLUSTER; ++i, ++PVEntry)
	{
		if (PVEntry->key == Low32(current.key))
		{
			PVEntry->date = TheShare.date_;
			PVEntry->knodes += knodes;
			if (PVEntry->depth <= depth)
			{
				PVEntry->value = value;
				PVEntry->depth = depth;
				PVEntry->move = move;
				PVEntry->ply = current.ply;
				if (ex_depth)
				{
					PVEntry->exclusion = exclusion;
					PVEntry->ex_depth = ex_depth;
				}
			}
			return;
		}
		int merit = HashMerit(*PVEntry);
		if (merit < minMerit)
		{
			minMerit = merit;
			best = PVEntry;
		}
	}
	best->key = Low32(current.key);
	best->date = TheShare.date_;
	best->value = value;
	best->depth = depth;
	best->move = move;
	best->exclusion = exclusion;
	best->ex_depth = ex_depth;
	best->knodes = knodes;
	best->ply = current.ply;
}

template<bool me, bool pv> INLINE int extension(const PlyState_& current, int move, int depth)
{
	int from = From(move);
	if (HasBit(current.passer, from))
	{
		int rank = OwnRank(me, from);
		if (rank >= 5 && depth < 16)
			return T(pv) + T(rank < 6 || depth < 10);
	}
	return 0;
}

template<bool me, bool pv> INLINE int check_extension(int move, int depth)
{
	return pv ? 2 : T(depth < 14) + T(depth < 28);
}

void sort(int* start, int* finish)
{
	for (int* p = start; p < finish - 1; ++p)
	{
		int* best = p;
		int value = *p;
		int previous = *p;
		for (int* q = p + 1; q < finish; ++q)
			if ((*q) > value)
			{
				value = *q;
				best = q;
			}
		*best = previous;
		*p = value;
	}
}

template<class I> void sort_moves(I start, I finish)
{
	auto better = [](int lhs, int rhs) { return (lhs >> 16) > (rhs >> 16); };
	stable_sort(start, finish, better);
}

inline int pick_move(PlyState_* current)
{
	int* best = current->current;
	if (F(*best))
		return 0;
	for (int* p = current->current + 1; T(*p); ++p)
	{
		if (*p > *best)
			best = p;
	}
	std::swap(*best, *current->current);
	return *(current->current++) & 0xFFFF;
}

INLINE void apply_wobble(void* p, int* move, int depth)
{
	int mp = (((*move & 0xFFFF) * 529) >> 9) & 1;
	*move += (mp + depth + (static_cast<int>(reinterpret_cast<sint64>(p) >> 12))) % (SETTINGS.wobble + 1);	// (minimal) bonus for right parity
}

INLINE bool is_killer(const PlyState_& current, uint16 move)
{
	for (int ik = 1; ik <= N_KILLER; ++ik)
		if (move == current.killer[ik])
			return true;
	return false;
}

void mark_evasions(int* list, State_* state)
{
	for (; T(*list); ++list)
	{
		int move = (*list) & 0xFFFF;
		auto& current = (*state)[0];
		if (F(state->board_.PieceAt(To(move))) && F(move & 0xE000))
		{
			if (move == current.ref[0])
				*list |= RefOneScore;
			else if (move == current.ref[1])
				*list |= RefTwoScore;
			else if (find(current.killer.begin() + 1, current.killer.end(), move) != current.killer.end())
			{
				int ik = static_cast<int>(find(current.killer.begin() + 1, current.killer.end(), move) - current.killer.begin());
				*list |= (0xFF >> Max(0, ik - 2)) << 16;
				if (ik == 1)
					*list |= 1 << 24;
			}
			else
				*list |= HistoryP(state, JoinFlag(move), state->board_.PieceAt(From(move)), From(move), To(move));
		}
	}
}

template<bool me> inline bool IsGoodCap(const State_& state, int move)
{
	return (HasBit(state[0].xray[me], From(move)) && !HasBit(FullLine[lsb(state().King(opp))][From(move)], To(move)))
			|| see<me>(state, move, 0);
}


template<bool me> void gen_next_moves(State_* state, int depth)
{
	PlyState_* current = state->current_;
	const Board_& board = state->board_;

	int* p, *q, *r;
	current->gen_flags &= ~FlagSort;
	switch (current->stage)
	{
	case s_hash_move:
	case r_hash_move:
	case e_hash_move:
		current->moves[0] = current->killer[0];
		current->moves[1] = 0;
		return;
	case s_good_cap:
	{
		current->mask = board.Piece(opp);
		r = gen_captures<me>(current->moves, *state);
		for (q = r - 1, p = current->moves; q >= p;)
		{
			int move = (*q) & 0xFFFF;
			if (!IsGoodCap<me>(*state, move))
			{
				int next = *p;
				*p = *q;
				*q = next;
				++p;
			}
			else
				--q;
		}
		current->start = p;
		current->current = p;
		sort(p, r);
	}
	return;
	case s_special:
		current->current = current->start;
		p = current->start;
		for (int ik = 1; ik <= N_KILLER; ++ik)
			if (T(current->killer[ik]))
				*p++ = current->killer[ik];
		if (current->ref[0] && !is_killer(*current, current->ref[0]))
			*p++ = current->ref[0];
		if (current->ref[1] && !is_killer(*current, current->ref[1]))
			*p++ = current->ref[1];
		*p = 0;
		return;
	case s_quiet:
		p = gen_quiet_moves<me>(current->start, state);
		current->gen_flags |= FlagSort;
		current->current = current->start;
		for (q = current->start; *q; ++q)
			apply_wobble(state, &*q, depth);
		return;
	case s_bad_cap:
		*(current->start) = 0;
		current->current = current->moves;
		if (!(current->gen_flags & FlagNoBcSort))
			sort(current->moves, current->start);
		return;
	case r_cap:
		r = gen_captures<me>(current->moves, *state);
		current->current = current->moves;
		sort(current->moves, r);
		return;
	case r_checks:
		r = gen_checks<me>(current->moves, *state);
		current->current = current->moves;
		sort(current->moves, r);
		return;
	case e_ev:
		current->mask = Filled;
		r = gen_evasions<me>(current->moves, *state);
		mark_evasions(current->moves, state);
		sort(current->moves, r);
		current->current = current->moves;
		return;
	}
}

template<bool me> int NextMove(State_* state, int depth)
{
	constexpr int StageNone = (1 << s_none) | (1 << e_none) | (1 << r_none);

	PlyState_* current = state->current_;
	int move;

	for ( ; ; )
	{
		if (F(*current->current))
		{
			current->stage++;
			if ((1 << current->stage) & StageNone)
				return 0;
			gen_next_moves<me>(state, depth);
			continue;
		}
		if (current->gen_flags & FlagSort)
			move = pick_move(current);
		else
		{
			move = (*current->current) & 0xFFFF;
			current->current++;
		}

		if (current->stage == s_quiet)
		{
			if (!is_killer(*current, move) && move != current->ref[0] && move != current->ref[1])
				return move;
		}
		else if (current->stage == s_special)
		{
			if (!state->board_.PieceAt(To(move)) && is_legal<me>(*state, move))
				return move;
		}
		else
			return move;
	}
}

template<bool me> bool see(const State_& state, int move, int margin)
{
	const Board_& board = state.board_;
	int from = From(move), to = To(move);
	int piece = SeeValue[board.PieceAt(from)], capture = SeeValue[board.PieceAt(to)];
	int cost = piece - capture + margin;
	if (cost <= 0)
		return 1;
	if (piece == SeeValue[WhiteKing])
		return 1;
	if (HasBit(state[0].xray[me], from))
		return 1;
	if (piece > (SeeValue[WhiteKing] >> 1))
		return 1;
	if (IsEP(move))
		return 1;
	if (!HasBit(state[0].att[opp], to))
		return 1;
	uint64 oppAtt = PAtt[me][to] & board.Pawn(opp);
	if (T(oppAtt) && cost > SeeValue[WhitePawn])
		return 0;
	uint64 occ = board.PieceAll() & ~Bit(from);	// occupancy after the initial capture
	uint64 myAtt = PAtt[opp][to] & board.Pawn(me) & occ;
	if (T(myAtt) && cost + SeeValue[WhitePawn] <= 0)
		return 1;
	oppAtt |= NAtt[to] & board.Knight(opp);
	if (T(oppAtt) && cost > SeeValue[WhiteDark])
		return 0;
	uint64 b_area = BishopAttacks(to, occ);
	uint64 opp_bishop = board.Bishop(opp);
	if (cost > SeeValue[IDark[me]])
		if (b_area & opp_bishop)
			return 0;
	uint64 my_bishop = board.Bishop(me);
	uint64 oppSliderB = BMask[to] & (opp_bishop | board.Queen(opp));
	uint64 oppSliderR = RMask[to] & board.Major(opp);
	uint64 mySliderB = BMask[to] & (my_bishop | board.Queen(me)) & occ;
	uint64 mySliderR = RMask[to] & board.Major(me) & occ;
	oppAtt |= (oppSliderB & b_area);
	myAtt |= NAtt[to] & board.Knight(me) & occ;
	uint64 r_area = RookAttacks(to, occ);
	oppAtt |= (oppSliderR & r_area);
	myAtt |= (mySliderB & b_area);
	myAtt |= (mySliderR & r_area);
	oppAtt |= KAtt[to] & board.King(opp);
	myAtt |= KAtt[to] & board.King(me);	// by now we know the initial capturer wasn't a king
	while (true)
	{
		if (uint64 u = (oppAtt & board.Pawn(opp)))
		{
			capture -= piece;
			piece = SeeValue[WhitePawn];
			int sq = lsb(u);
			occ ^= Bit(sq);
			oppAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & oppSliderB & (occ ^ oppAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					oppAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (oppAtt & board.Knight(opp)))
		{
			capture -= piece;
			piece = SeeValue[WhiteKnight];
			oppAtt ^= (~(u - 1)) & u;
		}
		else if (uint64 u = (oppAtt & opp_bishop))
		{
			capture -= piece;
			piece = SeeValue[WhiteDark];
			int sq = lsb(u);
			occ ^= Bit(sq);
			oppAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & oppSliderB & (occ ^ oppAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					oppAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (oppAtt & board.Rook(opp)))
		{
			capture -= piece;
			piece = SeeValue[WhiteRook];
			int sq = lsb(u);
			occ ^= Bit(sq);
			oppAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & oppSliderR & (occ ^ oppAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					oppAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (oppAtt & board.Queen(opp)))
		{
			capture -= piece;
			piece = SeeValue[WhiteQueen];
			int sq = lsb(u);
			occ ^= Bit(sq);
			oppAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & (oppSliderR | oppSliderB) & (occ ^ oppAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					oppAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (oppAtt & board.King(opp)))
		{
			capture -= piece;
			piece = SeeValue[WhiteKing];
		}
		else
			return 1;
		if (capture < -(SeeValue[WhiteKing] >> 1))
			return 0;
		if (piece + capture < margin)
			return 0;
		if (uint64 u = (myAtt & board.Pawn(me)))
		{
			capture += piece;
			piece = SeeValue[WhitePawn];
			int sq = lsb(u);
			occ ^= Bit(sq);
			myAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & mySliderB & (occ ^ myAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					myAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (myAtt & board.Knight(me)))
		{
			capture += piece;
			piece = SeeValue[WhiteKnight];
			myAtt ^= (~(u - 1)) & u;
		}
		else if (uint64 u = (myAtt & my_bishop))
		{
			capture += piece;
			piece = SeeValue[WhiteDark];
			int sq = lsb(u);
			occ ^= Bit(sq);
			myAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & mySliderB & (occ ^ myAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					myAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (myAtt & board.Rook(me)))
		{
			capture += piece;
			piece = SeeValue[WhiteRook];
			int sq = lsb(u);
			occ ^= Bit(sq);
			myAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & mySliderR & (occ ^ myAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					myAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (myAtt & board.Queen(me)))
		{
			capture += piece;
			piece = SeeValue[WhiteQueen];
			int sq = lsb(u);
			occ ^= Bit(sq);
			myAtt ^= Bit(sq);
			for (uint64 new_att = FullLine[to][sq] & (mySliderR | mySliderB) & (occ ^ myAtt); T(new_att); Cut(new_att))
			{
				int pos = lsb(new_att);
				if (F(Between[to][pos] & occ))
				{
					myAtt |= Bit(pos);
					break;
				}
			}
		}
		else if (uint64 u = (myAtt & board.King(me)))
		{
			capture += piece;
			piece = SeeValue[WhiteKing];
		}
		else
			return 0;
		if (capture > (SeeValue[WhiteKing] >> 1))
			return 1;
		if (capture - piece >= margin)
			return 1;
	}
}

template<bool me> void gen_root_moves(State_* state)
{
	evaluate(state);	// populate attacks etc

	PlyState_& current = *state->current_;
	const Board_& board = state->board_;
	int depth = -16;

	int killer = 0;
	if (GEntry* Entry = probe_hash(current))
	{
		if (T(Entry->move) && Entry->low_depth > depth)
		{
			depth = Entry->low_depth;
			killer = Entry->move;
		}
	}
	if (GPVEntry* PVEntry = probe_pv_hash(current))
	{
		if (PVEntry->depth > depth && T(PVEntry->move))
		{
			depth = PVEntry->depth;
			killer = PVEntry->move;
		}
	}

	current.killer[0] = killer;
	if (IsCheck(*state, me))
		current.stage = stage_evasion;
	else
	{
		current.stage = stage_search;
		current.ref = Refutations<me, false>(*state);
	}
	current.gen_flags = 0;
	RootList.clear();
	current.current = &current.moves[0];
	current.moves[0] = 0;
	while (int move = NextMove<me>(state, 0))
	{
		if (IsIllegal(*state, move))
			continue;
		if (find(RootList.begin(), RootList.end(), move) != RootList.end())
			continue;	// most like re-trying killer move
		RootList.push_back(move);
	}
}

template<bool me> INLINE bool forkable(const Board_& board, int dst)
{
	if (NAttAtt[dst] & board.King(me))
	{
		for (uint64 nn = board.Knight(opp) & NAttAtt[dst]; nn; Cut(nn))
		{
			if (T(NAtt[dst] & NAtt[lsb(nn)] & NAtt[lsb(board.King(me))]))
				return true;
		}
	}
	return false;
}

template<class T_> T_* NullTerminate(T_* list)
{
	*list = 0;
	return list;
}

template<bool me> int* gen_captures(int* list, const State_& state)
{
	static const int MvvLvaPromotion = MvvLva[WhiteQueen][BlackQueen];
	static const int MvvLvaPromotionKnight = MvvLva[WhiteKnight][BlackKnight];
	static const int MvvLvaPromotionBad = MvvLva[WhiteKnight][BlackPawn];

	const Board_& board = state.board_;
	uint64 u, v;
	int kMe = lsb(board.King(me)), kOpp = lsb(board.King(opp));
	auto bonus = [&](int to)
	{
		if (!HasBit(state[0].att[opp], to))
			return 2 << 26;
		return T(HasBit(state[0].dbl_att[me] & ~state[0].dbl_att[opp], to)) << 26;
	};
	if (state[0].ep_square)
		for (v = PAtt[opp][state[0].ep_square] & board.Pawn(me); T(v); Cut(v))
			list = AddMove(list, lsb(v), state[0].ep_square, FlagEP, MvvLva[IPawn[me]][IPawn[opp]] + bonus(lsb(v)));
	for (u = board.Pawn(me) & OwnLine<me>(6); T(u); Cut(u))
		if (F(board.PieceAt(lsb(u) + Push[me])))
		{
			int from = lsb(u), to = from + Push[me];
			list = AddMove(list, from, to, FlagPQueen, MvvLvaPromotion);
			if (T(NAtt[to] & board.King(opp)) || forkable<me>(board, to))	// Roc v Hannibal, 64th amateur series A round 2, proved the need for this second test
				list = AddMove(list, from, to, FlagPKnight, MvvLvaPromotionKnight);
		}
	for (v = ShiftW<opp>(state[0].mask) & board.Pawn(me) & OwnLine<me>(6); T(v); Cut(v))
	{
		int from = lsb(v), to = from + PushE[me];
		list = AddMove(list, from, to, FlagPQueen, MvvLvaPromotionCap[board.PieceAt(to)] + bonus(to));
		if (HasBit(NAtt[kOpp], to))
			list = AddMove(list, from, to, FlagPKnight, MvvLvaPromotionKnightCap[board.PieceAt(to)] + bonus(to));
	}
	for (v = ShiftE<opp>(state[0].mask) & board.Pawn(me) & OwnLine<me>(6); T(v); Cut(v))
	{
		int from = lsb(v), to = from + PushW[me];
		list = AddMove(list, from, to, FlagPQueen, MvvLvaPromotionCap[board.PieceAt(to)] + bonus(to));
		if (HasBit(NAtt[kOpp], to))
			list = AddMove(list, from, to, FlagPKnight, MvvLvaPromotionKnightCap[board.PieceAt(to)] + bonus(to));
	}
	if (T(state[0].att[me] & state[0].mask))
	{
		for (v = ShiftW<opp>(state[0].mask) & board.Pawn(me) & (~OwnLine<me>(6)); T(v); Cut(v))
			list = AddCaptureP(list, board, IPawn[me], lsb(v), lsb(v) + PushE[me], 0);
		for (v = ShiftE<opp>(state[0].mask) & board.Pawn(me) & (~OwnLine<me>(6)); T(v); Cut(v))
			list = AddCaptureP(list, board, IPawn[me], lsb(v), lsb(v) + PushW[me], 0);
		for (v = KAtt[lsb(board.King(me))] & state[0].mask & (~state[0].att[opp]); T(v); Cut(v))
			list = AddCaptureP(list, board, IKing[me], lsb(board.King(me)), lsb(v), 0);
		for (u = board.Knight(me); T(u); Cut(u))
			for (v = NAtt[lsb(u)] & state[0].mask; T(v); Cut(v))
				list = AddCaptureP(list, board, IKnight[me], lsb(u), lsb(v));
		for (u = board.Bishop(me); T(u); Cut(u))
			for (v = BishopAttacks(lsb(u), board.PieceAll()) & state[0].mask; T(v); Cut(v))
				list = AddCapture(list, board, lsb(u), lsb(v));
		for (u = board.Rook(me); T(u); Cut(u))
			for (v = RookAttacks(lsb(u), board.PieceAll()) & state[0].mask; T(v); Cut(v))
				list = AddCaptureP(list, board, IRook[me], lsb(u), lsb(v));
		for (u = board.Queen(me); T(u); Cut(u))
			for (v = QueenAttacks(lsb(u), board.PieceAll()) & state[0].mask; T(v); Cut(v))
				list = AddCaptureP(list, board, IQueen[me], lsb(u), lsb(v));
	}
	return NullTerminate(list);
}

template<bool me> int* gen_evasions(int* list, const State_& state)
{
	static const int MvvLvaPromotion = MvvLva[WhiteQueen][BlackQueen];

	const Board_& board = state.board_;
	uint64 b, u;
	//	pair<uint64, uint64> pJoins = pawn_joins(me, Pawn(me));

	int king = lsb(board.King(me));
	uint64 att = (NAtt[king] & board.Knight(opp)) | (PAtt[me][king] & board.Pawn(opp));
	for (u = (BMask[king] & (board.Bishop(opp) | board.Queen(opp))) | (RMask[king] & (board.Rook(opp) | board.Queen(opp))); T(u); u ^= b)
	{
		b = Bit(lsb(u));
		if (F(Between[king][lsb(u)] & board.PieceAll()))
			att |= b;
	}
	int att_sq = lsb(att);  // generally the only attacker
	uint64 esc = KAtt[king] & (~(board.Piece(me) | state[0].att[opp])) & state[0].mask;
	if (board.PieceAt(att_sq) >= WhiteLight)
		esc &= ~FullLine[king][att_sq];
	else if (board.PieceAt(att_sq) >= WhiteKnight)
		esc &= ~NAtt[att_sq];

	Cut(att);
	if (att)
	{  // second attacker (double check)
		att_sq = lsb(att);
		if (board.PieceAt(att_sq) >= WhiteLight)
			esc &= ~FullLine[king][att_sq];
		else if (board.PieceAt(att_sq) >= WhiteKnight)
			esc &= ~NAtt[att_sq];

		for (; T(esc); Cut(esc))
			list = AddCaptureP(list, board, IKing[me], king, lsb(esc), 0);
		return NullTerminate(list);
	}

	// not double check
	if (T(state[0].ep_square) && state[0].ep_square == att_sq + Push[me] && HasBit(state[0].mask, att_sq))
	{
		for (u = PAtt[opp][state[0].ep_square] & board.Pawn(me); T(u); Cut(u))
			list = AddMove(list, lsb(u), att_sq + Push[me], FlagEP, MvvLva[IPawn[me]][IPawn[opp]]);
	}
	for (u = PAtt[opp][att_sq] & board.Pawn(me); T(u); Cut(u))
	{
		int from = lsb(u);
		if (HasBit(OwnLine<me>(7), att_sq))
			list = AddMove(list, from, att_sq, FlagPQueen, MvvLvaPromotionCap[board.PieceAt(att_sq)]);
		else if (HasBit(state[0].mask, att_sq))
			list = AddCaptureP(list, board, IPawn[me], from, att_sq, 0);
	}
	for (; T(esc); Cut(esc))
		list = AddCaptureP(list, board, IKing[me], king, lsb(esc), 0);
	// now check interpositions
	uint64 inter = Between[king][att_sq];
	for (u = Shift<opp>(inter) & board.Pawn(me); T(u); Cut(u))
	{
		int from = lsb(u);
		if (HasBit(OwnLine<me>(6), from))
			list = AddMove(list, from, from + Push[me], FlagPQueen, MvvLvaPromotion);
		else if (F(~state[0].mask))
			list = AddMove(list, from, from + Push[me], 0, 0);
	}

	if (F(state[0].mask))
		return NullTerminate(list);

	if (F(~state[0].mask))
	{
		for (u = Shift<opp>(Shift<opp>(inter)) & OwnLine<me>(1) & board.Pawn(me); T(u); Cut(u))
		{
			int from = lsb(u);
			if (F(board.PieceAt(from + Push[me])))
			{
				int to = from + 2 * Push[me];
				list = AddMove(list, from, to, 0, 0);
			}
		}
	}
	inter = (inter | Bit(att_sq)) & state[0].mask;
	for (u = board.Knight(me); T(u); Cut(u))
		for (esc = NAtt[lsb(u)] & inter; T(esc); Cut(esc))
			list = AddCaptureP(list, board, IKnight[me], lsb(u), lsb(esc), 0);
	for (u = board.Bishop(me); T(u); Cut(u))
		for (esc = BishopAttacks(lsb(u), board.PieceAll()) & inter; T(esc); Cut(esc))
			list = AddCapture(list, board, lsb(u), lsb(esc));
	for (u = board.Rook(me); T(u); Cut(u))
		for (esc = RookAttacks(lsb(u), board.PieceAll()) & inter; T(esc); Cut(esc))
			list = AddCaptureP(list, board, IRook[me], lsb(u), lsb(esc), 0);
	for (u = board.Queen(me); T(u); Cut(u))
		for (esc = QueenAttacks(lsb(u), board.PieceAll()) & inter; T(esc); Cut(esc))
			list = AddCaptureP(list, board, IQueen[me], lsb(u), lsb(esc), 0);
	return NullTerminate(list);
}
template<bool me> int* gen_evasions(State_* state)
{
	return gen_evasions<me>(state->current_->moves, *state);
}


template<bool me> INLINE uint64 PawnJoins(const PlyState_& current)
{
	auto threat = current.att[opp] & current.passer;
	return Shift<me>(current.passer) | ShiftW<opp>(threat) | ShiftE<opp>(threat);
}

INLINE bool can_castle(const PlyState_& current, const uint64& occ, bool me, bool kingside)
{
	if (me == White)
	{
		return kingside
			? T(current.castle_flags & CanCastle_OO) && F(occ & 0x60) && F(current.att[Black] & 0x70)
			: T(current.castle_flags & CanCastle_OOO) && F(occ & 0xE) && F(current.att[Black] & 0x1C);
	}
	else
	{
		return kingside
			? T(current.castle_flags & CanCastle_oo) && F(occ & 0x6000000000000000) && F(current.att[White] & 0x7000000000000000)
			: T(current.castle_flags & CanCastle_ooo) && F(occ & 0x0E00000000000000) && F(current.att[White] & 0x1C00000000000000);
	}
}

template<bool me> int* gen_quiet_moves(int* list, State_* state)
{
	auto drop = [&](int loc) { return HasBit(state->current_->att[opp] & ~state->current_->dbl_att[me], loc) ? FlagCastling : 0; };
	auto dropPawn = [&](int loc) { return HasBit(state->current_->att[opp] & ~state->current_->att[me], loc) ? FlagCastling : 0; };

	const Board_& board = state->board_;
	uint64 occ = board.PieceAll();
	if (can_castle(*state->current_, occ, me, true))
		list = AddHistoryP(state, list, WhiteKing | me, me ? 60 : 4, me ? 62 : 6, FlagCastling);
	if (can_castle(*state->current_, occ, me, false))
		list = AddHistoryP(state, list, WhiteKing | me, me ? 60 : 4, me ? 58 : 2, FlagCastling);

	uint64 u, v, free = ~occ;
	for (v = Shift<me>(board.Pawn(me)) & free & (~OwnLine<me>(7)); T(v); Cut(v))
	{
		int to = lsb(v);
		int passer = T(HasBit(state->current_->passer, to - Push[me]));
		if (HasBit(OwnLine<me>(2), to) && F(board.PieceAt(to + Push[me])))
			list = AddHistoryP(state, list, IPawn[me], to - Push[me], to + Push[me], dropPawn(to + Push[me]));
		list = AddHistoryP(state, list, IPawn[me], to - Push[me], to, dropPawn(to), Square(OwnRank<me>(to) + 4 * passer - 2));
	}

	for (u = board.Knight(me); T(u); Cut(u))
	{
		int from = lsb(u);
		for (v = free & NAtt[from]; T(v); Cut(v))
		{
			int to = lsb(v);
			// int floor = T(NAtt[to] & Major(opp));
			list = AddHistoryP(state, list, IKnight[me], from, to, drop(to));
		}
	}

	for (u = board.Bishop(me); T(u); Cut(u))
	{
		int from = lsb(u);
		int which = HasBit(LightArea, from) ? ILight[me] : IDark[me];
		for (v = free & BishopAttacks(from, occ); T(v); Cut(v))
		{
			int to = lsb(v);
			list = AddHistoryP(state, list, which, from, to, drop(to));
		}
	}

	for (u = board.Rook(me); T(u); Cut(u))
	{
		int from = lsb(u);
		for (v = free & RookAttacks(from, occ); T(v); Cut(v))
		{
			int to = lsb(v);
			list = AddHistoryP(state, list, IRook[me], from, to, drop(to));
		}
	}
	for (u = board.Queen(me); T(u); Cut(u))
	{
		//uint64 qTarget = NAtt[lsb(King(opp))];	// try to get next to this
		int from = lsb(u);
		for (v = free & QueenAttacks(from, occ); T(v); Cut(v))
		{
			int to = lsb(v);
			list = AddHistoryP(state, list, IQueen[me], from, to, drop(to));	// KAtt[to] & qTarget ? FlagCastling : 0);
		}
	}
	int kLoc = lsb(board.King(me));
	auto xray = [&](int loc) { return T(state->current_->xray[opp]) && F(state->current_->xray[opp] & FullLine[kLoc][loc]) ? FlagCastling : 0; };
	for (v = KAtt[kLoc] & free & (~state->current_->att[opp]); T(v); Cut(v))
	{
		int to = lsb(v);
		list = AddHistoryP(state, list, IKing[me], kLoc, to, xray(to));
	}

	return NullTerminate(list);
}

template<bool me> int* gen_checks(int* list, const State_& state)
{
	static const int MvvLvaXray = MvvLva[WhiteQueen][WhitePawn];

	const Board_& board = state.board_;
	uint64 u, v, target;

	uint64 clear = ~(board.Piece(me) | state[0].mask), occ = board.PieceAll();
	int king = lsb(board.King(opp));
	// discovered checks
	for (u = state[0].xray[me] & board.Piece(me); T(u); Cut(u))
	{
		int from = lsb(u);
		target = clear & (~FullLine[king][from]);
		if (auto piece = board.PieceAt(from); piece == IPawn[me])
		{
			if (OwnRank<me>(from) < 6)
			{
				if (HasBit(target, from + Push[me]) && F(board.PieceAt(from + Push[me])))
				{
					// double push
					const int to2 = from + 2 * Push[me];
					if (OwnRank<me>(from) == 1 && HasBit(target, to2) && F(board.PieceAt(to2)))
						list = AddMove(list, from, to2, 0, MvvLvaXray);
					// single push
					list = AddMove(list, from, from + Push[me], 0, MvvLvaXray);
				}

				for (v = PAtt[me][from] & target & board.Piece(opp); T(v); Cut(v))
					list = AddMove(list, from, lsb(v), 0, MvvLvaXrayCap(board.PieceAt(lsb(v))));
			}
		}
		else
		{
			if (piece < WhiteLight)
				v = NAtt[from] & target;
			else if (piece < WhiteRook)
				v = BishopAttacks(from, occ) & target;
			else if (piece < WhiteQueen)
				v = RookAttacks(from, occ) & target;
			else if (piece < WhiteKing)
				v = QueenAttacks(from, occ) & target;
			else
				v = KAtt[from] & target & (~state[0].att[opp]);
			for (; T(v); Cut(v))
				list = AddMove(list, from, lsb(v), 0, MvvLvaXrayCap(board.PieceAt(lsb(v))));
		}
	}

	const uint64 nonDiscover = ~(state[0].xray[me] & board.Piece(me));  // exclude pieces already checked
	for (u = board.Knight(me) & NAttAtt[king] & nonDiscover; T(u); Cut(u))
		for (v = NAtt[king] & NAtt[lsb(u)] & clear; T(v); Cut(v))
			list = AddCaptureP(list, board, IKnight[me], lsb(u), lsb(v), 0);

	if (int kr = OwnRank<me>(king); kr > 2)
	{
		for (u = KAttAtt[king] & board.Pawn(me) & OwnLine<me>(kr - 2) & nonDiscover; T(u); Cut(u))
		{
			int from = lsb(u);
			for (v = PAtt[me][from] & PAtt[opp][king] & clear & board.Piece(opp); T(v); Cut(v))
				list = AddCaptureP(list, board, IPawn[me], from, lsb(v), 0);
			if (F(board.PieceAt(from + Push[me])) && HasBit(PAtt[opp][king] & clear, from + Push[me]))
				list = AddMove(list, from, from + Push[me], 0, 0);
		}
		if (kr == 4)
		{
			for (u = Shift<opp>(Shift<opp>(PAtt[opp][king] & clear)) & board.Pawn(me); T(u); Cut(u))
			{
				int from = lsb(u);
				if (int to = from + 2 * Push[me]; F(board.PieceAt(to)) && F(board.PieceAt(from + Push[me])))
					list = AddMove(list, from, to, 0, 0);
			}
		}
	}

	uint64 b_target = BishopAttacks(king, occ) & clear;
	uint64 r_target = RookAttacks(king, occ) & clear;
	for (u = board.Piece((T(board.King(opp) & LightArea) ? WhiteLight : WhiteDark) | me) & nonDiscover; T(u); Cut(u))
		for (v = BishopAttacks(lsb(u), occ) & b_target; T(v); Cut(v))
			list = AddCapture(list, board, lsb(u), lsb(v));
	for (u = board.Rook(me) & nonDiscover; T(u); Cut(u))
		for (v = RookAttacks(lsb(u), occ) & r_target; T(v); Cut(v))
			list = AddCaptureP(list, board, IRook[me], lsb(u), lsb(v), 0);
	for (u = board.Queen(me) & nonDiscover; T(u); Cut(u))
	{
		uint64 contact = KAtt[king];
		int from = lsb(u);
		for (v = QueenAttacks(from, occ) & (b_target | r_target); T(v); Cut(v))
		{
			int to = lsb(v);
			if (HasBit(contact, to))
				list = AddCaptureP(list, board, IQueen[me], from, to, T(Boundary & board.King(opp)) || OwnRank<me>(to) == 7 ? IPawn[opp] : IRook[opp]);
			else
				list = AddCaptureP(list, board, IQueen[me], from, to);
		}
	}

	if (OwnRank<me>(king) == 4)
	{	  // check for double-push checks	
		for (u = board.Pawn(me) & OwnLine<me>(1) & nonDiscover & PAtt[opp][king - 2 * Push[me]]; T(u); Cut(u))
		{
			int from = lsb(u);
			int to = from + 2 * Push[me];
			if (F(board.PieceAt(from + Push[me])) && F(board.PieceAt(to)))
				list = AddMove(list, from, to, 0, 0);
		}
	}
	return NullTerminate(list);
}

template<bool me> int* gen_delta_moves(int* list, State_* state, int margin)
{
	const Board_& board = state->board_;
	const PlyState_& current = *state->current_;
	uint64 occ = board.PieceAll(), free = ~occ;

	if (me == White)
	{
		if (can_castle(current, occ, me, true))
			list = AddCDeltaP(state, list, margin, WhiteKing, 4, 6, FlagCastling);
		if (can_castle(current, occ, me, false))
			list = AddCDeltaP(state, list, margin, WhiteKing, 4, 2, FlagCastling);
	}
	else
	{
		if (can_castle(current, occ, me, true))
			list = AddCDeltaP(state, list, margin, BlackKing, 60, 62, FlagCastling);
		if (can_castle(current, occ, me, false))
			list = AddCDeltaP(state, list, margin, BlackKing, 60, 58, FlagCastling);
	}
	for (uint64 v = Shift<me>(board.Pawn(me)) & free & (~OwnLine<me>(7)); T(v); Cut(v))
	{
		int to = lsb(v);
		if (HasBit(OwnLine<me>(2), to) && F(board.PieceAt(to + Push[me])))
			list = AddCDeltaP(state, list, margin, IPawn[me], to - Push[me], to + Push[me], 0);
		list = AddCDeltaP(state, list, margin, IPawn[me], to - Push[me], to, 0);
	}
	for (uint64 u = board.Knight(me); T(u); Cut(u))
	{
		int from = lsb(u);
		for (uint64 v = free & NAtt[lsb(u)]; T(v); Cut(v))
			list = AddCDeltaP(state, list, margin, IKnight[me], from, lsb(v), 0);
	}
	for (uint64 u = board.Piece(WhiteLight | me); T(u); Cut(u))
	{
		int from = lsb(u);
		for (uint64 v = free & BishopAttacks(lsb(u), occ); T(v); Cut(v))
			list = AddCDeltaP(state, list, margin, ILight[me], from, lsb(v), 0);
	}
	for (uint64 u = board.Piece(WhiteDark | me); T(u); Cut(u))
	{
		int from = lsb(u);
		for (uint64 v = free & BishopAttacks(lsb(u), occ); T(v); Cut(v))
			list = AddCDeltaP(state, list, margin, IDark[me], from, lsb(v), 0);
	}
	for (uint64 u = board.Rook(me); T(u); Cut(u))
	{
		int from = lsb(u);
		for (uint64 v = free & RookAttacks(lsb(u), occ); T(v); Cut(v))
			list = AddCDeltaP(state, list, margin, IRook[me], from, lsb(v), 0);
	}
	for (uint64 u = board.Queen(me); T(u); Cut(u))
	{
		int from = lsb(u);
		for (uint64 v = free & QueenAttacks(lsb(u), occ); T(v); Cut(v))
			list = AddCDeltaP(state, list, margin, IQueen[me], from, lsb(v), 0);
	}
	int from = lsb(board.King(me));
	for (uint64 v = KAtt[lsb(board.King(me))] & free & (~current.att[opp]); T(v); Cut(v))
		list = AddCDeltaP(state, list, margin, IKing[me], from, lsb(v), 0);
	return NullTerminate(list);
}

int time_to_stop(const SearchInfo_& SI, int time, int searching)
{
	if (time > TheTimeLimit.hardLimit_)
		return 1;
	if (searching)
		return 0;
	if (2 * time > TheTimeLimit.hardLimit_)
		return 1;
	if (TheShare.emaDepth_ > TheShare.depth_ + 2)
		return 0;
	if (time > TheTimeLimit.softLimit_)
		return 1;
	if (TheShare.firstMove_ || !SI.moves_.same() || SI.failLow_)
		return 0;
	if (time * 100 > TheTimeLimit.softLimit_ * TimeNoChangeMargin)
		return 1;
	if (SI.early_)
		return 0;
	if (time * 100 > TheTimeLimit.softLimit_ * TimeNoPVSCOMargin)
		return 1;
	if (SI.singular_ < 1)
		return 0;
	if (time * 100 > TheTimeLimit.softLimit_ * TimeSingOneMargin)
		return 1;
	if (SI.singular_ < 2)
		return 0;
	if (time * 100 > TheTimeLimit.softLimit_ * TimeSingTwoMargin)
		return 1;
	return 0;
}

template<bool me, bool exclusion, bool evasion> int scout(State_* state, int beta, int depth, int flags);

template<bool me> int singular_extension(State_* state, int ext, int prev_ext, int margin_one, int margin_two, int depth, int killer)
{
	int value = -MateValue;
	int singular = 0;
	if (ext < (prev_ext ? 1 : 2))
	{
		value = (IsCheck(*state, me) ? scout<me, 1, 1> : scout<me, 1, 0>)(state, margin_one, depth, killer);
		if (value < margin_one)
			singular = 1;
	}
	if (value < margin_one && ext < (prev_ext ? (prev_ext >= 2 ? 1 : 2) : 3))
	{
		value = (IsCheck(*state, me) ? scout<me, 1, 1> : scout<me, 1, 0>)(state, margin_two, depth, killer);
		if (value < margin_two)
			singular = 2;
	}
	return singular;
}

template<bool me> INLINE uint64 capture_margin_mask(const State_& state, int alpha, int* score)
{
	const Board_& board = state.board_;
	uint64 retval = board.Piece(opp);
	if (state[0].score + 200 * CP_SEARCH < alpha) {
		if (uint64 p = board.Pawn(opp);  state[0].att[me] & p) {
			retval ^= p;
			*score = state[0].score + 200 * CP_SEARCH;
		}
		if (state[0].score + 500 * CP_SEARCH < alpha) {
			if (uint64 m = board.Minor(opp); state[0].att[me] & m) {
				retval ^= m;
				*score = state[0].score + 500 * CP_SEARCH;
			}
			if (state[0].score + 700 * CP_SEARCH < alpha) {
				if (uint64 r = board.Rook(opp);  state[0].att[me] & r) {
					retval ^= r;
					*score = state[0].score + 700 * CP_SEARCH;
				}
				if (state[0].score + 1400 * CP_SEARCH < alpha) {
					if (uint64 q = board.Queen(opp); state[0].att[me] & q) {
						retval ^= q;
						*score = state[0].score + 1400 * CP_SEARCH;
					}
				}
			}
		}
	}
	return retval;
}

struct Abort_ : std::exception {};

inline void check_for_stop()
{
	if (TheShare.stopAll_)
		throw Abort_();
}
inline void stop()
{
	TheShare.stopAll_ = true;
}


#define HALT_CHECK(state) {\
    if (state->current_->ply >= 100) return 0; \
    for (int ihc = 4; ihc <= state->current_->ply; ihc += 2) if (state->hashHist_[state->hashHist_.size() - 1 - ihc] == state->current_->key) return 0; \
	if (state->Height() >= 126) {evaluate(state); return state->current_->score; }}

template<bool me> int QSearch(State_* state, int alpha, int beta, int depth, int flags)
{
	const Board_& board = state->board_;
	const PlyState_& current = *state->current_;
	int value, score, move, hash_move, hash_depth;
	auto finish = [&](int score, bool did_delta_moves)
	{
		if (depth >= -2 
			&& (depth >= 0 || state->current_->score + Futility::HashCut<me>(*state, did_delta_moves) >= alpha))
			hash_high(*state->current_, score, 1, false);
		return score;
	};

	check_for_stop();
	if (flags & FlagHaltCheck)
		HALT_CHECK(state);
#ifdef CPU_TIMING
#ifndef TIMING
	if (nodes > check_node + 0x4000)
	{
#else
	if (nodes > check_node + 0x100)
	{
#endif
		check_node = nodes;
#ifdef TIMING
		if (LastDepth >= 6)
#endif
			check_time(nullptr, 1);
	}
#endif
	if (flags & FlagCallEvaluation)
	{
		evaluate(state);
		if (current.score > beta)
			return current.score;
		state->selDepth_ = Max(state->selDepth_, state->Height());
	}
	if (IsCheck(*state, me))
		return q_evasion<me>(state, alpha, beta, depth, FlagHashCheck);

	int tempo = InitiativeConst;
	if (F(board.NonPawnKing(me) | (current.passer & board.Pawn(me) & Shift<opp>(current.patt[me] | ~current.att[opp]))))
		tempo = 0;
	else if (F(current.material & FlagUnusualMaterial) && current.material < TotalMat)
		tempo += (InitiativePhase * RO->material_[current.material].phase) / MAX_PHASE;
	score = current.score + tempo;
	if (score > alpha)
	{
		if (score >= beta)
			return score;
		alpha = score;
	}

	hash_move = hash_depth = 0;
	if (flags & FlagHashCheck)
	{
		if (GEntry* Entry = probe_hash(current))
		{
			if (T(Entry->high_depth) && Entry->high <= alpha)
				return Entry->high;
			if (T(Entry->low_depth))
			{
				if (Entry->low >= beta)
					return Entry->low;
				if (Entry->low_depth > hash_depth && T(Entry->move))
				{
					hash_move = Entry->move;
					hash_depth = Entry->low_depth;
				}
			}
			else
			{
				Entry->low_depth = 1;
				Entry->low = alpha;
			}
		}
		if (auto pvEntry = probe_pv_hash(current))
			return pvEntry->value;
	}

	current.mask = capture_margin_mask<me>(*state, alpha, &score);

	int nTried = 0;
	if (T(hash_move))
	{
		if (HasBit(current.mask, To(hash_move))
				|| T(hash_move & 0xE000)
				|| (depth >= -8 && (current.score + DeltaM(state, hash_move) > alpha || is_check<me>(*state, hash_move))))
		{
			move = hash_move;
			if (is_legal<me>(*state, move) && !IsIllegal(*state, move))
			{
				if (SeeValue[board.PieceAt(To(move))] > SeeValue[board.PieceAt(From(move))])
					++nTried;
				do_move<me>(state, move);
				value = -QSearch<opp>(state, -beta, -alpha, depth - 1, FlagNeatSearch);
				undo_move<me>(state, move);
				if (value > score)
				{
					score = value;
					if (value > alpha)
					{
						if (value >= beta)
							return hash_low(current, move, score, 1, false);
						alpha = value;
					}
				}
				if (F(Bit(To(hash_move)) & current.mask)
						&& F(hash_move & 0xE000)
						&& alpha >= beta - 1
						&& (depth < -2 || depth <= -1 && current.score + Futility::HashCut<me>(*state, false) < alpha))
					return alpha;
			}
		}
	}

	// done with hash move
	(void)gen_captures<me>(state->current_->moves, *state);
	state->current_->current = state->current_->moves;
	while (move = pick_move(state->current_))
	{
		if (move != hash_move && !IsIllegal(*state, move) && see<me>(*state, move, -SeeThreshold))
		{
			if (SeeValue[board.PieceAt(To(move))] > SeeValue[board.PieceAt(From(move))])
				++nTried;
			do_move<me>(state, move);
			value = -QSearch<opp>(state, -beta, -alpha, depth - 1, FlagNeatSearch);
			undo_move<me>(state, move);
			if (value > score)
			{
				score = value;
				if (score > alpha)
				{
					if (score >= beta)
						return hash_low(current, move, Max(score, beta), 1, false);
					alpha = score;
				}
			}
		}
	}

	if (depth < -2 || (depth <= -1 && current.score + Futility::CheckCut<me>(*state) < alpha))
		return finish(score, false);
	gen_checks<me>(state->current_->moves, *state);
	state->current_->current = state->current_->moves;
	while (move = pick_move(state->current_))
	{
		if (move != hash_move 
			&& !IsIllegal(*state, move) 
			&& !IsRepetition(*state, alpha + 1, move) 
			&& see<me>(*state, move, -SeeThreshold))
		{
			do_move<me>(state, move);
			value = -q_evasion<opp>(state, -beta, -alpha, depth - 1, FlagNeatSearch);
			undo_move<me>(state, move);
			if (value > score)
			{
				score = value;
				if (score > alpha)
				{
					if (score >= beta)
						return hash_low(current, move, Max(score, beta), 1, false);
					alpha = score;
				}
			}
		}
	}

	if (T(nTried) 
			|| current.score + Futility::DeltaCut<me>(*state) < alpha 
			|| T(current.threat & board.Piece(me)) 
			|| T(current.xray[opp] & board.NonPawn(opp)) 
			|| T(board.Pawn(opp) & OwnLine<me>(1) & Shift<me>(~board.PieceAll())))
		return finish(score, false);
	int margin = alpha - current.score + 6 * CP_SEARCH;
	gen_delta_moves<me>(state->current_->moves, state, margin);
	state->current_->current = state->current_->moves;
	while (move = pick_move(state->current_))
	{
		if (move != hash_move 
			&& !IsIllegal(*state, move)
			&& !IsRepetition(*state, alpha + 1, move) 
			&& see<me>(*state, move, -SeeThreshold))
		{
			++nTried;
			do_move<me>(state, move);
			value = -QSearch<opp>(state, -beta, -alpha, depth - 1, FlagNeatSearch);
			undo_move<me>(state, move);
			if (value > score)
			{
				score = value;
				if (score > alpha)
				{
					if (score >= beta)
					{
						if (N_KILLER >= 1 && current.killer[1] != move)
						{
							for (int jk = N_KILLER; jk > 1; --jk)
								state->current_->killer[jk] = state->current_->killer[jk - 1];
							state->current_->killer[1] = move;
						}
						return hash_low(current, move, Max(score, beta), 1, false);
					}
					alpha = score;
				}
			}
			if (nTried >= 3)
				break;
		}
	}
	return finish(score, true);
}

template<bool me> int q_evasion(State_* state, int alpha, int beta, int depth, int flags)
{
	const Board_& board = state->board_;
	const PlyState_& current = *state->current_;
	
	int score = state->Height() - MateValue;
	if (flags & FlagHaltCheck)
		HALT_CHECK(state);

	int hash_move = 0, hash_depth = 0;
	if (flags & FlagHashCheck)
	{
		if (GEntry* Entry = probe_hash(current))
		{
			if (T(Entry->high_depth) && Entry->high <= alpha)
				return Entry->high;
			if (T(Entry->low_depth))
			{
				if (Entry->low >= beta)
					return Entry->low;
				if (Entry->low_depth > hash_depth && T(Entry->move))
				{
					hash_move = Entry->move;
					hash_depth = Entry->low_depth;
				}
			}
		}
		if (auto pvEntry = probe_pv_hash(current))
			return pvEntry->value;
	}

	if (flags & FlagCallEvaluation)
		evaluate(state);
	current.mask = Filled;
	if (current.score - 10 * CP_SEARCH <= alpha)
	{
		score = current.score - 10 * CP_SEARCH;
		current.mask = capture_margin_mask<me>(*state, alpha, &score);
	}

	alpha = Max(score, alpha);
	(void)gen_evasions<me>(state);
	state->current_->current = state->current_->moves;
	if (F(current.moves[0]))
		return score;
	int pext = F(current.moves[1]);
	if (!pext)
	{
		state->current_->ref = Refutations<me, true>(*state);
		mark_evasions(state->current_->moves, state);
		if (T(hash_move) && (T(Bit(To(hash_move)) & current.mask) || T(hash_move & 0xE000)))
		{
			for (auto p = state->current_->moves; T(*p); ++p)
			{
				if (((*p) & 0xFFFF) == hash_move)
				{
					*p |= 0x7FFF0000;
					break;
				}
			}
		}
	}
	int cnt = 0;
	while (int move = pick_move(state->current_))
	{
		if (IsIllegal(*state, move))
			continue;
		++cnt;
		if (IsRepetition(*state, alpha + 1, move))
		{
			score = Max(0, score);
			continue;
		}
		if (F(board.PieceAt(To(move))) && F(move & 0xE000))
		{
			if (cnt > 3 && !is_check<me>(*state, move))
				continue;
			if (int value = current.score + DeltaM(state, move) + 10 * CP_SEARCH; value <= alpha)
			{
				score = Max(value, score);
				continue;
			}
		}
		do_move<me>(state, move);
		int value = -QSearch<opp>(state, -beta, -alpha, depth - 1 + pext, FlagNeatSearch);
		undo_move<me>(state, move);
		if (value > score)
		{
			score = value;
			if (value > alpha)
			{
				if (value >= beta)
					return score;
				alpha = value;
			}
		}
	}
	return score;
}

template<bool exclusion, bool evasion> int cut_search(State_* state, int move, int hash_move, int score, int beta, int depth, int flags, int sp_init)
{
	if (exclusion)
		return score;
	state->current_->best = move;
	if (!evasion && depth >= 10)
		score = Min(beta, score);
	if (F(state->board_.PieceAt(To(move))) && F(move & 0xE000))
	{
		UpdateRef<evasion>(state, move);
		if (!evasion)
		{
			if (state->current_->killer[1] != move && F(flags & FlagNoKillerUpdate))
			{
				for (int jk = N_KILLER; jk > 1; --jk) 
					state->current_->killer[jk] = state->current_->killer[jk - 1];
				state->current_->killer[1] = move;
			}
			if (state->current_->stage == s_quiet && (move & 0xFFFF) == (*(state->current_->current - 1) & 0xFFFF))
				HistoryGood(state, *(state->current_->current - 1), depth);	// restore history information
			else
				HistoryGood(state, move, depth);
			if (move != hash_move && state->current_->stage == s_quiet && !sp_init)
				for (auto p = state->current_->start; p < (state->current_->current - 1); ++p)
					HistoryBad(state, *p, depth);
		}
	}
	return hash_low(*state->current_, move, score, depth, false);
};

INLINE int RazoringThreshold(int score, int depth, int height)
{
	return score + (70 + 8 * Max(height, depth) + 3 * Square(Max(0, depth - 7))) * CP_SEARCH;
}

template<int PV = 0> struct LMR_
{
	const double scale_;
	LMR_(int depth) : scale_(0.118 + 0.001 * depth) {}
	INLINE int operator()(int cnt, int stage) const
	{
		if (cnt <= 2 || stage < s_quiet)
			return 0;
		int retval = int(scale_ * msb(Square(Square(Square(uint64(cnt)))))) - PV;
		return Max(0, retval);
	}
};

struct HashResult_
{
	bool done_;
	int score_;
	int hashMove_;
	int played_;
	int singular_;
};

template<int me> void check_recapture(const State_& state, int to, int depth, int* ext)
{
	if (depth < 16 && to == To(state[0].move) && T(state().PieceAt(to)))
		*ext = Max(*ext, 2);
}

template<bool me, bool evasion> HashResult_ try_hash(State_* state, int beta, int depth, int flags)
{
	const Board_& board = state->board_;
	const PlyState_& current = *state->current_;

	auto abort = [](int score) {return HashResult_({ true, score, 0, 0, }); };
	if (flags & FlagCallEvaluation)
		evaluate(state);
	if (!evasion && IsCheck(*state, me))
		return abort(scout<me, 0, 1>(state, beta, depth, flags & (~(FlagHaltCheck | FlagCallEvaluation))));

	if (!evasion)
	{
		int value = current.score - (90 + depth * 8 + Max(depth - 5, 0) * 32) * CP_SEARCH;
		if (value >= beta 
			&& depth <= 13 
			&& T(board.NonPawnKing(me)) 
			&& F(board.Pawn(opp) & OwnLine<me>(1) & Shift<me>(~board.PieceAll())) 
			&& F(flags & (FlagReturnBestMove | FlagDisableNull)))
			return abort(value);

		value = current.score + Futility::HashCut<me>(*state, false);
		if (value < beta && depth <= 3)
			return abort(Max(value, QSearch<me>(state, beta - 1, beta, 1, FlagHashCheck | (flags & 0xFFFF))));
	}

	int hash_move = current.best = flags & 0xFFFF;
	current.best = hash_move;
	int high_depth = 0, hash_depth = -1;
	int high_value = MateValue, hash_value = -MateValue;
	if (GEntry* Entry = probe_hash(current))
	{
		if (Entry->high < beta && Entry->high_depth >= depth)
			return abort(Entry->high);
		if (!evasion && Entry->high_depth > high_depth)
		{
			high_depth = Entry->high_depth;
			high_value = Entry->high;
		}
		if (T(Entry->move) && Entry->low_depth > hash_depth)
		{
			current.best = hash_move = Entry->move;
			hash_depth = Entry->low_depth;
			if (!evasion && Entry->low_depth)
				hash_value = Entry->low;
		}
		if (Entry->low >= beta && Entry->low_depth >= depth)
		{
			if (Entry->move)
			{
				current.best = Entry->move;
				if (F(board.PieceAt(To(Entry->move))) && F(Entry->move & 0xE000))
				{
					UpdateRef<evasion>(state, Entry->move);
					if (!evasion)
					{
						if (current.killer[1] != Entry->move && F(flags & FlagNoKillerUpdate))
						{
							for (int jk = N_KILLER; jk > 1; --jk)
								state->current_->killer[jk] = state->current_->killer[jk - 1];
							state->current_->killer[1] = Entry->move;
						}
					}
				}
				return abort(Entry->low);
			}
			if (evasion || F(flags & FlagReturnBestMove))
				return abort(Entry->low);
		}
		if (evasion && Entry->low_depth >= depth - 8 && Entry->low > hash_value)
			hash_value = Entry->low;
	}

	if (auto res = PyrrhicWDL(*state, depth); res != TB_RESULT_FAILED)
	{
		++state->tbHits_;
		hash_low(current, 0, TbValues[res], TbDepth(depth), true);
		hash_high(current, TbValues[res], TbDepth(depth), true);
		return abort(TbValues[res]);
	}

	if (GPVEntry * PVEntry = (depth < 20 ? nullptr : probe_pv_hash(current)))
	{
		hash_low(current, PVEntry->move, PVEntry->value, PVEntry->depth, true);
		hash_high(current, PVEntry->value, PVEntry->depth, true);
		if (PVEntry->depth >= depth)
		{
			if (PVEntry->move)
				current.best = PVEntry->move;
			if (F(flags & FlagReturnBestMove) && (current.ply <= PliesToEvalCut) == (PVEntry->ply <= PliesToEvalCut))
				return abort(PVEntry->value);
		}
		if (T(PVEntry->move) && PVEntry->depth > hash_depth)
		{
			current.best = hash_move = PVEntry->move;
			hash_depth = PVEntry->depth;
			hash_value = PVEntry->value;
		}
	}

	int score = depth < 10 ? state->Height() - MateValue : beta - 1;
	if (evasion && hash_depth >= depth && hash_value > -EvalValue)
		score = Min(beta - 1, Max(score, hash_value));
	if (evasion && T(flags & FlagCallEvaluation))
		evaluate(state);

	if (!evasion && depth >= 12 && (F(hash_move) || hash_value < beta || hash_depth < depth - 12) && (high_value >= beta || high_depth < depth - 12) &&
		F(flags & FlagDisableNull))
	{
		int new_depth = depth - 8;
		int value = scout<me, 0, 0>(state, beta, new_depth, FlagHashCheck | FlagNoKillerUpdate | FlagDisableNull | FlagReturnBestMove | hash_move);
		if (value >= beta)
		{
			if (current.best)
				hash_move = current.best;
			hash_depth = new_depth;
			hash_value = beta;
		}
	}
	if (!evasion 
		&& depth >= 4 
		&& current.score + 3 * CP_SEARCH >= beta 
		&& F(flags & (FlagDisableNull | FlagReturnBestMove)) 
		&& (high_value >= beta || high_depth < depth - 10) 
		&& (depth < 12 || (hash_value >= beta && hash_depth >= depth - 12)) 
		&& beta > -EvalValue 
		&& T(board.NonPawnKing(me)))
	{
		int new_depth = depth - 8;
		do_null(state);
		int value = -scout<opp, 0, 0>(state, 1 - beta, new_depth, FlagHashCheck);
		undo_null(state);
		if (value >= beta)
		{
			if (depth < 12)
				hash_low(current, 0, value, depth, false);
			return abort(value);
		}
	}

	if (evasion)
	{
		current.mask = Filled;
		if (depth < 4 && current.score - 10 * CP_SEARCH < beta)
		{
			score = current.score - 10 * CP_SEARCH;
			current.mask = capture_margin_mask<me>(*state, beta - 1, &score);
		}
		(void)gen_evasions<me>(state);
		if (F(current.moves[0]))
			return abort(score);
	}

	if (T(hash_move))
	{
		int singular = 0;
		auto succeed = [&](int score) {return HashResult_({ true, score, hash_move, 1, singular }); };
		int move = hash_move;
		if (is_legal<me>(*state, move) && !IsIllegal(*state, move))
		{
			int ext = evasion && F(current.moves[1])
					? 2
					: (is_check<me>(*state, move) 
							? check_extension<me, 0>(move, depth) 
							: extension<me, 0>(current, move, depth));
			if (ext < 2 && depth >= 16 && hash_value >= beta)
			{
				int test_depth = depth - Min(12, depth / 2);
				if (hash_depth >= test_depth)
				{
					int margin_one = beta - ExclSingle(depth);
					int margin_two = beta - ExclDouble(depth);
					int prev_ext = ExtFromFlag(flags);
					if (singular = singular_extension<me>(state, ext, prev_ext, margin_one, margin_two, test_depth, hash_move))
						ext = Max(ext, singular + (prev_ext < 1) - (singular >= 2 && prev_ext >= 2));
				}
			}
			int to = To(move);
			check_recapture<0>(*state, to, depth, &ext);
			int new_depth = depth - 2 + ext;
			do_move<me>(state, move);
			if (evasion)
				evaluate(state);
			if (evasion && T(state->current_->att[opp] & state->board_.King(me)))	// POSTPONED -- why only if evasion?
			{
				undo_move<me>(state, move);
				return HashResult_({ false, score, hash_move, 0 });
			}
			int new_flags = (evasion ? FlagNeatSearch ^ FlagCallEvaluation : FlagNeatSearch)
				| ((hash_value >= beta && hash_depth >= depth - 12) ? FlagDisableNull : 0)
				| ExtToFlag(ext);

			int value = -scout<opp, 0, 0>(state, 1 - beta, new_depth, new_flags);
			undo_move<me>(state, move);
			if (value > score)
				score = value;
			return HashResult_({ false, score, hash_move, 1, singular });
		}
	}
	return HashResult_({ false, score, hash_move, 0, 0 });
}

template<bool me, bool exclusion, bool evasion> int scout(State_* state, int beta, int depth, int flags)
{
	const Board_& board = state->board_;
	const PlyState_& current = *state->current_;

	int height = state->Height();
	if (height > 100)
		++beta;

	if (depth <= 1)
		return (evasion ? q_evasion<me> : QSearch<me>)(state, beta - 1, beta, 1, flags);
	int score = height - MateValue;
	if (flags & FlagHaltCheck)
	{
		if (score >= beta)
			return beta;
		if (MateValue - height < beta)
			return beta - 1;
		if (!evasion)
		{
			HALT_CHECK(state);
		}
		if (depth >= 8 && time_to_stop(state->searchInfo_, millisecs(TheTimeLimit.start_, now()), true))
			stop();	// will break the outer loop
	}

	int hash_move = flags & 0xFFFF, cnt = 0, played = 0;
	int do_split = 0, sp_init = 0;
	int singular = 0;
	if (exclusion)
	{
		score = beta - 1;
		if (evasion)
		{
			(void)gen_evasions<me>(state);
			if (F(current.moves[0]))
				return score;
		}
	}
	else
	{
		HashResult_ hash_info = try_hash<me, evasion>(state, beta, depth, flags);
		score = hash_info.score_;
		if (hash_info.done_)
			return score;
		hash_move = hash_info.hashMove_;
		if (score >= beta)
			return cut_search<exclusion, evasion>(state, hash_move, hash_move, score, beta, depth, flags, 0);
		cnt = played = hash_info.played_;
		singular = hash_info.singular_;
	}

	// done with hash 
	bool can_hash_d0 = !exclusion && !evasion;
	const int margin = evasion ? 0 : RazoringThreshold(current.score, depth, height);	// not used if evasion
	state->current_->ref = Refutations<me, evasion>(*state);
	if (evasion)
		mark_evasions(state->current_->moves, state);
	else
	{
		state->current_->killer[0] = 0;
		state->current_->stage = stage_search;
		state->current_->gen_flags = 0;
		if (margin < beta)
		{
			can_hash_d0 = false;
			score = Max(margin, score);
			state->current_->stage = stage_razoring;
			state->current_->mask = board.Piece(opp);
			int value = margin + (200 + 8 * depth) * CP_SEARCH;
			if (value < beta)
			{
				score = Max(value, score);
				state->current_->mask ^= board.Pawn(opp);
			}
		}
		state->current_->moves[0] = 0;
		if (depth <= 5)
			state->current_->gen_flags |= FlagNoBcSort;
	}
	int moves_to_play = 3 + Square(depth) / 6;
	state->current_->current = state->current_->moves;

	bool forced = evasion && F(current.moves[1]);
	int move_back = 0;
	if (beta > 0 && height >= 2 && current.ply >= 2 && F((*state)[1].move & 0xF000))
	{
		int pvsMove = (*state)[1].move;
		move_back = (To(pvsMove) << 6) | From(pvsMove);
		if (board.PieceAt(To(move_back)))
			move_back = 0;
	}

	LMR_<0> reduction_n(depth);
	while (int move = evasion ? pick_move(state->current_) : NextMove<me>(state, depth))
	{
		if (move == hash_move)
			continue;
		if (IsIllegal(*state, move))
			continue;
		++cnt;
		if ((move & 0xFFFF) == move_back && IsRepetition(*state, beta, move))
		{
			score = Max(0, score);
			continue;
		}
		bool check = (!evasion && current.stage == r_checks) || is_check<me>(*state, move);
		int ext;
		if (evasion && forced)
			ext = 2;
		else if (check && see<me>(*state, move, 0))
			ext = check_extension<me, 0>(move, depth);
		else
			ext = extension<me, 0>(current, move, depth);
		int new_depth = depth - 2 + ext;
		if (F(board.PieceAt(To(move))) && F(move & 0xE000))
		{
			if (evasion || !is_killer(current, move))
			{
				if (!check && cnt > moves_to_play)
				{
					state->current_->gen_flags &= ~FlagSort;
					continue;
				}
				if (!evasion && !check && F(board.PieceAt(To(move))))
				{
					int reduction = reduction_n(cnt, current.stage);
					if (!evasion && move == current.ref[0] || move == current.ref[1])
						reduction = Max(0, reduction - 1);
					if (reduction >= 2 && !(board.Queen(White) | board.Queen(Black)) && popcnt(board.NonPawnKingAll()) <= 4)
						reduction += reduction / 2;
					if (!evasion && new_depth - reduction > 3 && !see<me>(*state, move, -SeeThreshold))
						reduction += 2;
					if (!evasion && reduction == 1 && new_depth > 4)
						reduction = cnt > 3 ? 2 : 0;
					new_depth = max(new_depth - reduction, min(depth - 3, 3));
				}
			}
			if (!check)
			{
				int value = current.score + DeltaM(state, move) + 10 * CP_SEARCH;
				if (value < beta && depth <= 3)
				{
					score = Max(value, score);
					continue;
				}
				if (!evasion && cnt > 7 && (value = margin + DeltaM(state, move) - 25 * CP_SEARCH * msb(cnt)) < beta && depth <= 19)
				{
					score = Max(value, score);
					continue;
				}
			}
			if (!evasion && depth <= 9 && T(board.NonPawnKing(me)) && !see<me>(*state, move, -SeeThreshold))
				continue;
		}
		else if (!evasion && !check && depth <= 9)
		{
			if ((current.stage == s_bad_cap && depth <= 5)
				|| (current.stage == r_cap && !see<me>(*state, move, -SeeThreshold)))
				continue;
		}

		do_move<me>(state, move);
		if (probe_pv_hash(*state->current_) && new_depth < depth - 2 + Min(1, ext))
			++new_depth;
		int value = -scout<opp, 0, 0>(state, 1 - beta, new_depth, FlagNeatSearch | ExtToFlag(ext));	// POSTPONED -- call scout_evasion here if check?
		if (value >= beta && new_depth < depth - 2 + ext)
			value = -scout<opp, 0, 0>(state, 1 - beta, depth - 2 + ext, FlagNeatSearch | FlagDisableNull | ExtToFlag(ext));
		undo_move<me>(state, move);
		++played;
		if (value > score)
		{
			score = value;
			if (value >= beta)
				return cut_search<exclusion, evasion>(state, move, hash_move, score, beta, depth, flags, sp_init);
		}
	}

	if (can_hash_d0 && F(cnt))
	{
		hash_high(current, 0, 127, true);
		hash_low(current, 0, 0, 127, true);
		return 0;
	}
	if (F(exclusion))
		hash_high(current, score, depth, false);
	return score;
}


void send_curr_move(int move, int cnt)
{
	assert(move);
	auto currTime = now();
	auto diffTime = millisecs(TheTimeLimit.start_, currTime);
	if (diffTime <= InfoLag || millisecs(InfoTime, currTime) <= InfoDelay)
		return;
	InfoTime = currTime;
	char moveStr[16];
	move_to_string(move, moveStr);
	printf("info currmove %s currmovenumber %d\n", moveStr, cnt);
}

void send_multipv(int depth, int curr_number)
{
	abort();	// not implemented
}


struct Thread_
{
	State_ state_;
	vector<Thread_>* peeps_;	// held by only first thread
	ThreadOwn_ own_;
};

template<bool me> int RootMove(Thread_* self, int depth)
{
	PlyState_* current = self->state_.current_;
	int move = (*current->current) & 0xFFFF;
	current->current++;
	return move;
}


struct AtRoot_
{
	enum {ROOT = 1};
	using out_t = pair<sint16, uint16>;
	out_t Output(sint16 score, uint16 move) const { return make_pair(score, move); }
};
struct NotRoot_
{
	enum {ROOT = 0};
	using out_t = sint16;
	out_t Output(sint16 score, uint16 ) const { return score; }
};

template<bool me, class T_> typename T_::out_t pv_search(T_ where, Thread_* self, int alpha, int beta, int depth, int flags)
{
	bool RootList = false;	// hide global RootList; we use only self->own_.rootList_
	State_* state = &self->state_;
	const PlyState_& current = *state->current_;
	const Board_& board = state->board_;

	int value, move, cnt, pext = 0, ext, hash_value = -MateValue, margin, singular = 0, played = 0, new_depth, hash_move,
			hash_depth, old_alpha = alpha, ex_depth = 0, ex_value = 0;
	int start_knodes = static_cast<int>(state->nodes_ >> 10);
	int height = state->Height();

	if (!self->own_.results_.empty() && (where.ROOT || depth > 8 || depth > 2 + height))
	{	// don't bother checking for stop until we can make some move
		self->own_.lastTime_ = millisecs(TheTimeLimit.start_, now());
		if (time_to_stop(state->searchInfo_, self->own_.lastTime_, !where.ROOT))
			stop();	// will break the outer loop
	}
	if constexpr (where.ROOT)
	{
		auto& rootList = self->own_.rootList_;
		depth = Max(depth, 2);
		flags |= ExtToFlag(1);
		if (F(rootList[0]))
			return where.Output(0, 0);

		sort_moves(rootList.begin(), rootList.end());
		for (auto& m : rootList)
			m &= 0xFFFF;
		SetMoveScore(&rootList[0], 2);
	}
	else
	{
		if (depth <= 1)
			return where.Output(QSearch<me>(state, alpha, beta, 1, FlagNeatSearch), 0);
		if (height - MateValue >= beta)
			return where.Output(beta, 0);
		if (MateValue - height <= alpha)
			return where.Output(alpha, 0);
		if constexpr (!where.ROOT)
			HALT_CHECK(state);
	}

	// check hash
	hash_depth = -1;
	current.best = hash_move = 0;
	if (GPVEntry* PVEntry = probe_pv_hash(current))
	{
		hash_low(current, PVEntry->move, PVEntry->value, PVEntry->depth, true);
		hash_high(current, PVEntry->value, PVEntry->depth, true);
		if (PVEntry->depth >= depth)
		{
			if (PVEntry->move)
				current.best = PVEntry->move;
			if ((current.ply <= PliesToEvalCut && PVEntry->ply <= PliesToEvalCut) || (current.ply >= PliesToEvalCut && PVEntry->ply >= PliesToEvalCut))
				if (!PVEntry->value || !draw_in_pv<me>(state))
					return where.Output(PVEntry->value, PVEntry->move);
		}
		if (T(PVEntry->move) && PVEntry->depth > hash_depth)
		{
			current.best = hash_move = PVEntry->move;
			hash_depth = PVEntry->depth;
			hash_value = PVEntry->value;
		}
		state->searchInfo_.hashDepth_ = hash_depth;
	}
	if (time_to_stop(state->searchInfo_, self->own_.lastTime_, !where.ROOT))
		stop();	// will break the outer loop
	check_for_stop();
	if (GEntry* Entry = probe_hash(current))
	{
		if (T(Entry->move) && Entry->low_depth > hash_depth)
		{
			current.best = hash_move = Entry->move;
			hash_depth = Entry->low_depth;
			if (Entry->low_depth)
				hash_value = Entry->low;
		}
	}
	if (auto res = PyrrhicWDL(*state, depth); res != TB_RESULT_FAILED) 
	{
		++state->tbHits_;
		hash_high(current, TbValues[res], TbDepth(depth), true);
		hash_low(current, 0, TbValues[res], TbDepth(depth), true);
	}

	if constexpr (where.ROOT)
	{
		hash_move = self->own_.rootList_[0];
		hash_value = TheShare.pvsScore_;
		hash_depth = Max(0, depth - 2);
	}

	evaluate(state);

	if (F(where.ROOT) && depth >= 6 && (F(hash_move) || hash_value <= alpha || hash_depth < depth - 8))
	{
		new_depth = depth - (T(hash_move) ? 4 : 2);
		value = pv_search<me>(NotRoot_(), self, alpha, beta, new_depth, hash_move);
		bool accept = value > alpha || alpha < -EvalValue;
		if (!accept)
		{
			new_depth = depth - 8;
			for (int i = 0; i < 5 && !accept; ++i)
			{
				margin = alpha - (CP_SEARCH << (i + 3));
				if (T(hash_move) && hash_depth >= new_depth && hash_value >= margin)
					break;
				value = scout<me, 0, 0>(state, margin, new_depth, FlagHashCheck | FlagNoKillerUpdate | FlagDisableNull | FlagReturnBestMove | hash_move);
				accept = value >= margin;
			}
		}
		if (accept)
		{
			if (current.best)
				hash_move = current.best;
			hash_depth = new_depth;
			TheShare.pvsScore_ = hash_value = value;
		}
	}
	if (F(where.ROOT) && IsCheck(*state, me))
	{
		current.mask = Filled;
		(void)gen_evasions<me>(state);
		if (F(current.moves[0]))
			return where.Output(height - MateValue, 0);
		alpha = Max(2 + height - MateValue, alpha);
		if (F(current.moves[1]))
			pext = 2;
	}

	cnt = 0;
	if (hash_move && is_legal<me>(*state, move = hash_move))
	{
		++cnt;
		if (where.ROOT)
		{
			state->ClearStack();
			if (self->peeps_)
				send_curr_move(move, cnt);
		}
		ext = Max(pext, extension<me, 1>(*state->current_, move, depth));
		check_recapture<1>(*state, To(move), depth, &ext);
		if (depth >= 12 && hash_value > alpha && ext < 2 && hash_depth >= (new_depth = depth - Min(12, depth / 2)))
		{
			int margin_one = hash_value - ExclSingle(depth);
			int margin_two = hash_value - ExclDouble(depth);
			int prev_ext = ExtFromFlag(flags);
			singular = singular_extension<me>(state, where.ROOT ? 0 : ext, where.ROOT ? 0 : prev_ext, margin_one, margin_two, new_depth, hash_move);
			if (singular)
			{
				ext = Max(ext, singular + (prev_ext < 1) - (singular >= 2 && prev_ext >= 2));
				if constexpr (where.ROOT)
					state->searchInfo_.singular_ = singular;
				ex_depth = new_depth;
				ex_value = (singular >= 2 ? margin_two : margin_one) - 1;
			}
		}
		new_depth = depth - 2 + ext;
		if constexpr (where.ROOT)
		{
			if (height < self->own_.pvRefDepth_.size())
				new_depth = self->own_.pvRefDepth_[height] = Max(new_depth, self->own_.pvRefDepth_[height]);
			else
				self->own_.pvRefDepth_.resize(height + 1, new_depth);
		}
		do_move<me>(state, move);
		evaluate(state);
		if (state->current_->att[opp] & state->board_.King(me))
		{
			undo_move<me>(state, move);
			--cnt;
		}
		else
		{
			value = -pv_search<opp>(NotRoot_(), self, -beta, -alpha, new_depth, ExtToFlag(ext));
			undo_move<me>(state, move);
			++played;
			if constexpr (where.ROOT)
				self->own_.results_.Add(move, value, depth, alpha, beta);
			if (value > alpha)
			{
				if constexpr (where.ROOT)
				{
					state->searchInfo_.failLow_ = false;
					state->searchInfo_.failHigh_ = state->searchInfo_.early_ = value >= beta;
					hash_low(current, move, value, depth, false);
					// only send info on return to aspiration window
				}
				current.best = move;
				if (value >= beta)
					return where.Output(hash_low(current, move, value, depth, false), move);
				alpha = value;
			}
			else if constexpr (where.ROOT)
			{
				state->searchInfo_.failLow_ = true;
				state->searchInfo_.failHigh_ = false;
				state->searchInfo_.singular_ = 0;
				// only send PV on return to aspiration window
			}
		}
	}

	state->current_->gen_flags = 0;
	if (!IsCheck(*state, me))
	{
		state->current_->stage = stage_search;
		state->current_->ref = Refutations<me, false>(*state);
	}
	else
	{
		state->current_->stage = stage_evasion;
		state->current_->ref = Refutations<me, true>(*state);
	}
	state->current_->killer[0] = 0;
	state->current_->moves[0] = 0;
	if constexpr (where.ROOT)
		state->current_->current = &self->own_.rootList_[1];
	else
		state->current_->current = state->current_->moves;

	LMR_<1> reduction_n(depth);
	bool firstIsBest = true;
	while (move = (where.ROOT ? RootMove<me>(self, depth) : NextMove<me>(state, depth)))
	{
		if (where.ROOT && depth < TheShare.depth_)
			break;
		if (move == hash_move)
			continue;
		if (IsIllegal(*state, move))
			continue;
		++cnt;
		if constexpr (where.ROOT)
		{
			state->ClearStack();
			if (self->peeps_)
				send_curr_move(move, cnt);
		}
		if (IsRepetition(*state, alpha + 1, move))
			continue;
		ext = Max(pext, extension<me, 1>(current, move, depth));
		check_recapture<1>(*state, To(move), depth, &ext);
		new_depth = depth - 2 + ext;
		if (depth >= 6 && F(move & 0xE000) && F(board.PieceAt(To(move))) && (where.ROOT || !is_killer(current, move)) && F(IsCheck(*state, me)) && cnt > 3)
		{
			int reduction = reduction_n(cnt, current.stage);
			if (move == current.ref[0] || move == current.ref[1])
				reduction = Max(0, reduction - 1);
			if (reduction >= 2 && !(board.Queen(White) | board.Queen(Black)) && popcnt(board.NonPawnKingAll()) <= 4)
				reduction += reduction / 2;
			if (reduction > 2 && state->Height() < 2)
				reduction += 2 - state->Height();
			new_depth = Max(3, new_depth - reduction);
		}

		do_move<me>(state, move);  // now current != state->current_, until undo_move below
		if (new_depth <= 1)
			value = -pv_search<opp>(NotRoot_(), self, -beta, -alpha, new_depth, ExtToFlag(ext));
		else
			value = -scout<opp, 0, 0>(state, -alpha, new_depth, FlagNeatSearch | ExtToFlag(ext));
		if (value > alpha && new_depth > 1)
		{
			if constexpr (where.ROOT)
			{
				SetMoveScore(&self->own_.rootList_[cnt - 1], 1);
				state->searchInfo_.early_ = false;
			}
			new_depth = depth - 2 + ext;
			value = -pv_search<opp>(NotRoot_(), self, -beta, -alpha, new_depth, ExtToFlag(ext));
		}
		undo_move<me>(state, move);
		++played;
		if constexpr (where.ROOT)
			self->own_.results_.Add(move, value, depth, alpha, beta);
		if (value > alpha)
		{
			if constexpr (where.ROOT)
			{
				SetMoveScore(&self->own_.rootList_[cnt - 1], cnt + 3);
				state->searchInfo_.moves_.push(0);
				firstIsBest = false;
				state->searchInfo_.failLow_ = false;
				hash_low(current, move, value, depth, false);
				// only send PV on return to aspiration window
			}
			current.best = move;
			if (value >= beta)
				return where.Output(hash_low(current, move, value, depth, false), move);
			alpha = value;
		}
	}
	if (where.ROOT && firstIsBest)
		state->searchInfo_.moves_.push(hash_move);
	if (F(cnt) && !IsCheck(*state, me))
	{
		hash_exact(current, 0, 0, 127, 0, 0, 0);
		return where.Output(0, 0);
	}
	hash_high(current, alpha, depth, false);
	if (alpha > old_alpha)
	{
		if (current.best != hash_move)
			ex_depth = 0;
		hash_exact(current, current.best, alpha, depth, ex_value, ex_depth, static_cast<int>(state->nodes_ >> 10) - start_knodes);
	}
	return where.Output(alpha, current.best);
}


// try to fit into Ethereal framework

struct PVariation
{
	score_t score_;
	vector<uint16> line_;
	PVariation(score_t score) : score_(score) { line_.reserve(MAX_HEIGHT); }
};

void uciReport(const Thread_& thread, const vector<Thread_>* all_threads, const PVariation& pv)
{
	// Gather all of the statistics that the UCI protocol would be
	// interested in. Also, bound the value passed by alpha and
	// beta, since Ethereal uses a mix of fail-hard and fail-soft

	const AspirationState_& window = thread.own_.window_;
	uint32 elapsed = millisecs(TheTimeLimit.start_, now());
	int bounded = Max(window.alpha_, Min<int>(pv.score_, window.beta_));

	if (all_threads)
	{
		uint64 nodes = 0, tbhits = 0;
		for (const auto& t : *all_threads)
		{
			nodes += t.state_.nodes_;
			tbhits += t.state_.tbHits_;
		}
		//int nps = (int)(1000 * (nodes / (1 + elapsed)));

		printf("info time %d knodes %d tbhits %d\n",
			static_cast<int>(elapsed), static_cast<int>(nodes >> 10), static_cast<int>(tbhits));
	}

	// If the score is MATE or MATED in X, convert to X
	int score = bounded >= EvalValue
			? (MateValue - bounded + 1) / 2
			: bounded <= -EvalValue ? -(bounded + MateValue) / 2 : bounded;

	// Two possible score types, mate and cp = centipawns
	const char* type = abs(bounded) >= EvalValue ? "mate" : "cp";

	// Partial results from a windowed search have bounds
	const char* bound = bounded >= window.beta_
			? " lowerbound "
			: bounded <= window.alpha_ ? " upperbound " : " ";

	printf("info depth %d seldepth %d score %s %d%spv ",
			window.depth_ / 2, thread.state_.selDepth_, type, score / CP_SEARCH, bound);

	// Iterate over the PV and print each move
	for (auto m: pv.line_)
	{
		if (!m)
			break;
		char moveStr[6];
		move_to_string(m, moveStr);
		printf("%s ", moveStr);
	}

	// Send out a newline and flush
	puts(""); fflush(stdout);
}


AtRoot_::out_t search(Thread_* self, score_t alpha, score_t beta, int depth, bool cutnode)
{
	State_* state = &self->state_;
	// NodeState* ns = &thread->states[thread->height];

	auto func = state->current_->turn ? pv_search<Black, AtRoot_> : pv_search<White, AtRoot_>;
	return func(AtRoot_(), self, alpha, beta, depth, FlagNeatSearch);
}


struct LimitInputs_
{
	int time, inc, mtg;
	uint32 timeLimit;
	int limitedByNone, limitedByTime, limitedBySelf;
	int limitedByDepth, limitedByMoves, limitedByNodes;
	int multiPV, depthLimit;
	uint64 nodeLimit;
	array<uint16_t, 256> searchMoves, excludedMoves;
};


uint16 move_from_hash(const State_& state, size_t height = 0)
{
	if (GPVEntry* PVEntry = probe_pv_hash(state.stack_[height]))
	{
		if (PVEntry->move)
			return PVEntry->move;
	}
	if (GEntry* Entry = probe_hash(state.stack_[height]))
	{
		if (Entry->move)
			return Entry->move;
	}
	return 0;
}

PVariation PVFromHash(score_t score, const State_& state_in, int best_move)
{
	constexpr int MICRO_HASH = 1024;	// accept some stubby PVs
	bitset<MICRO_HASH> seen = {};
	PVariation pv(score);
	// See if we can provide a ponder from the hashtable
	State_ tempState;
	tempState.Reset(state_in);
	while (pv.line_.size() < MAX_PV_LEN)
	{
		uint16 move = pv.line_.empty() && T(best_move) ? best_move : move_from_hash(tempState, pv.line_.size());
		if (move && !is_legal(tempState, move))
			move = 0;
		if (!move)
			break;
		pv.line_.push_back(move);
		do_move(&tempState, tempState.current_->turn, move);
		auto loc = tempState.current_->key & (MICRO_HASH - 1);
		if (pv.line_.size() > 4 && seen[loc])
			break;
		seen.set(loc);
	}
	return pv;
}

sint16 ExpandDelta(sint16 delta)
{
	return delta > EvalValue / 2
			? EvalValue / 2
			: 4 * CP_SEARCH + delta + max(0, delta - 10 * CP_SEARCH);
}

void aspirationWindow(Thread_* thread)
{
	constexpr size_t MinUpdateMS = 2500;
	constexpr int MinUpdateDepth = 10;

	AspirationState_& window = thread->own_.window_;
	int depthIn = window.depth_;
	if (auto best = thread->own_.results_.best(); best.move_ != 0 && best.lower_ > -MateValue)
	{
		window.alpha_ = Max(-MateValue, best.lower_ - window.delta_);
		window.beta_ = Min<int>(MateValue, best.upper_ + window.delta_);
	}
	else if (auto h = probe_pv_hash(*thread->state_.current_))
	{
		if (h->move)
			thread->own_.results_.Add(h->move, h->value, h->depth, h->value - 1, h->value + 1);
		window.alpha_ = Max(-MateValue, h->value - window.delta_);
		window.beta_ = Min<int>(MateValue, h->value + window.delta_);
	}

	bool failedLow = false, failedHigh = false;
	for ( ; ; )
	{
		// Perform a search and consider reporting results
		auto [score, move] = search(thread, window.alpha_, window.beta_, window.depth_, false);
		if (!thread->own_.iThread_)
			if ((score > window.alpha_ && score < window.beta_) || millisecs(TheTimeLimit.start_, now()) >= MinUpdateMS)
			{
				PVariation pv = PVFromHash(score, thread->state_, 0);
				uciReport(*thread, nullptr, pv);
			}

		// Search returned a result within our window
		if (score < window.beta_)
		{
			if (score > window.alpha_)
			{
				if (window.depth_ > MinUpdateDepth)
				{
					window.delta_ = ExpandDelta(0);
					window.alpha_ = Max<int>(-MateValue, score - window.delta_);
					window.beta_ = Min<int>(MateValue, score + window.delta_);
				}
				return;
			}

			// Search failed low, adjust window and reset depth
			failedLow = true;
			window.alpha_ = Max(-MateValue + window.delta_, window.alpha_) - window.delta_;
			if (!failedHigh)
				window.beta_ = window.alpha_ + 1;
			window.depth_ = depthIn;
		}
		else
		{	// Search failed high, adjust window and reduce depth
			failedHigh = true;
			window.beta_ = Min(MateValue - window.delta_, window.beta_) + window.delta_;
			if (!failedLow)
				window.alpha_ = window.beta_ - 1;
		}
		if (window.alpha_ < -MateValue)
			window.alpha_ = -MateValue;
		if (window.beta_ > MateValue)
			window.beta_ = MateValue;
		window.delta_ = ExpandDelta(window.delta_);
	}
}


void iterativeDeepening(Thread_* thread, const LimitInputs_& limits)
{
	constexpr sint16 InitBeta = 200, InitDelta = 50;
	// Bind when we expect to deal with NUMA
	//if (thread->nthreads > 8)
	//    bindThisThread(thread->index);

	// Perform iterative deepening until exit conditions
	try
	{
		AspirationState_& window = thread->own_.window_ = ASPIRATION_INIT;

		for (; window.depth_ < MaxDepth; window.depth_ += 2)
		{
			if (auto pvEntry = probe_pv_hash(*thread->state_.current_))
				window.depth_ = Max(window.depth_, pvEntry->depth + 2);

			// Perform a search for the current depth for each requested line of play
			aspirationWindow(thread);
			// if (IS_PONDERING) continue;

			// Check for termination by any of the possible limits
			if ((limits.limitedBySelf && time_to_stop(thread->state_.searchInfo_, thread->own_.lastTime_, false))
					|| (limits.limitedByDepth && window.depth_ >= 2 * limits.depthLimit)
					|| (limits.limitedByTime && millisecs(TheTimeLimit.start_, now()) >= limits.timeLimit))
			{
				stop();  // for other threads
				break;
			}
		}
	}
	catch (Abort_)
	{	
		return;
	}
}


void get_position(char src[], State_* state)
{
	const char* fen;
	char* moves;
	const char* ptr;
	int move;

	fen = strstr(src, "fen ");
	moves = strstr(src, "moves ");
	if (fen != nullptr)
		get_board(fen + 4, state);
	else
		get_board("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", state);
	if (moves != nullptr)
	{
		char pv_string[1024];
		ptr = moves + 6;
		while (*ptr != 0)
		{
			pv_string[0] = *ptr++;
			pv_string[1] = *ptr++;
			pv_string[2] = *ptr++;
			pv_string[3] = *ptr++;
			if (*ptr == 0 || *ptr == ' ')
				pv_string[4] = 0;
			else
			{
				pv_string[4] = *ptr++;
				pv_string[5] = 0;
			}
			evaluate(state);
			move = move_from_string(*state, pv_string);
			if (state->current_->turn)
				do_move<1>(state, move);
			else
				do_move<0>(state, move);
			// push this down the stack
			memcpy(&state->stack_[0], state->current_, sizeof(PlyState_));
			state->current_ = &state->stack_[0];
			while (*ptr == ' ') ++ptr;
		}
	}
	if (state->hashHist_.size() > state->current_->ply + 1)
	{
		size_t offset = state->hashHist_.size() - state->current_->ply - 1;
		for (size_t ii = 0; ii < state->current_->ply; ++ii)
			state->hashHist_[ii] = state->hashHist_[ii + offset];
		state->hashHist_.resize(state->current_->ply + 1);
	}
}

inline int get_number(const char *token)
{
	if (token == NULL)
		return 0;
	return atoi(token);
}
inline size_t get_size(const char *token)
{
	if (token == NULL)
		return 0;
	return size_t(atoll(token));
}

namespace Version
{
	const char* mdy = __DATE__;
	const char now[10] = { mdy[7], mdy[8], mdy[9], mdy[10], mdy[0], mdy[1], mdy[2], mdy[4], mdy[5], 0 };
}

void SetTimeLimit(const LimitInputs_& input, int ply = 0)
{
	constexpr int MovesTg = 28, TimeRatio = 120;

	int time_max = Max(input.time - Min(1000, (3 * input.time) / 4), 0);
	int nmoves;
	int exp_moves = MovesTg - 1;
	if (input.mtg > 0)
		nmoves = Max(1, input.mtg - 1);
	else
	{
		nmoves = MovesTg - 1;
		if (ply > 40)
			nmoves += Min(ply - 40, (100 - ply) / 2);
		exp_moves = nmoves;
	}
	int softTimeLimit = Min(time_max, (time_max + (Min(exp_moves, nmoves) * input.inc) / 2) / Min(exp_moves, nmoves));
	int hardTimeLimit = Min(time_max, (time_max + (Min(exp_moves, nmoves) * input.inc)) / Min(7, Min(exp_moves, nmoves)));
	hardTimeLimit = Min(hardTimeLimit, 3 * softTimeLimit);

	if (input.timeLimit != 0)
	{
		hardTimeLimit = input.timeLimit;
		softTimeLimit = numeric_limits<decltype(softTimeLimit)>::max();
	}
	else if (input.limitedByNone)
		hardTimeLimit = softTimeLimit = numeric_limits<int>::max();

	TheTimeLimit.softLimit_ = softTimeLimit;
	TheTimeLimit.hardLimit_ = hardTimeLimit;
	printf("info time limits soft %d hard %d\n", softTimeLimit, hardTimeLimit);
}


#ifndef REGRESSION

void populateThreadPool(vector<Thread_>* threads)
{
	for (size_t i = 0; i < threads->size(); i++)
	{
		auto& thread = (*threads)[i];

		thread.peeps_ = i ? 0 : threads;
		init_search(&thread.own_, &thread.state_, !i, true);	// POSTPONED:  delete this?
		thread.own_.iThread_ = static_cast<uint16>(i);
	}
}

void resetThreadPool(vector<Thread_>* threads, bool clear_hash)
{
	// Reset the per-thread tables, used for move ordering
	// and evaluation caching. This is needed for ucinewgame
	// calls in order to ensure a deterministic behaviour

	for (auto& thread: *threads)
	{
		init_search(&thread.own_, &thread.state_, clear_hash && !thread.own_.iThread_, true);	// POSTPONED:  delete this?
	}
}


namespace
{
	int getInput(char* str)
	{
		char* ptr;

		if (fgets(str, 8192, stdin) == NULL)
			return 0;

		ptr = strchr(str, '\n');
		if (ptr != NULL) *ptr = '\0';

		ptr = strchr(str, '\r');
		if (ptr != NULL) *ptr = '\0';

		return 1;
	}

	int strEquals(const char* str1, const char* str2) {
		return strcmp(str1, str2) == 0;
	}

	int strStartsWith(const char* str, const char* key) {
		return strstr(str, key) == str;
	}
}	// leave local

struct UCIResponse_
{
	uint16_t best, ponder;
	int score;
};

UCIResponse_ select_from_threads(const vector<Thread_>& threads, const State_& state_in)
{
	/// A thread is better than another if any are true:
	/// [1] The thread has an equal depth and greater score.
	/// [2] The thread has a mate score and is closer to mate.
	/// [3] The thread has a greater depth without replacing a closer mate

	const Thread_* bestThread = nullptr;
	RootScores_::Record_ best = { 0, 0, -MateValue, -MateValue };
	for (const auto& t : threads)
	{
		auto result = t.own_.results_.best();
		if (result.move_ == 0)
			continue;
		char move[6];
		move_to_string(result.move_, move);
		printf("info best from thread %d: %s %d %d \n", t.own_.iThread_, move, result.lower_, result.depth_);

		if (bestThread)
		{
			if (result.lower_ <= best.lower_ && result.depth_ <= best.depth_)
				continue;
			if (result.lower_ < best.lower_ && best.lower_ > EvalValue)
				continue;
			if (result.depth_ < best.depth_ && result.lower_ < EvalValue)
				continue;
		}
		bestThread = &t;
		best = result;
	}

	if (best.move_ == 0)
	{
		printf("info No best thread, choosing via hash");
		best.move_ = move_from_hash(threads[0].state_, 0);
	}
	if (best.move_ == 0)
	{
		printf("info No best thread or hash, choosing via root");
		best.move_ = *max_element(threads[0].own_.rootList_.begin(), threads[0].own_.rootList_.end());
	}

	// Best and Ponder moves are simply the PV moves
	UCIResponse_ retval = {
		best.move_,
		0,
		best.lower_
	};

	// See if we can provide a ponder from the hashtable
	PVariation pv = PVFromHash(retval.score, state_in, best.move_);
	retval.ponder = pv.line_.size() >= 2 ? pv.line_[1] : 0;

	uciReport(bestThread ? *bestThread : threads[0], threads[0].peeps_, pv);

	assert(retval.best);
	return retval;
}

UCIResponse_ getBestMove(vector<Thread_>& threads, const State_& state, const LimitInputs_& limits)
{
	// Initialize each Thread in the Thread Pool. We need a reference
	// to the UCI seach parameters, access to the timing information,
	// somewhere to store the results of each iteration by the main, and
	// our own copy of the state. Also, we reset the seach statistics

	for (auto& thread : threads)
	{
		thread.state_.Reset(state);
		init_search(&thread.own_, &thread.state_, false, false);

		// Reset the accumulator stack. The table can remain
		//threads[i].nnue->current = &threads[i].nnue->stack[0];
		//threads[i].nnue->current->accurate[WHITE] = 0;
		//threads[i].nnue->current->accurate[BLACK] = 0;

		// memset(threads[i].nodeStates, 0, sizeof(NodeState) * STACK_SIZE);
	}

	// Allow Syzygy to refine the move list for optimal results
	// if (!limits->limitedByMoves && limits->multiPV == 1)
	//	tablebasesProbeDTZ(state, limits);

	// Create a new thread for each of the helpers and reuse the current
	// thread for the main thread, which avoids some overhead and saves
	// us from having the current thread eating CPU time while waiting
	vector<unique_ptr<thread>> pthreads;
	for (int i = 1; i < threads.size(); i++)
		pthreads.emplace_back(new thread(&iterativeDeepening, &threads[i], limits));
	iterativeDeepening(&threads[0], limits);

	// When the main thread exits it should signal for the helpers to
	// shutdown. Wait until all helpers have finished before moving on
	stop();
	for (auto& p : pthreads)
		p->join();

	// Pick the best of our completed threads
	return select_from_threads(threads, state);
}


void start_search_threads(vector<Thread_>* threads_in, const State_* state_in, const LimitInputs_* limits_in)
{
	auto& threads = *threads_in;
	const auto& state = *state_in;
	const auto& limits = *limits_in;

	static uint64 nodesSofar = 0;
	static double elapsedSofar = 0.0;

	SetTimeLimit(limits);	// set TheTimeLimit
	++TheShare.date_; // age the hash contents
	// Execute search, setting best and ponder moves
	auto uciMove = getBestMove(threads, state, limits);
	assert(uciMove.best);

	// UCI spec does not want reports until out of pondering
	// while (IS_PONDERING);
	
	elapsedSofar += millisecs(TheTimeLimit.start_, now());
	uint64 nodes = 0;
	for (const auto& t : threads)
		nodes += t.state_.nodes_;
	nodesSofar += nodes;
	int nps = (int)(1000 * (nodesSofar / (1 + elapsedSofar)));
	printf("info nodes %llu nps %d score cp %d\n", nodes, nps, uciMove.score / CP_SEARCH);

	// Report best move ( we should always have one )
	char str[6];
	move_to_string(uciMove.best, str);
	printf("bestmove %s score %d", str, uciMove.score / CP_SEARCH);
	TheShare.firstMove_ = false;
	TheShare.pvsScore_ = uciMove.score;
	if (TheShare.emaDepth_ > 0.0)
		TheShare.emaDepth_ += 0.2 * (TheShare.depth_ - TheShare.emaDepth_);
	else
		TheShare.emaDepth_ = TheShare.depth_;


	// Report ponder move ( if we have one )
	if (uciMove.ponder != 0) 
	{
		move_to_string(uciMove.ponder, str);
		printf(" ponder %s", str);
	}

	// Make sure this all gets reported
	printf("\n"); fflush(stdout);
}

thread* uciGo(vector<Thread_>& threads, State_& state, int multiPV, char* str)
{
	/// Parse the entire "go" command in order to fill out a Limits struct, found at ucigo->limits.
	/// After we have processed all of this, we can execute a new search thread, held by *pthread,
	/// and detach it.
	TheTimeLimit.start_ = now();
	int wtime = 0, btime = 0;
	int winc = 0, binc = 0, mtg = -1;

	char moveStr[6];
	char* ptr = strtok(str, " ");

	auto turn = state.current_->turn;
	(turn ? gen_root_moves<1> : gen_root_moves<0>)(&state);
	int idx = 0;

	LimitInputs_ limits = {};
	// memset(limits, 0, sizeof(Limits_));

	for (ptr = strtok(NULL, " "); ptr != NULL; ptr = strtok(NULL, " "))
	{
		// Parse time control conditions
		if (strEquals(ptr, "wtime")) wtime = atoi(strtok(NULL, " "));
		if (strEquals(ptr, "btime")) btime = atoi(strtok(NULL, " "));
		if (strEquals(ptr, "winc")) winc = atoi(strtok(NULL, " "));
		if (strEquals(ptr, "binc")) binc = atoi(strtok(NULL, " "));
		if (strEquals(ptr, "movestogo")) mtg = atoi(strtok(NULL, " "));

		// Parse special search termination conditions
		if (strEquals(ptr, "depth")) limits.depthLimit = atoi(strtok(NULL, " "));
		if (strEquals(ptr, "movetime")) limits.timeLimit = atoi(strtok(NULL, " "));
		if (strEquals(ptr, "nodes")) limits.nodeLimit = static_cast<uint64>(atof(strtok(NULL, " ")));

		// Parse special search modes
		if (strEquals(ptr, "infinite")) limits.limitedByNone = TRUE;
		if (strEquals(ptr, "searchmoves")) limits.limitedByMoves = TRUE;
		// if (strEquals(ptr, "ponder")) IS_PONDERING = TRUE;

		// Parse any specific moves that we are to search
		for (auto m: RootList)
		{
			move_to_string(m, moveStr);
			if (strEquals(ptr, moveStr))
			{
				limits.searchMoves[idx++] = m & 0xFFFF;
				break;
			}
		}
	}

	// Special exit cases: Time, Depth, and Nodes
	limits.limitedByTime = limits.timeLimit != 0;
	limits.limitedByDepth = limits.depthLimit != 0;
	limits.limitedByNodes = limits.nodeLimit != 0;

	// No special case nor infinite, so we set our own time
	limits.limitedBySelf = !limits.depthLimit && !limits.timeLimit
			&& !limits.limitedByNone && !limits.nodeLimit;

	// Pick the time values for the colour we are playing as
	limits.time = (state.current_->turn == White) ? wtime : btime;
	limits.inc = (state.current_->turn == White) ? winc : binc;
	limits.mtg = (state.current_->turn == White) ? mtg : mtg;

	// Cap our MultiPV search based on the suggested or legal moves
	limits.multiPV = Min(multiPV, limits.limitedByMoves ? idx : static_cast<int>(RootList.size()));

	// Spawn a new thread to handle the search
	TheShare.stopAll_ = false;
	return new thread(&start_search_threads, &threads, &state, &limits);
}

unsigned tb_probe_force_init_fwd();
void uciSetOption(char* str, vector<Thread_>* threads)
{
	// Handle setting UCI options in Ethereal. Options include:
	//  Hash                : Size of the Transposition Table in Megabyes
	//  Threads             : Number of search threads to use
	//  EvalFile            : Network weights for Ethereal's NNUE evaluation
	//  MultiPV             : Number of search lines to report per iteration
	//  MoveOverhead        : Overhead on time allocation to avoid time losses
	//  SyzygyPath          : Path to Syzygy Tablebases
	//  SyzygyProbeDepth    : Minimal Depth to probe the highest cardinality Tablebase
	//  UCI_Chess960        : Set when playing FRC, but not required in order to work

	if (strStartsWith(str, "setoption name Hash value "))
	{
		int megabytes = atoi(str + strlen("setoption name Hash value "));
		ResizeHash(megabytes);
		printf("info string set Hash to %dMB\n", megabytes);
	}

	if (strStartsWith(str, "setoption name Threads value ")) {
		int nthreads = atoi(str + strlen("setoption name Threads value "));
		threads->resize(nthreads);
		populateThreadPool(threads);	// initializes each state
		printf("info string set Threads to %d\n", nthreads);
	}

	if (strStartsWith(str, "setoption name SyzygyPath value ")) {
		char* ptr = str + strlen("setoption name SyzygyPath value ");
		if (!strStartsWith(ptr, "<empty>"))
		{
			SETTINGS.tbPath = ptr;
			tb_init(ptr);
			//auto res = tb_probe_force_init_fwd();
			//printf("info tb init %d\n", res);
		}
		else
		{
			SETTINGS.tbPath.clear();
		}
		printf("info string set SyzygyPath to %s\n", ptr);
	}

	if (strStartsWith(str, "setoption name SyzygyProbeDepth value ")) {
		TBMinDepth = atoi(str + strlen("setoption name SyzygyProbeDepth value "));
		printf("info string set SyzygyProbeDepth to %u\n", TBMinDepth);
	}

	fflush(stdout);
}


int main(int argc, char** argv)
{
	State_ state;
	char str[8192] = { 0 };
	unique_ptr<thread> pthreadsgo;
	bool multiPV = false;
	TheShare.stopAll_ = true;
	TheShare.emaDepth_ = 0.0;

	init_data(&DATA);

	// Create the UCI-board and our threads
	vector<Thread_> threads(1);
	populateThreadPool(&threads);	// initializes the one state to startpos

	// no command line control

	/*
	|------------|-----------------------------------------------------------------------|
	|  Commands  | Response. * denotes that the command blocks until no longer searching |
	|------------|-----------------------------------------------------------------------|
	|        uci |           Outputs the engine name, authors, and all available options |
	|    isready | *           Responds with readyok when no longer searching a position |
	| ucinewgame | *  Resets the TT and any Hueristics to ensure determinism in searches |
	|  setoption | *     Sets a given option and reports that the option was set if done |
	|   position | *  Sets the board position via an optional FEN and optional move list |
	|         go | *       Searches the current position with the provided time controls |
	|  ponderhit |          Flags the search to indicate that the ponder move was played |
	|       stop |            Signals the search threads to finish and report a bestmove |
	|       quit |             Exits the engine and any searches by killing the UCI loop |
	|      perft |            Custom command to compute PERFT(N) of the current position |
	|      print |         Custom command to print an ASCII view of the current position |
	|------------|-----------------------------------------------------------------------|
	*/

	while (getInput(str))
	{
		if (strEquals(str, "uci")) {
			printf("id name Roc "); printf(Version::now); printf("\n");
			printf("id author Demichev, Grant, Hyer\n");
			printf("option name Hash type spin default 16 min 2 max 131072\n");
			printf("option name Threads type spin default 1 min 1 max 2048\n");
			printf("option name SyzygyPath type string default <empty>\n");
			printf("option name SyzygyProbeDepth type spin default 0 min 0 max 127\n");
			printf("option name Ponder type check default false\n");
			printf("uciok\n"), fflush(stdout);
		}

		else if (strEquals(str, "isready"))
		{
			while (!TheShare.stopAll_)
			{ 
				printf("info not ready, still working\n");
				this_thread::sleep_for(chrono::seconds(1));
			}
			printf("readyok\n"), fflush(stdout);
		}

		else if (strEquals(str, "ucinewgame"))
			resetThreadPool(&threads, true);

		else if (strStartsWith(str, "setoption"))
			uciSetOption(str, &threads);

		else if (strStartsWith(str, "position"))
			get_position(str, &state);

		else if (strStartsWith(str, "go"))
		{
			pthreadsgo.reset(uciGo(threads, state, multiPV, str));
			pthreadsgo->detach();   // maybe not needed?
		}

		//else if (strEquals(str, "ponderhit"))
		//	IS_PONDERING = 0;

		else if (strEquals(str, "stop"))
			stop();  // , IS_PONDERING = 0;

		else if (strEquals(str, "quit"))
			break;

		//else if (strStartsWith(str, "perft"))
		//	cout << perft(&board, atoi(str + strlen("perft "))) << endl;

		//else if (strStartsWith(str, "print"))
		//	printBoard(&board), fflush(stdout);
	}

	return 0;
}

unsigned PyrrhicWDL(const State_& state, int depth)
{
	// Never take a Syzygy Probe in a Root node, in a node with Castling rights or en passant,
	// in a node which was not just zero'ed by a Pawn Move or Capture
	if (state.Height() == 0 || state.current_->castle_flags || state.current_->ply || state.current_->ep_square)
		return TB_RESULT_FAILED;

	const Board_& board = state.board_;
	uint64 white = board.Piece(White);
	uint64 black = board.Piece(Black);
	auto pop = popcount(white | black);

	// Apply TB_PROBE_DEPTH only at the maximum popcount
	if (pop > static_cast<int>(TB_LARGEST) || (pop == TB_LARGEST && depth < TBMinDepth))
		return TB_RESULT_FAILED;

	// Tap into Pyrrhic's API. Pyrrhic takes the state representation, followed
	// by the enpass square (0 if none set), and the turn. Pyrrhic defines WHITE
	// as 1, and BLACK as 0, which is the opposite of how Ethereal defines them

	return tb_probe_wdl(white, black, board.King(White) | board.King(Black),
		    board.Queen(White) | board.Queen(Black), board.Rook(White) | board.Rook(Black),
			board.Bishop(White) | board.Bishop(Black), board.Knight(White) | board.Knight(Black),
		    board.Pawn(White) | board.Pawn(Black), 0, state.current_->turn ^ 1);
}

unsigned tb_probe_force_init_fwd()
{
	return tb_probe_wdl(0x80, 0x0120, 0xA0, 0, 0, 0, 0, 0x0100, 25, false);
}


#endif

