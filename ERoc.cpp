
#ifdef BE_ETHEREAL

/// Roc and Platform
#include "Base/Platform.h"
#include <array>
#include "Chess/Chess.h"
#include "Chess/Bit.h"
#include "Chess/Pack.h"
#include "Chess/Array.h"
#include "Chess/Board.h"
#include "Chess/Score.h"
#include "Chess/Killer.h"
#include "Chess/Material.h"
#include "Chess/Eval.h"

INLINE constexpr packed_t EPack(sint16 op, sint16 eg)
{
    return Pack((11 * op + eg) / 12, (op + eg) / 2, (op + 11 * eg) / 12, 0);
}



using std::array;

#pragma warning(disable: 4996)

// config

#define USE_NNUE 0
#define USE_AVX2 1

/// types.h

#include <cassert>
#include <cstdio>
#include <cstdint>
#include <cctype>
#include <memory>
#include <intrin.h>
#include <chrono>
#include <thread>
#include <iostream>
#undef assert
#define assert(x)

constexpr int FALSE = 0, TRUE = 1;
enum { MG, EG, N_PHASES };
constexpr int OP_PHASE = 22, MG_PHASE = 12, EG_PHASE = 2;
enum { WHITE, BLACK, N_COLORS };
enum { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, N_PIECES };
constexpr int MAX_PLY = 128, MAX_MOVES = 256;

constexpr inline int ColoredPiece(int c, int p) { return c | (p << 2); }
constexpr int WHITE_PAWN = ColoredPiece(WHITE, PAWN);
constexpr int BLACK_PAWN = ColoredPiece(BLACK, PAWN);
constexpr int WHITE_KNIGHT = ColoredPiece(WHITE, KNIGHT);
constexpr int BLACK_KNIGHT = ColoredPiece(BLACK, KNIGHT);
constexpr int WHITE_BISHOP = ColoredPiece(WHITE, BISHOP);
constexpr int BLACK_BISHOP = ColoredPiece(BLACK, BISHOP);
constexpr int WHITE_ROOK = ColoredPiece(WHITE, ROOK);
constexpr int BLACK_ROOK = ColoredPiece(BLACK, ROOK);
constexpr int WHITE_QUEEN = ColoredPiece(WHITE, QUEEN);
constexpr int BLACK_QUEEN = ColoredPiece(BLACK, QUEEN);
constexpr int WHITE_KING = ColoredPiece(WHITE, KING);
constexpr int BLACK_KING = ColoredPiece(BLACK, KING);
constexpr int EMPTY = 26;

constexpr array<int, 32> MakeMatIndices()
{
    array<int, 32> retval{};
    retval[WHITE_PAWN] = MatCodeWP;
    retval[BLACK_PAWN] = MatCodeBP;
    retval[WHITE_KNIGHT] = MatCodeWN;
    retval[BLACK_KNIGHT] = MatCodeBN;
    retval[WHITE_BISHOP] = MatCodeWL;
    retval[BLACK_BISHOP] = MatCodeBL;
    retval[WHITE_ROOK] = MatCodeWR;
    retval[BLACK_ROOK] = MatCodeBR;
    retval[WHITE_QUEEN] = MatCodeWQ;
    retval[BLACK_QUEEN] = MatCodeBQ;
    return retval;
}
constexpr array<int, 32> MatIndices = MakeMatIndices();

constexpr int MATE_IN_MAX = 32000, MATE = MATE_IN_MAX + MAX_PLY;
constexpr int TBWIN_IN_MAX = 30976, TBWIN = TBWIN_IN_MAX + MAX_PLY;
constexpr int VALUE_NONE = MATE + 1;

constexpr int N_RANKS = 8, N_FILES = 8, N_SQUARES = N_RANKS * N_FILES;

constexpr inline int TypeOf(int piece) { return piece / 4; }
constexpr inline int ColorOf(int piece) { return piece % 4; }

constexpr inline int IsPiece(int piece) { return piece >= 0 && TypeOf(piece) < N_PIECES && ColorOf(piece) < N_COLORS; }

constexpr inline int makePiece(int type, int colour) {
    assert(0 <= type && type < N_PIECES);
    assert(0 <= colour && colour <= N_COLORS);
    return ColoredPiece(colour, type);
}

// Renamings, currently for move ordering

constexpr int N_CONTINUATION = 2;
using KillerMoves = array<uint16_t, N_KILLER>;
using KillerTable = array<KillerMoves, MAX_PLY + 1>;
using CounterMoveTable = array<array<array<uint16_t, N_SQUARES>, N_PIECES>, N_COLORS>;
using HistoryTable = array<array<array<array<array<score_t, N_SQUARES>, N_SQUARES>, 2>, 2>, N_COLORS>;
using CaptureHistoryTable = array<array<array<array<array<score_t, N_PIECES - 1>, N_SQUARES>, 2>, 2>, N_PIECES>;
using ContinuationTable = array<array<array<array<array<array<score_t, N_SQUARES>, N_PIECES>, N_CONTINUATION>, N_SQUARES>, N_PIECES>, 2>;

constexpr inline packed_t MakeScore(score_t mg, score_t eg) { return EPack(mg, eg); }
constexpr inline score_t ScoreOP(packed_t s) { return Pick16<1>(s); }
constexpr inline score_t ScoreMG(packed_t s) { return Pick16<2>(s); }
constexpr inline score_t ScoreEG(packed_t s) { return Pick16<3>(s); }


// Trivial alignment macros

#define ALIGN64 alignas(64)
#ifdef _MSC_VER
#define INLINE __forceinline
#define NOINLINE __declspec(noinline)
#define strtok_r strtok_s
void Prefetch1(const char* p)
{
    _mm_prefetch(p, _MM_HINT_T0);
}
template<int N> void Prefetch(const void* q)
{
    const char* p = reinterpret_cast<const char*>(q);
    //p -= reinterpret_cast<size_t>(p) & 63;
    for (int ii = 0; ii < N; ++ii)
        Prefetch1(p + 64 * ii);
}
#else
#define INLINE static inline __attribute__((always_inline))
#define NOINLINE __attribute__((noinline))
#endif


/// bitboards.h

constexpr uint64
    LONG_DIAGONALS = 0x8142241818244281ull,
    CENTER_SQUARES = 0x0000001818000000ull,
    CENTER_BIG = 0x00003C3C3C3C0000ull,

    LEFT_FLANK = File[0] | File[1] | File[2] | File[3],
    RIGHT_FLANK = File[4] | File[5] | File[6] | File[7],

    PROMOTION_RANKS = Line[0] | Line[7];

constexpr array<int, 8> MIRROR_FILE = { 0, 1, 2, 3, 3, 2, 1, 0 };


/// bitboards.c

constexpr int mirrorFile(int file) {
    assert(0 <= file && file < N_FILES);
    return MIRROR_FILE[file];
}

constexpr int rankOf(int sq) {
    assert(0 <= sq && sq < N_SQUARES);
    return RankOf(sq);
}

constexpr int square(int rank, int file) {
    assert(0 <= rank && rank < N_RANKS);
    assert(0 <= file && file < N_FILES);
    return rank * N_FILES + file;
}

template<int US> constexpr int RelativeSquare(int sq) 
{
    static_assert(0 <= US && US < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return square(OwnRankOf<US>(sq), FileOf(sq));
}
INLINE int relativeSquare(int colour, int sq)
{
    return (colour == WHITE ? RelativeSquare<WHITE> : RelativeSquare<BLACK>)(sq);
}

template<int US> constexpr int RelativeSquare32(int sq) 
{
    static_assert(0 <= US && US < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return 4 * OwnRankOf<US>(sq) + mirrorFile(FileOf(sq));
}

constexpr void setBit(uint64* bb, int i) {
    assert(!HasBit(*bb, i));
    *bb ^= Bit(i);
}

uint64 squaresOfMatchingColour(int sq) {
    assert(0 <= sq && sq < N_SQUARES);
    return HasBit(LightArea, sq) ? LightArea : DarkArea;
}

int popcount(uint64 bb) {
#ifdef _MSC_VER
    return static_cast<int>(_mm_popcnt_u64(bb));
#else
    return __builtin_popcountll(bb);
#endif
}

int frontmost(int colour, uint64 bb) {
    assert(0 <= colour && colour < N_COLORS);
    return colour == WHITE ? msb(bb) : lsb(bb);
}

int backmost(int colour, uint64 bb) {
    assert(0 <= colour && colour < N_COLORS);
    return colour == WHITE ? lsb(bb) : msb(bb);
}

inline int poplsb(uint64* bb) {
    int retval = lsb(*bb);
    *bb &= *bb - 1;
    return retval;
}

int popmsb(uint64* bb) {
    int retval = msb(*bb);
    *bb ^= 1ull << retval;
    return retval;
}

void printBitboard(uint64 bb) 
{
    for (int rank = 7; rank >= 0; rank--) {
        char line[] = ". . . . . . . .";

        for (int file = 0; file < N_FILES; file++)
            if (HasBit(bb, square(rank, file)))
                line[2 * file] = 'X';

        printf("%s\n", line);
    }

    printf("\n");
}

/// PSQT from evaluate.c

/* Piece Square Evaluation Terms */

#define S MakeScore

using PSQVals = array<packed_t, N_SQUARES>;

constexpr PSQVals PawnPSQT = {
    S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0),
    S(-13,   7), S(-4,   0), S(1,   4), S(6,   1), S(3,  10), S(-9,   4), S(-9,   3), S(-16,   7),
    S(-21,   5), S(-17,   6), S(-1,  -6), S(12, -14), S(8, -10), S(-4,  -5), S(-15,   7), S(-24,  11),
    S(-14,  16), S(-21,  17), S(9, -10), S(10, -24), S(4, -22), S(4, -10), S(-20,  17), S(-17,  18),
    S(-15,  18), S(-18,  11), S(-16,  -8), S(4, -30), S(-2, -24), S(-18,  -9), S(-23,  13), S(-17,  21),
    S(-20,  48), S(-9,  44), S(1,  31), S(17,  -9), S(36,  -6), S(-9,  31), S(-6,  45), S(-23,  49),
    S(-33, -70), S(-66,  -9), S(-16, -22), S(65, -23), S(41, -18), S(39, -14), S(-47,   4), S(-62, -51),
    S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0), S(0,   0),
};

constexpr PSQVals KnightPSQT = {
    S(-31, -38), S(-6, -24), S(-20, -22), S(-16,  -1), S(-11,  -1), S(-22, -19), S(-8, -20), S(-41, -30),
    S(1,  -5), S(-11,   3), S(-6, -19), S(-1,  -2), S(0,   0), S(-9, -16), S(-8,  -3), S(-6,   1),
    S(7, -21), S(8,  -5), S(7,   2), S(10,  19), S(10,  19), S(4,   2), S(8,  -4), S(3, -19),
    S(16,  21), S(17,  30), S(23,  41), S(27,  50), S(24,  53), S(23,  41), S(19,  28), S(13,  26),
    S(13,  30), S(23,  30), S(37,  51), S(30,  70), S(26,  67), S(38,  50), S(22,  33), S(14,  28),
    S(-24,  25), S(-5,  37), S(25,  56), S(22,  60), S(27,  55), S(29,  55), S(-1,  32), S(-19,  25),
    S(13,  -2), S(-11,  18), S(27,  -2), S(37,  24), S(41,  24), S(40,  -7), S(-13,  16), S(2,  -2),
    S(-167,  -5), S(-91,  12), S(-117,  41), S(-38,  17), S(-18,  19), S(-105,  48), S(-119,  24), S(-165, -17),
};

constexpr PSQVals BishopPSQT = {
    S(5, -21), S(1,   1), S(-1,   5), S(1,   5), S(2,   8), S(-6,  -2), S(0,   1), S(4, -25),
    S(26, -17), S(2, -31), S(15,  -2), S(8,   8), S(8,   8), S(13,  -3), S(9, -31), S(26, -29),
    S(9,   3), S(22,   9), S(-5,  -3), S(18,  19), S(17,  20), S(-5,  -6), S(20,   4), S(15,   8),
    S(0,  12), S(10,  17), S(17,  32), S(20,  32), S(24,  34), S(12,  30), S(15,  17), S(0,  14),
    S(-20,  34), S(13,  31), S(1,  38), S(21,  45), S(12,  46), S(6,  38), S(13,  33), S(-14,  37),
    S(-13,  31), S(-11,  45), S(-7,  23), S(2,  40), S(8,  38), S(-21,  34), S(-5,  46), S(-9,  35),
    S(-59,  38), S(-49,  22), S(-13,  30), S(-35,  36), S(-33,  36), S(-13,  33), S(-68,  21), S(-55,  35),
    S(-66,  18), S(-65,  36), S(-123,  48), S(-107,  56), S(-112,  53), S(-97,  43), S(-33,  22), S(-74,  15),
};

constexpr PSQVals RookPSQT = {
    S(-26,  -1), S(-21,   3), S(-14,   4), S(-6,  -4), S(-5,  -4), S(-10,   3), S(-13,  -2), S(-22, -14),
    S(-70,   5), S(-25, -10), S(-18,  -7), S(-11, -11), S(-9, -13), S(-15, -15), S(-15, -17), S(-77,   3),
    S(-39,   3), S(-16,  14), S(-25,   9), S(-14,   2), S(-12,   3), S(-25,   8), S(-4,   9), S(-39,   1),
    S(-32,  24), S(-21,  36), S(-21,  36), S(-5,  26), S(-8,  27), S(-19,  34), S(-13,  33), S(-30,  24),
    S(-22,  46), S(4,  38), S(16,  38), S(35,  30), S(33,  32), S(10,  36), S(17,  31), S(-14,  43),
    S(-33,  60), S(17,  41), S(0,  54), S(33,  36), S(29,  35), S(3,  52), S(33,  32), S(-26,  56),
    S(-18,  41), S(-24,  47), S(-1,  38), S(15,  38), S(14,  37), S(-2,  36), S(-24,  49), S(-12,  38),
    S(33,  55), S(24,  63), S(-1,  73), S(9,  66), S(10,  67), S(0,  69), S(34,  59), S(37,  56),
};

constexpr PSQVals QueenPSQT = {
    S(20, -34), S(4, -26), S(9, -34), S(17, -16), S(18, -18), S(14, -46), S(9, -28), S(22, -44),
    S(6, -15), S(15, -22), S(22, -42), S(13,   2), S(17,   0), S(22, -49), S(18, -29), S(3, -18),
    S(6,  -1), S(21,   7), S(5,  35), S(0,  34), S(2,  34), S(5,  37), S(24,   9), S(13, -15),
    S(9,  17), S(12,  46), S(-6,  59), S(-19, 109), S(-17, 106), S(-4,  57), S(18,  48), S(8,  33),
    S(-10,  42), S(-8,  79), S(-19,  66), S(-32, 121), S(-32, 127), S(-23,  80), S(-8,  95), S(-10,  68),
    S(-28,  56), S(-23,  50), S(-33,  66), S(-18,  70), S(-17,  71), S(-19,  63), S(-18,  65), S(-28,  76),
    S(-16,  61), S(-72, 108), S(-19,  65), S(-52, 114), S(-54, 120), S(-14,  59), S(-69, 116), S(-11,  73),
    S(8,  43), S(19,  47), S(0,  79), S(3,  78), S(-3,  89), S(13,  65), S(18,  79), S(21,  56),
};

constexpr PSQVals KingPSQT = {
    S(87, -77), S(67, -49), S(4,  -7), S(-9, -26), S(-10, -27), S(-8,  -1), S(57, -50), S(79, -82),
    S(35,   3), S(-27,  -3), S(-41,  16), S(-89,  29), S(-64,  26), S(-64,  28), S(-25,  -3), S(30,  -4),
    S(-44, -19), S(-16, -19), S(28,   7), S(0,  35), S(18,  32), S(31,   9), S(-13, -18), S(-36, -13),
    S(-48, -44), S(98, -39), S(71,  12), S(-22,  45), S(12,  41), S(79,  10), S(115, -34), S(-59, -38),
    S(-6, -10), S(95, -39), S(39,  14), S(-49,  18), S(-27,  19), S(35,  14), S(81, -34), S(-50, -13),
    S(24, -39), S(123, -22), S(105,  -1), S(-22, -21), S(-39, -20), S(74, -15), S(100, -23), S(-17, -49),
    S(0, -98), S(28, -21), S(7, -18), S(-3, -41), S(-57, -39), S(12, -26), S(22, -24), S(-15,-119),
    S(-16,-153), S(49, -94), S(-21, -73), S(-19, -32), S(-51, -55), S(-42, -62), S(53, -93), S(-58,-133),
};


/* Material Value Evaluation Terms */

constexpr packed_t PawnValue = S(82, 144);
constexpr packed_t KnightValue = S(426, 475);
constexpr packed_t BishopValue = S(441, 510);
constexpr packed_t RookValue = S(627, 803);
constexpr packed_t QueenValue = S(1292, 1623);
constexpr packed_t KingValue = S(0, 0);

#undef S

constexpr PSQVals NullPSQT = make_array<64>([](int) { return packed_t(0); });

constexpr array<PSQVals, 32> PSQT =
{
    make_array<64>([&](int sq) { return PawnValue + PawnPSQT[RelativeSquare<WHITE>(sq)]; }),
    make_array<64>([&](int sq) { return -PawnValue - PawnPSQT[RelativeSquare<BLACK>(sq)]; }),
    NullPSQT,
    NullPSQT,
    make_array<64>([&](int sq) { return KnightValue + KnightPSQT[RelativeSquare<WHITE>(sq)]; }),
    make_array<64>([&](int sq) { return -KnightValue - KnightPSQT[RelativeSquare<BLACK>(sq)]; }),
    NullPSQT,
    NullPSQT,
    make_array<64>([&](int sq) { return BishopValue + BishopPSQT[RelativeSquare<WHITE>(sq)]; }),
    make_array<64>([&](int sq) { return -BishopValue - BishopPSQT[RelativeSquare<BLACK>(sq)]; }),
    NullPSQT,
    NullPSQT,
    make_array<64>([&](int sq) { return RookValue + RookPSQT[RelativeSquare<WHITE>(sq)]; }),
    make_array<64>([&](int sq) { return -RookValue - RookPSQT[RelativeSquare<BLACK>(sq)]; }),
    NullPSQT,
    NullPSQT,
    make_array<64>([&](int sq) { return QueenValue + QueenPSQT[RelativeSquare<WHITE>(sq)]; }),
    make_array<64>([&](int sq) { return -QueenValue - QueenPSQT[RelativeSquare<BLACK>(sq)]; }),
    NullPSQT,
    NullPSQT,
    make_array<64>([&](int sq) { return KingValue + KingPSQT[RelativeSquare<WHITE>(sq)]; }),
    make_array<64>([&](int sq) { return -KingValue - KingPSQT[RelativeSquare<BLACK>(sq)]; }),
    NullPSQT,
    NullPSQT,
    NullPSQT,
    NullPSQT,
    NullPSQT,
    NullPSQT,
    NullPSQT,
    NullPSQT,
    NullPSQT,
    NullPSQT
};


/// zobrist.c

array<array<uint64, N_SQUARES>, 32> ZobristKeys;
array<uint64, N_FILES> ZobristEnpassKeys;
array<uint64, N_SQUARES> ZobristCastleKeys;
uint64 ZobristTurnKey;

uint64 rand64() 
{
    // http://vigna.di.unimi.it/ftp/papers/xorshift.pdf

    static uint64 seed = 1070372ull;

    seed ^= seed >> 12;
    seed ^= seed << 25;
    seed ^= seed >> 27;

    return seed * 2685821657736338717ull;
}

void initZobrist() 
{
    // Init the main Zobrist keys for all pieces
    for (int piece = PAWN; piece <= KING; piece++)
        for (int sq = 0; sq < N_SQUARES; sq++)
            for (int colour = WHITE; colour <= BLACK; colour++)
                ZobristKeys[makePiece(piece, colour)][sq] = rand64();

    // Init the Zobrist keys for each enpass file
    for (int file = 0; file < N_FILES; file++)
        ZobristEnpassKeys[file] = rand64();

    // Init the Zobrist keys for each castle rook
    for (int sq = 0; sq < N_SQUARES; sq++)
        ZobristCastleKeys[sq] = rand64();

    // Init the Zobrist key for side to move
    ZobristTurnKey = rand64();
}

/// move.h

constexpr uint16_t 
    NONE_MOVE = 0, NULL_MOVE = 11,

    NORMAL_MOVE = 0 << 12, CASTLE_MOVE = 1 << 12,
    ENPASS_MOVE = 2 << 12, PROMOTION_MOVE = 3 << 12,

    PROMOTE_TO_KNIGHT = 0 << 14, PROMOTE_TO_BISHOP = 1 << 14,
    PROMOTE_TO_ROOK = 2 << 14, PROMOTE_TO_QUEEN = 3 << 14,

    KNIGHT_PROMO_MOVE = PROMOTION_MOVE | PROMOTE_TO_KNIGHT,
    BISHOP_PROMO_MOVE = PROMOTION_MOVE | PROMOTE_TO_BISHOP,
    ROOK_PROMO_MOVE = PROMOTION_MOVE | PROMOTE_TO_ROOK,
    QUEEN_PROMO_MOVE = PROMOTION_MOVE | PROMOTE_TO_QUEEN
;

inline int MoveFrom(int move) { return ((move) >> 0) & 63; }
inline int MoveTo(int move) { return ((move) >> 6) & 63; }
inline int MoveType(int move) { return (move) & (3 << 12); }
inline int MovePromoType(int move) { return  (move) & (3 << 14); }
inline int MovePromoPiece(int move) { return  1 + ((move) >> 14); }
inline int MoveMake(int from, int to, int flag) { return from | (to << 6) | flag; }

constexpr array<const char*, N_COLORS> PieceLabel = { "PNBRQK", "pnbrqk" };

inline int castleKingTo(int king, int rook) {
    return square(rankOf(king), (rook > king) ? 6 : 2);
}

inline int castleRookTo(int king, int rook) {
    return square(rankOf(king), (rook > king) ? 5 : 3);
}


void squareToString(int sq, char* str) 
{
    // Helper for writing the enpass square, as well as for converting
    // a move into long algabraic notation. When there is not an enpass
    // square we will output a "-" as expected for a FEN

    assert(-1 <= sq && sq < N_SQUARES);

    if (sq == -1)
        *str++ = '-';
    else {
        *str++ = FileOf(sq) + 'a';
        *str++ = rankOf(sq) + '1';
    }

    *str++ = '\0';
}

void moveToString(uint16_t move, char* str, int chess960) 
{
    int from = MoveFrom(move), to = MoveTo(move);

    // FRC reports using KxR notation, but standard does not
    if (MoveType(move) == CASTLE_MOVE && !chess960)
        to = castleKingTo(from, to);

    // Encode squares (Long Algebraic Notation)
    squareToString(from, &str[0]);
    squareToString(to, &str[2]);

    // Add promotion piece label (Uppercase)
    if (MoveType(move) == PROMOTION_MOVE) {
        str[4] = PieceLabel[BLACK][MovePromoPiece(move)];
        str[5] = '\0';
    }
}

void printMove(uint16_t move, int chess960) {
    char str[6]; moveToString(move, str, chess960);
    printf("%s\n", str);
}



/// history.h

constexpr int HistoryDivisor = 16384;

/// movepicker.h


enum { NORMAL_PICKER, NOISY_PICKER };

enum {
    STAGE_TABLE,
    STAGE_GENERATE_NOISY, STAGE_GOOD_NOISY,
    STAGE_GENERATE_KILLER, STAGE_KILLER, 
    STAGE_COUNTER_MOVE,
    STAGE_GENERATE_QUIET, STAGE_QUIET,
    STAGE_BAD_NOISY,
    STAGE_DONE,
};


/// timeman.h

/// limits from uci.h
struct Limits {
    double start, time, inc, mtg, timeLimit;
    int limitedByNone, limitedByTime, limitedBySelf;
    int limitedByDepth, limitedByMoves, limitedByNodes;
    int multiPV, depthLimit; uint64 nodeLimit;
    uint16_t searchMoves[MAX_MOVES], excludedMoves[MAX_MOVES];
};



struct TimeManager {
    int pv_stability;
    double start_time, ideal_usage, max_usage;
    array<uint64, 0x1000> nodes;
};


/// search.h

struct PVariation {
    int length, score;
    uint16_t line[MAX_PLY];
};


constexpr int WindowDepth = 5;
constexpr int WindowSize = 10;
constexpr int WindowTimerMS = 2500;

constexpr int CurrmoveTimerMS = 2500;

constexpr int TTResearchMargin = 128;

constexpr int BetaPruningDepth = 8;
constexpr int BetaMargin = 75;

constexpr int AlphaPruningDepth = 5;
constexpr int AlphaMargin = 3000;

constexpr int NullMovePruningDepth = 2;

constexpr int ProbCutDepth = 5;
constexpr int ProbCutMargin = 100;

constexpr int FutilityPruningDepth = 8;
constexpr int FutilityMarginBase = 92;
constexpr int FutilityMarginPerDepth = 59;
constexpr int FutilityMarginNoHistory = 158;
constexpr array<int, 2> FutilityPruningHistoryLimit = { 12000, 6000 };

constexpr array<int, 2> ContinuationPruningDepth = { 3, 2 };
constexpr array<int, 2> ContinuationPruningHistoryLimit = { -1000, -2500 };

constexpr int LateMovePruningDepth = 8;

constexpr int SEEPruningDepth = 9;
constexpr int SEEQuietMargin = -64;
constexpr int SEENoisyMargin = -19;
constexpr int SEEPieceValues[] = {
     100,  450,  450,  675,
    1300,    0,    0,    0,
};

constexpr int QSSeeMargin = 110;
constexpr int QSDeltaMargin = 150;


/// state.h

struct Thread;

struct Board_
{
    array<uint8, N_SQUARES> at_;
    array<uint64, 3> colors_;
    array<uint64, 8> pieces_;

    INLINE uint64 Pawns() const { return pieces_[PAWN]; }
    INLINE uint64& Pawns() { return pieces_[PAWN]; }
    INLINE uint64 Pawns(int me) const { return pieces_[PAWN] & colors_[me]; }
    INLINE uint64 Knights() const { return pieces_[KNIGHT]; }
    INLINE uint64& Knights() { return pieces_[KNIGHT]; }
    INLINE uint64 Knights(int me) const { return pieces_[KNIGHT] & colors_[me]; }
    INLINE uint64 Bishops() const { return pieces_[BISHOP]; }
    INLINE uint64& Bishops() { return pieces_[BISHOP]; }
    INLINE uint64 Bishops(int me) const { return pieces_[BISHOP] & colors_[me]; }
    INLINE uint64 Rooks() const { return pieces_[ROOK]; }
    INLINE uint64& Rooks() { return pieces_[ROOK]; }
    INLINE uint64 Rooks(int me) const { return pieces_[ROOK] & colors_[me]; }
    INLINE uint64 Queens() const { return pieces_[QUEEN]; }
    INLINE uint64& Queens() { return pieces_[QUEEN]; }
    INLINE uint64 Queens(int me) const { return pieces_[QUEEN] & colors_[me]; }
    INLINE uint64 Kings() const { return pieces_[KING]; }
    INLINE uint64& Kings() { return pieces_[KING]; }
    INLINE uint64 Kings(int me) const { return pieces_[KING] & colors_[me]; }
};

struct State 
{
    Board_ board_;
    uint8_t castleMasks[N_SQUARES];
    uint64 hash, pkhash, kingAttackers, threats;
    uint64 castleRooks;
    packed_t psqtmat;
    int turn, epSquare, halfMoveCounter, fullMoveCounter;
    int numMoves, chess960, matIndex;
    uint64 history[MAX_MOVES];    // should be MAX_PLY + 100?
    Thread* thread;
};

struct Undo {
    uint64 hash, pkhash, kingAttackers, threats, castleRooks;
    packed_t psqtmat;
    int epSquare, halfMoveCounter, capturePiece, matIndex;
};


/// attacks.h

struct Magic {
    uint64 magic;
    uint64 mask;
    uint64 shift;
    uint64* offset;
};

// needed for Pyrrhic
inline uint64 pawnAttacks(int colour, int sq) { return PAtt[colour][sq]; }
inline uint64 knightAttacks(int sq) { return NAtt[sq]; }
uint64 bishopAttacks(int sq, uint64 occupied);
uint64 rookAttacks(int sq, uint64 occupied);
uint64 queenAttacks(int sq, uint64 occupied);
inline uint64 kingAttacks(int sq) { return KAtt[sq]; }

constexpr array<uint64, N_SQUARES> RookMagics = {
    0xA180022080400230ull, 0x0040100040022000ull, 0x0080088020001002ull, 0x0080080280841000ull,
    0x4200042010460008ull, 0x04800A0003040080ull, 0x0400110082041008ull, 0x008000A041000880ull,
    0x10138001A080C010ull, 0x0000804008200480ull, 0x00010011012000C0ull, 0x0022004128102200ull,
    0x000200081201200Cull, 0x202A001048460004ull, 0x0081000100420004ull, 0x4000800380004500ull,
    0x0000208002904001ull, 0x0090004040026008ull, 0x0208808010002001ull, 0x2002020020704940ull,
    0x8048010008110005ull, 0x6820808004002200ull, 0x0A80040008023011ull, 0x00B1460000811044ull,
    0x4204400080008EA0ull, 0xB002400180200184ull, 0x2020200080100380ull, 0x0010080080100080ull,
    0x2204080080800400ull, 0x0000A40080360080ull, 0x02040604002810B1ull, 0x008C218600004104ull,
    0x8180004000402000ull, 0x488C402000401001ull, 0x4018A00080801004ull, 0x1230002105001008ull,
    0x8904800800800400ull, 0x0042000C42003810ull, 0x008408110400B012ull, 0x0018086182000401ull,
    0x2240088020C28000ull, 0x001001201040C004ull, 0x0A02008010420020ull, 0x0010003009010060ull,
    0x0004008008008014ull, 0x0080020004008080ull, 0x0282020001008080ull, 0x50000181204A0004ull,
    0x48FFFE99FECFAA00ull, 0x48FFFE99FECFAA00ull, 0x497FFFADFF9C2E00ull, 0x613FFFDDFFCE9200ull,
    0xFFFFFFE9FFE7CE00ull, 0xFFFFFFF5FFF3E600ull, 0x0010301802830400ull, 0x510FFFF5F63C96A0ull,
    0xEBFFFFB9FF9FC526ull, 0x61FFFEDDFEEDAEAEull, 0x53BFFFEDFFDEB1A2ull, 0x127FFFB9FFDFB5F6ull,
    0x411FFFDDFFDBF4D6ull, 0x0801000804000603ull, 0x0003FFEF27EEBE74ull, 0x7645FFFECBFEA79Eull,
};

constexpr array<uint64, N_SQUARES> BishopMagics = {
    0xFFEDF9FD7CFCFFFFull, 0xFC0962854A77F576ull, 0x5822022042000000ull, 0x2CA804A100200020ull,
    0x0204042200000900ull, 0x2002121024000002ull, 0xFC0A66C64A7EF576ull, 0x7FFDFDFCBD79FFFFull,
    0xFC0846A64A34FFF6ull, 0xFC087A874A3CF7F6ull, 0x1001080204002100ull, 0x1810080489021800ull,
    0x0062040420010A00ull, 0x5028043004300020ull, 0xFC0864AE59B4FF76ull, 0x3C0860AF4B35FF76ull,
    0x73C01AF56CF4CFFBull, 0x41A01CFAD64AAFFCull, 0x040C0422080A0598ull, 0x4228020082004050ull,
    0x0200800400E00100ull, 0x020B001230021040ull, 0x7C0C028F5B34FF76ull, 0xFC0A028E5AB4DF76ull,
    0x0020208050A42180ull, 0x001004804B280200ull, 0x2048020024040010ull, 0x0102C04004010200ull,
    0x020408204C002010ull, 0x02411100020080C1ull, 0x102A008084042100ull, 0x0941030000A09846ull,
    0x0244100800400200ull, 0x4000901010080696ull, 0x0000280404180020ull, 0x0800042008240100ull,
    0x0220008400088020ull, 0x04020182000904C9ull, 0x0023010400020600ull, 0x0041040020110302ull,
    0xDCEFD9B54BFCC09Full, 0xF95FFA765AFD602Bull, 0x1401210240484800ull, 0x0022244208010080ull,
    0x1105040104000210ull, 0x2040088800C40081ull, 0x43FF9A5CF4CA0C01ull, 0x4BFFCD8E7C587601ull,
    0xFC0FF2865334F576ull, 0xFC0BF6CE5924F576ull, 0x80000B0401040402ull, 0x0020004821880A00ull,
    0x8200002022440100ull, 0x0009431801010068ull, 0xC3FFB7DC36CA8C89ull, 0xC3FF8A54F4CA2C89ull,
    0xFFFFFCFCFD79EDFFull, 0xFC0863FCCB147576ull, 0x040C000022013020ull, 0x2000104000420600ull,
    0x0400000260142410ull, 0x0800633408100500ull, 0xFC087E8E4BB2F736ull, 0x43FF9E4EF4CA2C89ull,
};

// Pyrrhic -- must see kingAttacks etc

extern int TB_LARGEST;   // Set by Pyrrhic in tb_init()
#include "pyrrhic/tbprobe.cpp"
using namespace std;    // only after pyrrhic



// these are from move.h


/// masks.h

/// masks.c

array<array<int, N_SQUARES>, N_SQUARES> DistanceBetween;
array<array<int, 1 << N_FILES>, N_FILES> KingPawnFileDistance;
array<array<uint64, N_SQUARES>, N_COLORS> KingAreaMasks, ForwardFileMasks, PassedPawnMasks, PawnConnectedMasks, OutpostSquareMasks;
array<uint64, N_FILES> AdjacentFilesMasks;
array<uint64, N_COLORS> OutpostRanksMasks;

int distanceBetween(int s1, int s2) {
    assert(0 <= s1 && s1 < N_SQUARES);
    assert(0 <= s2 && s2 < N_SQUARES);
    return DistanceBetween[s1][s2];
}

int kingPawnFileDistance(uint64 pawns, int ksq) {
    pawns |= pawns >> 8; pawns |= pawns >> 16; pawns |= pawns >> 32;
    assert(0 <= FileOf(ksq) && FileOf(ksq) < N_FILES);
    assert((pawns & 0xFF) < (1ull << N_FILES));
    return KingPawnFileDistance[FileOf(ksq)][pawns & 0xFF];
}

int openFileCount(uint64 pawns) {
    pawns |= pawns >> 8; pawns |= pawns >> 16; pawns |= pawns >> 32;
    return popcount(~pawns & 0xFF);
}

uint64 kingAreaMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return KingAreaMasks[colour][sq];
}

uint64 forwardRanksMasks(int colour, int rank) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= rank && rank < N_RANKS);
    return Forward[colour][rank] | Line[rank];
}

uint64 forwardFileMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return ForwardFileMasks[colour][sq];
}

uint64 adjacentFilesMasks(int file) {
    assert(0 <= file && file < N_FILES);
    return AdjacentFilesMasks[file];
}

uint64 passedPawnMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return PassedPawnMasks[colour][sq];
}

uint64 pawnConnectedMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return PawnConnectedMasks[colour][sq];
}

uint64 outpostSquareMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return OutpostSquareMasks[colour][sq];
}

uint64 outpostRanksMasks(int colour) {
    assert(0 <= colour && colour < N_COLORS);
    return OutpostRanksMasks[colour];
}

void initMasks()
{
    // Init a table for the distance between two given squares
    for (int sq1 = 0; sq1 < N_SQUARES; sq1++)
        for (int sq2 = 0; sq2 < N_SQUARES; sq2++)
            DistanceBetween[sq1][sq2] = Max(abs(FileOf(sq1) - FileOf(sq2)), abs(rankOf(sq1) - rankOf(sq2)));

    // Init a table to compute the distance between Pawns and Kings file-wise
    for (uint64 mask = 0ull; mask <= 0xFF; mask++)
    {
        for (int file = 0; file < N_FILES; file++)
        {
            // Look at only one side at a time by shifting off the other pawns
            uint64 left = (0xFFull & (mask << (N_FILES - file - 1))) >> (N_FILES - file - 1);
            uint64 right = (mask >> file) << file;

            // Find closest Pawn on each side. If no pawn, use "max" distance
            int ldist = left ? file - msb(left) : N_FILES - 1;
            int rdist = right ? lsb(right) - file : N_FILES - 1;

            // Take the min distance, unless there are no pawns, then use 0
            int dist = (left | right) ? Min(ldist, rdist) : 0;
            KingPawnFileDistance[file][mask] = dist;
        }
    }

    // Init a table for the King Areas. Use the King's square, the King's target
    // squares, and the squares within the pawn shield. When on the A/H files, extend
    // the King Area to include an additional file, namely the C and F file respectively
    for (int sq = 0; sq < N_SQUARES; sq++) 
    {
        KingAreaMasks[WHITE][sq] = kingAttacks(sq) | Bit(sq) | (kingAttacks(sq) << 8);
        KingAreaMasks[BLACK][sq] = kingAttacks(sq) | Bit(sq) | (kingAttacks(sq) >> 8);

        KingAreaMasks[WHITE][sq] |= FileOf(sq) != 0 ? 0ull : KingAreaMasks[WHITE][sq] << 1;
        KingAreaMasks[BLACK][sq] |= FileOf(sq) != 0 ? 0ull : KingAreaMasks[BLACK][sq] << 1;

        KingAreaMasks[WHITE][sq] |= FileOf(sq) != 7 ? 0ull : KingAreaMasks[WHITE][sq] >> 1;
        KingAreaMasks[BLACK][sq] |= FileOf(sq) != 7 ? 0ull : KingAreaMasks[BLACK][sq] >> 1;
    }

    // Init a table of bitmasks for the ranks at or above a given rank, by colour
    // Init a table of bitmasks for the squares on a file above a given square, by colour
    for (int sq = 0; sq < N_SQUARES; sq++) {
        ForwardFileMasks[WHITE][sq] = File[FileOf(sq)] & Forward[WHITE][rankOf(sq)];
        ForwardFileMasks[BLACK][sq] = File[FileOf(sq)] & Forward[BLACK][rankOf(sq)];
    }

    // Init a table of bitmasks containing the files next to a given file
    for (int file = 0; file < N_FILES; file++) 
    {
        AdjacentFilesMasks[file] = File[Max(0, file - 1)];
        AdjacentFilesMasks[file] |= File[Min(N_FILES - 1, file + 1)];
        AdjacentFilesMasks[file] &= ~File[file];
    }

    // Init a table of bitmasks to check if a given pawn has any opposition
    for (int colour = WHITE; colour <= BLACK; colour++)
        for (int sq = 0; sq < N_SQUARES; sq++)
            PassedPawnMasks[colour][sq] = ~forwardRanksMasks(!colour, rankOf(sq))
                    & (adjacentFilesMasks(FileOf(sq)) | File[FileOf(sq)]);

    // Init a table of bitmasks to check if a square is an outpost relative
    // to opposing pawns, such that no enemy pawn may attack the square with ease
    for (int colour = WHITE; colour <= BLACK; colour++)
        for (int sq = 0; sq < N_SQUARES; sq++)
            OutpostSquareMasks[colour][sq] = PassedPawnMasks[colour][sq] & ~File[FileOf(sq)];

    // Init a pair of bitmasks to check if a square may be an outpost, by colour
    OutpostRanksMasks[WHITE] = Line[3] | Line[4] | Line[5];
    OutpostRanksMasks[BLACK] = Line[2] | Line[3] | Line[4];

    // Init a table of bitmasks to check for supports for a given pawn
    for (int sq = 8; sq < 56; sq++) {
        PawnConnectedMasks[WHITE][sq] = pawnAttacks(BLACK, sq) | pawnAttacks(BLACK, sq + 8);
        PawnConnectedMasks[BLACK][sq] = pawnAttacks(WHITE, sq) | pawnAttacks(WHITE, sq - 8);
    }
}


/// network.h


#define PKNETWORK_INPUTS  (224)
#define PKNETWORK_LAYER1  ( 32)
#define PKNETWORK_OUTPUTS (  2)

typedef struct PKNetwork {

    // PKNetworks are of the form [Input, Hidden Layer 1, Output Layer]
    // Our current Network is [224x32, 32x1]. The Network is trained to
    // output a Score in CentiPawns for the Midgame and Endgame

    // We transpose the Input Weights matrix in order to get better
    // caching and memory lookups, since when computing we iterate
    // over only the ~20 Inputs set out of the 224 possible Inputs

    ALIGN64 float inputWeights[PKNETWORK_INPUTS][PKNETWORK_LAYER1];
    ALIGN64 float inputBiases[PKNETWORK_LAYER1];

    ALIGN64 float layer1Weights[PKNETWORK_OUTPUTS][PKNETWORK_LAYER1];
    ALIGN64 float layer1Biases[PKNETWORK_OUTPUTS];

} PKNetwork;


/// network.c


PKNetwork PKNN;

static array<string, 224> PKWeights = {
#include "weights/pknet_224x32x2.net"
    ""
};

inline int computePKNetworkIndex(int colour, int piece, int sq) 
{
    return (64 + 48) * colour + (48 * (piece == KING)) + sq - 8 * (piece == PAWN);
}


packed_t computePKNetwork(const Board_& board) 
{
    uint64 pawns = board.Pawns();
    uint64 kings = board.Kings();
    uint64 black = board.colors_[BLACK];

    float layer1Neurons[PKNETWORK_LAYER1];
    float outputNeurons[PKNETWORK_OUTPUTS];

    // Layer 1: Compute the values in the hidden Neurons of Layer 1
    // by looping over the Kings and Pawns bitboards, and applying
    // the weight which corresponds to each piece. We break the Kings
    // into two nearly duplicate steps, in order to more efficiently
    // set and update the Layer 1 Neurons initially

    { // Do one King first so we can set the Neurons
        int sq = poplsb(&kings);
        int idx = computePKNetworkIndex(HasBit(black, sq), KING, sq);
        for (int i = 0; i < PKNETWORK_LAYER1; i++)
            layer1Neurons[i] = PKNN.inputBiases[i] + PKNN.inputWeights[idx][i];
    }

    { // Do the remaining King as we would do normally
        int sq = poplsb(&kings);
        int idx = computePKNetworkIndex(HasBit(black, sq), KING, sq);
        for (int i = 0; i < PKNETWORK_LAYER1; i++)
            layer1Neurons[i] += PKNN.inputWeights[idx][i];
    }

    while (pawns) {
        int sq = poplsb(&pawns);
        int idx = computePKNetworkIndex(HasBit(black, sq), PAWN, sq);
        for (int i = 0; i < PKNETWORK_LAYER1; i++)
            layer1Neurons[i] += PKNN.inputWeights[idx][i];
    }

    // Layer 2: Trivially compute the Output layer. Apply a ReLU here.
    // We do not apply a ReLU in Layer 1, since we already know that all
    // of the Inputs in Layer 1 are going to be zeros or ones

    for (int i = 0; i < PKNETWORK_OUTPUTS; i++) {
        outputNeurons[i] = PKNN.layer1Biases[i];
        for (int j = 0; j < PKNETWORK_LAYER1; j++)
            if (layer1Neurons[j] >= 0.0)
                outputNeurons[i] += layer1Neurons[j] * PKNN.layer1Weights[i][j];
    }

    assert(PKNETWORK_OUTPUTS == N_PHASES);
    return MakeScore((int)outputNeurons[MG], (int)outputNeurons[EG]);
}

void initPKNetwork()
{
    for (int i = 0; i < PKNETWORK_LAYER1; i++)
    {
        string temp = PKWeights[i];
        temp.push_back(0);
        auto weights = &temp[0];
        strtok(weights, " ");

        for (int j = 0; j < PKNETWORK_INPUTS; j++)
            PKNN.inputWeights[j][i] = static_cast<float>(atof(strtok(NULL, " ")));
        PKNN.inputBiases[i] = static_cast<float>(atof(strtok(NULL, " ")));
    }

    for (int i = 0; i < PKNETWORK_OUTPUTS; i++)
    {
        string temp = PKWeights[i + PKNETWORK_LAYER1];
        temp.push_back(0);
        auto weights = &temp[0];
        strtok(weights, " ");

        for (int j = 0; j < PKNETWORK_LAYER1; j++)
            PKNN.layer1Weights[i][j] = static_cast<float>(atof(strtok(NULL, " ")));
        PKNN.layer1Biases[i] = static_cast<float>(atof(strtok(NULL, " ")));
    }
}



/// nnue/types.h


#if defined(USE_AVX2)
#include "archs/avx2.h"
#elif defined(USE_AVX)
#include "archs/avx.h"
#elif defined(USE_SSSE3)
#include "archs/ssse3.h"
#endif

constexpr int INSIZE = 20480, KPSIZE = 768, L1SIZE = 1536, L2SIZE = 8, L3SIZE = 32, OUTSIZE = 1;
constexpr int NUM_REGS = 16;

typedef struct NNUEDelta {
    int piece, from, to;
} NNUEDelta;

typedef struct NNUEAccumulator {
    int changes, accurate[N_COLORS];
    NNUEDelta deltas[3];
    ALIGN64 int16_t values[N_COLORS][KPSIZE];
} NNUEAccumulator;

typedef struct NNUEAccumulatorTableEntry {
    NNUEAccumulator accumulator;
    uint64 occupancy[N_COLORS][N_COLORS][N_PIECES - 1];
} NNUEAccumulatorTableEntry;

typedef struct NNUEEvaluator {
    NNUEAccumulator stack[MAX_PLY + 4];         // Each ply of search
    NNUEAccumulator* current;                   // Pointer of the current stack location
    NNUEAccumulatorTableEntry table[N_SQUARES]; // Finny table with Accumulators for each square
} NNUEEvaluator;


/// nnue/utils.h


#ifdef _MSC_VER

template<class T_> INLINE T_* align_malloc() {
    return reinterpret_cast<T_*>(_mm_malloc(sizeof(T_), 64));
}

INLINE void align_free(void* ptr) {
    _mm_free(ptr);
}

#else

INLINE void* align_malloc(size_t size) {
    void* mem; return posix_memalign(&mem, 64, size) ? NULL : mem;
}

INLINE void align_free(void* ptr) {
    free(ptr);
}

#endif

/// transposition.h

#if defined(__linux__)
#include <sys/mman.h>
#endif


/// The Transposition Table contains information from positions that have been
/// searched previously. Each entry contains a bound, a depth, an age, and some
/// additional Zobrist bits. An Entry may also contain a static evaluation for
/// the node, a search evaluation for the node, and a best move at that node.
///
/// Each Entry contains 10-bytes of information. We group together entries into
/// Buckets, containing three Entries a piece, as well as 2 additional bytes to
/// pad out the structure to 32-bytes. This gives us multiple options when we
/// run into a Zobrist collision with the Transposition Table lookup key.
///
/// Generally, we prefer to replace entries that came from previous searches,
/// as well as those which come from a lower depth. However, sometimes we do
/// not replace any such entry, if it would be too harmful to do so.
///
/// The minimum size of the Transposition Table is 2MB. This is so that we
/// can lookup the table with at least 16-bits, and so that we may align the
/// Table on a 2MB memory boundary, when available via the Operating System.

enum {
    BOUND_NONE = 0,
    BOUND_LOWER = 1,
    BOUND_UPPER = 2,
    BOUND_EXACT = 3,

    TT_MASK_BOUND = 0x03,
    TT_MASK_AGE = 0xFC,
    TT_BUCKET_NB = 3,
};

struct TTEntry {
    int8_t depth;
    uint8_t generation;
    int16_t eval, value;
    uint16_t move, hash16;
};

struct TTBucket {
    TTEntry slots[TT_BUCKET_NB];
    uint16_t padding;
};

struct TTable {
    vector<TTBucket> buckets;
    uint64 hashMask;
    uint8_t generation;
};

void tt_store(uint64 hash, int height, uint16_t move, int value, int eval, int depth, int bound);


struct MovePicker {
    int split, noisy_size, quiet_size, i_killer;
    int stage, type, threshold;
    int values[MAX_MOVES];
    uint16_t moves[MAX_MOVES];
    KillerMoves killers;
    uint16_t tt_move, counter;
};


/// The Pawn King table contains saved evaluations, and additional Pawn information
/// that is expensive to compute during evaluation. This includes the location of all
/// passed pawns, and Pawn-Shelter / Pawn-Storm scores for use in King Safety evaluation.
///
/// While this table is seldom accessed when using Ethereal NNUE, the table generally has
/// an extremely high, 95%+ hit rate, generating a substantial overall speedup to Ethereal.

enum {
    PK_CACHE_KEY_SIZE = 16,
    PK_CACHE_MASK = 0xFFFF,
    PK_CACHE_SIZE = 1 << PK_CACHE_KEY_SIZE,
};

struct PKEntry
{
    uint64 pkhash, passed;
    packed_t eval, safetyw, safetyb;
};
typedef array<PKEntry, PK_CACHE_SIZE>  PKTable;

/// thread.h

enum {
    STACK_OFFSET = 4,
    STACK_SIZE = MAX_PLY + STACK_OFFSET
};

struct NodeState 
{
    int eval;          // Static evaluation of the Node
    int movedPiece;    // Moving piece, otherwise UB
    int dextensions;   // Number of Double Extensions
    bool tactical;     // Cached moveIsTactical()
    uint16_t move;     // Move applied at the Node
    uint16_t excluded; // Excluded move during Singular Extensions
    MovePicker mp;     // Move Picker at each ply

    // Fast reference for future use for History lookups
    array<array<array<score_t, N_SQUARES>, N_PIECES>, N_CONTINUATION>* continuations;
};

struct Thread
{
    State state;
    Limits* limits;
    TimeManager* tm;
    PVariation pvs[MAX_PLY];
    PVariation mpvs[MAX_MOVES];

    int multiPV;
    uint16_t bestMoves[MAX_MOVES];

    uint64 nodes, tbhits;
    int depth, seldepth, height, completed;

    NNUEEvaluator* nnue;

    Undo undoStack[STACK_SIZE];
    NodeState* states, nodeStates[STACK_SIZE];

    ALIGN64 PKTable pktable;
    ALIGN64 KillerTable killers;
    ALIGN64 CounterMoveTable cmtable;
    ALIGN64 HistoryTable history;
    ALIGN64 CaptureHistoryTable chistory;
    ALIGN64 ContinuationTable continuation;

    size_t index, nthreads;
    Thread* threads;
};


/// Simple Pawn+King Evaluation Hash Table, which also stores some additional
/// safety information for use in King Safety, when not using NNUE evaluations

PKEntry* getCachedPawnKingEval(Thread* thread, const State* state) 
{
    PKEntry* pke = &thread->pktable[state->pkhash & PK_CACHE_MASK];
    return pke->pkhash == state->pkhash ? pke : NULL;
}

void storeCachedPawnKingEval(Thread* thread, const State* state, uint64 passed, packed_t eval, const array<packed_t, 2>& safety) 
{
    PKEntry& pke = thread->pktable[state->pkhash & PK_CACHE_MASK];
    pke = { state->pkhash, passed, eval, safety[WHITE], safety[BLACK] };
}




/// nnue/accumulator.h

extern ALIGN64 int16_t in_weights[INSIZE * KPSIZE];
extern ALIGN64 int16_t in_biases[KPSIZE];

INLINE NNUEEvaluator* nnue_create_evaluator() {

    NNUEEvaluator* nnue = align_malloc<NNUEEvaluator>();

#if USE_NNUE

    for (size_t i = 0; i < N_SQUARES; i++) {
        memset(nnue->table[i].occupancy, 0, sizeof(nnue->table[i].occupancy));
        memcpy(nnue->table[i].accumulator.values[WHITE], in_biases, sizeof(int16_t) * KPSIZE);
        memcpy(nnue->table[i].accumulator.values[BLACK], in_biases, sizeof(int16_t) * KPSIZE);
    }

#endif

    return nnue;
}

INLINE void nnue_delete_accumulators(NNUEEvaluator* ptr) {
    align_free(ptr);
}

INLINE void nnue_pop(State* state) 
{
    if (USE_NNUE && state->thread != NULL)
        --state->thread->nnue->current;
}

INLINE void nnue_push(State* state) 
{
    if (USE_NNUE && state->thread != NULL) {
        NNUEAccumulator* accum = ++state->thread->nnue->current;
        accum->accurate[WHITE] = accum->accurate[BLACK] = FALSE;
        accum->changes = 0;
    }
}

INLINE void nnue_move_piece(State* state, int piece, int from, int to) 
{
    if (USE_NNUE && state->thread != NULL) {
        NNUEAccumulator* accum = state->thread->nnue->current;
        accum->deltas[accum->changes++] = NNUEDelta{ piece, from, to };
    }
}

INLINE void nnue_add_piece(State* state, int piece, int sq) 
{
    nnue_move_piece(state, piece, N_SQUARES, sq);
}

INLINE void nnue_remove_piece(State* state, int piece, int sq) 
{
    if (piece != EMPTY)
        nnue_move_piece(state, piece, sq, N_SQUARES);
}


/// nnue.accumulator.c


constexpr inline int sq64_to_sq32(int sq) {
    constexpr int Mirror[] = { 3, 2, 1, 0, 0, 1, 2, 3 };
    return ((sq >> 1) & ~0x3) + Mirror[sq & 0x7];
}

int nnue_index(int piece, int relksq, int colour, int sq) 
{
    const int ptype = TypeOf(piece);
    const int pcolour = ColorOf(piece);
    const int relpsq = relativeSquare(colour, sq);

    const int mksq = HasBit(LEFT_FLANK, relksq) ? (relksq ^ 0x7) : relksq;
    const int mpsq = HasBit(LEFT_FLANK, relksq) ? (relpsq ^ 0x7) : relpsq;

    return 640 * sq64_to_sq32(mksq) + (64 * (5 * (colour == pcolour) + ptype)) + mpsq;
}

int nnue_can_update(NNUEAccumulator* accum, State* state, int colour) 
{
    // Search back through the tree to find an accurate accum
    while (accum != state->thread->nnue->stack) {

        // A King move prevents the entire tree from being updated
        if (accum->changes
            && accum->deltas[0].piece == makePiece(KING, colour))
            return FALSE;

        // Step back, since the root can't be accurate
        accum = accum - 1;

        // We found it, so we can update the entire tree
        if (accum->accurate[colour])
            return TRUE;
    }

    return FALSE;
}

void nnue_update_accumulator(NNUEAccumulator* accum, State* state, int colour, int relksq) 
{
    int add = 0, remove = 0;
    int add_list[3], remove_list[3];
    vepi16* inputs, * outputs, * weights, registers[NUM_REGS];

    // Recurse and update all out of our date parents
    if (!(accum - 1)->accurate[colour])
        nnue_update_accumulator((accum - 1), state, colour, relksq);

    // Determine the features that have changed, by looping through them
    for (NNUEDelta* x = &accum->deltas[0]; x < &accum->deltas[0] + accum->changes; x++) {

        // HalfKP does not concern with KxK relations
        if (TypeOf(x->piece) == KING)
            continue;

        // Moving or placing a Piece to a Square
        if (x->to != N_SQUARES)
            add_list[add++] = nnue_index(x->piece, relksq, colour, x->to);

        // Moving or deleting a Piece from a Square
        if (x->from != N_SQUARES)
            remove_list[remove++] = nnue_index(x->piece, relksq, colour, x->from);
    }

    for (int offset = 0; offset < KPSIZE; offset += NUM_REGS * vepi16_cnt) {

        outputs = (vepi16*)&(accum - 0)->values[colour][offset];
        inputs = (vepi16*)&(accum - 1)->values[colour][offset];

        for (int i = 0; i < NUM_REGS; i++)
            registers[i] = inputs[i];

        for (int i = 0; i < add; i++) {

            weights = (vepi16*)&in_weights[add_list[i] * KPSIZE + offset];

            for (int j = 0; j < NUM_REGS; j++)
                registers[j] = vepi16_add(registers[j], weights[j]);
        }

        for (int i = 0; i < remove; i++) {

            weights = (vepi16*)&in_weights[remove_list[i] * KPSIZE + offset];

            for (int j = 0; j < NUM_REGS; j++)
                registers[j] = vepi16_sub(registers[j], weights[j]);
        }

        for (int i = 0; i < NUM_REGS; i++)
            outputs[i] = registers[i];
    }

    accum->accurate[colour] = TRUE;
    return;
}

void nnue_refresh_accumulator(NNUEEvaluator* nnue, NNUEAccumulator* accum, State* state, int colour, int relsq) 
{
    vepi16* outputs, * weights, registers[NUM_REGS];
    const int ksq = lsb(state->board_.Kings(colour));
    NNUEAccumulatorTableEntry* entry = &nnue->table[ksq];

    int set_indexes[32], set_count = 0;
    int unset_indexes[32], unset_count = 0;

    for (int c = WHITE; c <= BLACK; c++) {

        for (int pt = PAWN; pt <= QUEEN; pt++) {

            uint64 pieces = state->board_.pieces_[pt] & state->board_.colors_[c];
            uint64 to_set = pieces & ~entry->occupancy[colour][c][pt];
            uint64 to_unset = entry->occupancy[colour][c][pt] & ~pieces;

            while (to_set)
                set_indexes[set_count++] = nnue_index(makePiece(pt, c), relsq, colour, poplsb(&to_set));

            while (to_unset)
                unset_indexes[unset_count++] = nnue_index(makePiece(pt, c), relsq, colour, poplsb(&to_unset));

            entry->occupancy[colour][c][pt] = pieces;
        }
    }

    for (int offset = 0; offset < KPSIZE; offset += NUM_REGS * vepi16_cnt) 
    {
        outputs = (vepi16*)&entry->accumulator.values[colour][offset];

        for (int i = 0; i < NUM_REGS; i++)
            registers[i] = outputs[i];

        for (int i = 0; i < set_count; i++) {

            weights = (vepi16*)&in_weights[set_indexes[i] * KPSIZE + offset];

            for (int j = 0; j < NUM_REGS; j++)
                registers[j] = vepi16_add(registers[j], weights[j]);
        }

        for (int i = 0; i < unset_count; i++) {

            weights = (vepi16*)&in_weights[unset_indexes[i] * KPSIZE + offset];

            for (int j = 0; j < NUM_REGS; j++)
                registers[j] = vepi16_sub(registers[j], weights[j]);
        }

        for (int i = 0; i < NUM_REGS; i++)
            outputs[i] = registers[i];
    }

    memcpy(accum->values[colour], entry->accumulator.values[colour], sizeof(int16_t) * KPSIZE);
    accum->accurate[colour] = TRUE;
}


/// attacks.c


#ifdef USE_PEXT
#include <immintrin.h>
#endif

ALIGN64 uint64 BishopAttacks[0x1480];
ALIGN64 uint64 RookAttacks[0x19000];

ALIGN64 Magic BishopTable[N_SQUARES];
ALIGN64 Magic RookTable[N_SQUARES];

inline int sliderIndex(uint64 occupied, Magic* table)
{
#ifdef USE_PEXT
    return _pext_u64(occupied, table->mask);
#else
    return static_cast<int>(((occupied & table->mask) * table->magic) >> table->shift);
#endif
}

inline int validCoordinate(int rank, int file)
{
    return 0 <= rank && rank < N_RANKS
        && 0 <= file && file < N_FILES;
}

inline void setSquare(uint64* bb, int rank, int file)
{
    if (validCoordinate(rank, file))
        *bb |= 1ull << square(rank, file);
}
void setSquare(State* state, int colour, int piece, int sq)
{
    // Generate a piece on the given square. This serves as an aid
    // to setting up the state from a FEN. We make sure update any
    // related hash values, as well as the PSQT + material values

    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= piece && piece < N_PIECES);
    assert(0 <= sq && sq < N_SQUARES);

    state->board_.at_[sq] = makePiece(piece, colour);
    setBit(&state->board_.colors_[colour], sq);
    setBit(&state->board_.pieces_[piece], sq);

    state->psqtmat += PSQT[state->board_.at_[sq]][sq];
    state->hash ^= ZobristKeys[state->board_.at_[sq]][sq];
    if (piece == PAWN || piece == KING)
        state->pkhash ^= ZobristKeys[state->board_.at_[sq]][sq];
}


uint64 sliderAttacks(int sq, uint64 occupied, const int delta[4][2])
{

    int rank, file, dr, df;
    uint64 result = 0ull;

    for (int i = 0; i < 4; i++) {

        dr = delta[i][0], df = delta[i][1];

        for (rank = rankOf(sq) + dr, file = FileOf(sq) + df; validCoordinate(rank, file); rank += dr, file += df) {
            setBit(&result, square(rank, file));
            if (HasBit(occupied, square(rank, file)))
                break;
        }
    }

    return result;
}

void initSliderAttacks(int sq, Magic* table, uint64 magic, const int delta[4][2])
{
    uint64 edges = ((Line[0] | Line[7]) & ~Line[rankOf(sq)])
        | ((File[0] | File[7]) & ~File[FileOf(sq)]);

    uint64 occupied = 0ull;

    // Init entry for the given square
    table[sq].magic = magic;
    table[sq].mask = sliderAttacks(sq, 0, delta) & ~edges;
    table[sq].shift = 64 - popcount(table[sq].mask);

    // Track the offset as we use up the table
    if (sq != N_SQUARES - 1)
        table[sq + 1].offset = table[sq].offset + (1ull << popcount(table[sq].mask));

    do { // Init attacks for all occupancy variations
        int index = sliderIndex(occupied, &table[sq]);
        table[sq].offset[index] = sliderAttacks(sq, occupied, delta);
        occupied = (occupied - table[sq].mask) & table[sq].mask;
    } while (occupied);
}


void initAttacks()
{
    const int PawnDelta[2][2] = { { 1,-1}, { 1, 1} };
    const int KnightDelta[8][2] = { {-2,-1}, {-2, 1}, {-1,-2}, {-1, 2},{ 1,-2}, { 1, 2}, { 2,-1}, { 2, 1} };
    const int KingDelta[8][2] = { {-1,-1}, {-1, 0}, {-1, 1}, { 0,-1},{ 0, 1}, { 1,-1}, { 1, 0}, { 1, 1} };
    const int BishopDelta[4][2] = { {-1,-1}, {-1, 1}, { 1,-1}, { 1, 1} };
    const int RookDelta[4][2] = { {-1, 0}, { 0,-1}, { 0, 1}, { 1, 0} };

    // First square has initial offset
    BishopTable[0].offset = BishopAttacks;
    RookTable[0].offset = RookAttacks;

    // Init attack tables for sliding pieces
    for (int sq = 0; sq < 64; sq++) {
        initSliderAttacks(sq, BishopTable, BishopMagics[sq], BishopDelta);
        initSliderAttacks(sq, RookTable, RookMagics[sq], RookDelta);
    }
}



template<int US> uint64 pawnAttacks(int sq) {
    static_assert(0 <= US && US < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return PAtt[US][sq];
}

uint64 bishopAttacks(int sq, uint64 occupied) {
    assert(0 <= sq && sq < N_SQUARES);
    return BishopTable[sq].offset[sliderIndex(occupied, &BishopTable[sq])];
}

uint64 rookAttacks(int sq, uint64 occupied) {
    assert(0 <= sq && sq < N_SQUARES);
    return RookTable[sq].offset[sliderIndex(occupied, &RookTable[sq])];
}

uint64 queenAttacks(int sq, uint64 occupied) {
    assert(0 <= sq && sq < N_SQUARES);
    return bishopAttacks(sq, occupied) | rookAttacks(sq, occupied);
}


uint64 pawnLeftAttacks(uint64 pawns, uint64 targets, int colour) {
    return targets & (colour == WHITE ? (pawns << 7) & ~File[7]
        : (pawns >> 7) & ~File[0]);
}

uint64 pawnRightAttacks(uint64 pawns, uint64 targets, int colour) {
    return targets & (colour == WHITE ? (pawns << 9) & ~File[0]
        : (pawns >> 9) & ~File[7]);
}

uint64 pawnAttackSpan(uint64 pawns, uint64 targets, int colour) {
    return pawnLeftAttacks(pawns, targets, colour)
        | pawnRightAttacks(pawns, targets, colour);
}

uint64 pawnAttackDouble(uint64 pawns, uint64 targets, int colour) {
    return pawnLeftAttacks(pawns, targets, colour)
        & pawnRightAttacks(pawns, targets, colour);
}

uint64 pawnAdvance(uint64 pawns, uint64 occupied, int colour) {
    return ~occupied & (colour == WHITE ? (pawns << 8) : (pawns >> 8));
}

uint64 pawnEnpassCaptures(uint64 pawns, int epsq, int colour) {
    return epsq == -1 ? 0ull : pawnAttacks(!colour, epsq) & pawns;
}



uint64 allAttackedSquares(const Board_& board, int colour)
{
    uint64 friendly = board.colors_[colour];
    uint64 occupied = board.colors_[!colour] | friendly;

    uint64 pawns = friendly & board.Pawns();
    uint64 knights = friendly & board.Knights();
    uint64 bishops = friendly & (board.Bishops() | board.Queens());
    uint64 rooks = friendly & (board.Rooks() | board.Queens());
    uint64 kings = friendly & board.Kings();

    uint64 threats = pawnAttackSpan(pawns, ~0ULL, colour);
    while (knights) threats |= knightAttacks(poplsb(&knights));
    while (bishops) threats |= bishopAttacks(poplsb(&bishops), occupied);
    while (rooks)   threats |= rookAttacks(poplsb(&rooks), occupied);
    while (kings)   threats |= kingAttacks(poplsb(&kings));

    return threats;
}

int squareIsAttacked(const Board_& board, int colour, int sq)
{
    uint64 enemy = board.colors_[!colour];
    uint64 occupied = board.colors_[colour] | enemy;

    uint64 enemyPawns = enemy & board.Pawns();
    uint64 enemyKnights = enemy & board.Knights();
    uint64 enemyBishops = enemy & (board.Bishops() | board.Queens());
    uint64 enemyRooks = enemy & (board.Rooks() | board.Queens());
    uint64 enemyKings = enemy & board.Kings();

    // Check for attacks to this square. While this function has the same
    // result as using attackersToSquare(state, colour, sq) != 0ull, this
    // has a better running time by avoiding some slider move lookups. The
    // speed gain is easily proven using the provided PERFT suite

    return (pawnAttacks(colour, sq) & enemyPawns)
        || (knightAttacks(sq) & enemyKnights)
        || (enemyBishops && (bishopAttacks(sq, occupied) & enemyBishops))
        || (enemyRooks && (rookAttacks(sq, occupied) & enemyRooks))
        || (kingAttacks(sq) & enemyKings);
}

uint64 allAttackersToSquare(const Board_& board, uint64 occupied, int sq)
{
    // When performing a static exchange evaluation we need to find all
    // attacks to a given square, but we also are given an updated occupied
    // bitboard, which will likely not match the actual state, as pieces are
    // removed during the iterations in the static exchange evaluation

    return (pawnAttacks(WHITE, sq) & board.Pawns(BLACK))
            | (pawnAttacks(BLACK, sq) & board.Pawns(WHITE))
            | (knightAttacks(sq) & board.Knights())
            | (bishopAttacks(sq, occupied) & (board.Bishops() | board.Queens()))
            | (rookAttacks(sq, occupied) & (board.Rooks() | board.Queens()))
            | (kingAttacks(sq) & board.Kings());
}

uint64 attackersToKingSquare(const State& state)
{
    // Wrapper for allAttackersToSquare() for use in check detection
    int kingsq = lsb(state.board_.colors_[state.turn] & state.board_.Kings());
    uint64 occupied = state.board_.colors_[WHITE] | state.board_.colors_[BLACK];
    return allAttackersToSquare(state.board_, occupied, kingsq) & state.board_.colors_[!state.turn];
}



/// move.c

array<uint64, 16> CornersToMask =
{
    0x0000000000000000ull,
    0x000000000000000Full,
    0x00000000000000F0ull,
    0x00000000000000FFull,
    0x0F00000000000000ull,
    0x0F0000000000000Full,
    0x0F000000000000F0ull,
    0x0F000000000000FFull,
    0xF000000000000000ull,
    0xF00000000000000Full,
    0xF0000000000000F0ull,
    0xF0000000000000FFull,
    0xFF00000000000000ull,
    0xFF0000000000000Full,
    0xFF000000000000F0ull,
    0xFF000000000000FFull
};

int CornerIndex(int sq)
{
    return (FileOf(sq) > 3 ? 1 : 0) + (RankOf(sq) > 3 ? 2 : 0);
}

template<bool KNOWN_UNUSUAL> int MatIndex(const Board_& board)
{
    int wp = popcnt(board.Pawns(WHITE));
    int bp = popcnt(board.Pawns(BLACK));
    int wn = popcnt(board.Knights(WHITE));
    int bn = popcnt(board.Knights(BLACK));
    int wl = popcnt(board.Bishops(WHITE) & LightArea);
    int bl = popcnt(board.Bishops(BLACK) & LightArea);
    int wd = popcnt(board.Bishops(WHITE) & DarkArea);
    int bd = popcnt(board.Bishops(BLACK) & DarkArea);
    int wr = popcnt(board.Rooks(WHITE));
    int br = popcnt(board.Rooks(BLACK));
    int wq = popcnt(board.Queens(WHITE));
    int bq = popcnt(board.Queens(BLACK));

    bool unusual = KNOWN_UNUSUAL || wn > 2 || bn > 2 || wl > 1 || bl > 1 || wd > 1 || bd > 1 || wr > 2 || br > 2 || wq > 2 || bq > 2;
    int retval = wp * MatCodeWP + bp * MatCodeBP + wn * MatCodeWN + bn * MatCodeBN + wl * MatCodeWL + bl * MatCodeBL + wd * MatCodeWD + bd * MatCodeBD + wr * MatCodeWR + br * MatCodeBR + wq * MatCodeWQ + bq * MatCodeBQ;
    return unusual ? retval | FlagUnusualMaterial : retval;
}

struct PerMaterial
{
    array<uint16, 2> scale;
    int phase;
    score_t matQuad;
};
array<PerMaterial, TotalMat> MaterialInfo;



inline void updateCastleZobrist(State* state, uint64 oldRooks, uint64 newRooks) 
{
    uint64 diff = oldRooks ^ newRooks;
    while (diff)
        state->hash ^= ZobristCastleKeys[poplsb(&diff)];
}

void applyNormalMove(State* state, uint16_t move, Undo* undo)
{
    const int from = MoveFrom(move);
    const int to = MoveTo(move);

    const int fromPiece = state->board_.at_[from];
    const int toPiece = state->board_.at_[to];

    const int fromType = TypeOf(fromPiece);
    const int toType = TypeOf(toPiece);
    const int toColour = ColorOf(toPiece);

    if (fromType == PAWN || toPiece != EMPTY)
        state->halfMoveCounter = 0;
    else
        state->halfMoveCounter += 1;

    state->board_.pieces_[fromType] ^= (1ull << from) ^ (1ull << to);
    state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << to);

    state->board_.pieces_[toType] ^= (1ull << to);
    state->board_.colors_[toColour] ^= (1ull << to);

    state->board_.at_[from] = EMPTY;
    state->board_.at_[to] = fromPiece;
    undo->capturePiece = toPiece;
    if (toPiece != EMPTY)
    {
        if (state->matIndex & FlagUnusualMaterial)
            state->matIndex = MatIndex<false>(state->board_);
        else  // capture never creates unusual material
            state->matIndex -= (toType == BISHOP && HasBit(DarkArea, to) ? 4 : 1) * MatIndices[toPiece];
    }

    state->castleRooks &= CornersToMask[state->castleMasks[from]];
    state->castleRooks &= CornersToMask[state->castleMasks[to]];
    updateCastleZobrist(state, undo->castleRooks, state->castleRooks);

    state->psqtmat += PSQT[fromPiece][to]
        - PSQT[fromPiece][from]
        - PSQT[toPiece][to];

    state->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[toPiece][to]
        ^ ZobristTurnKey;

    if (fromType == PAWN || fromType == KING)
        state->pkhash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to];

    if (toType == PAWN)
        state->pkhash ^= ZobristKeys[toPiece][to];

    if (fromType == PAWN && (to ^ from) == 16) 
    {
        uint64 enemyPawns = state->board_.Pawns(!state->turn)
                & adjacentFilesMasks(FileOf(from))
                & (state->turn == WHITE ? Line[3] : Line[4]);
        if (enemyPawns) {
            state->epSquare = state->turn == WHITE ? from + 8 : from - 8;
            state->hash ^= ZobristEnpassKeys[FileOf(from)];
        }
    }

    nnue_push(state);
    nnue_move_piece(state, fromPiece, from, to);
    nnue_remove_piece(state, toPiece, to);
}

void applyCastleMove(State* state, uint16_t move, Undo* undo) 
{
    const int from = MoveFrom(move);
    const int rFrom = MoveTo(move);

    const int to = castleKingTo(from, rFrom);
    const int rTo = castleRookTo(from, rFrom);

    const int fromPiece = makePiece(KING, state->turn);
    const int rFromPiece = makePiece(ROOK, state->turn);

    state->halfMoveCounter += 1;

    state->board_.Kings() ^= (1ull << from) ^ (1ull << to);
    state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << to);

    state->board_.Rooks() ^= (1ull << rFrom) ^ (1ull << rTo);
    state->board_.colors_[state->turn] ^= (1ull << rFrom) ^ (1ull << rTo);

    state->board_.at_[from] = EMPTY;
    state->board_.at_[rFrom] = EMPTY;

    state->board_.at_[to] = fromPiece;
    state->board_.at_[rTo] = rFromPiece;

    state->castleRooks &= CornersToMask[state->castleMasks[from]];
    updateCastleZobrist(state, undo->castleRooks, state->castleRooks);

    state->psqtmat += PSQT[fromPiece][to]
        - PSQT[fromPiece][from]
        + PSQT[rFromPiece][rTo]
        - PSQT[rFromPiece][rFrom];

    state->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[rFromPiece][rFrom]
        ^ ZobristKeys[rFromPiece][rTo]
        ^ ZobristTurnKey;

    state->pkhash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to];

    assert(TypeOf(fromPiece) == KING);

    undo->capturePiece = EMPTY;

    nnue_push(state);
    if (from != to) nnue_move_piece(state, fromPiece, from, to);
    if (rFrom != rTo) nnue_move_piece(state, rFromPiece, rFrom, rTo);
}

void applyEnpassMove(State* state, uint16_t move, Undo* undo) 
{
    const int from = MoveFrom(move);
    const int to = MoveTo(move);
    const int ep = to - 8 + (state->turn << 4);

    const int fromPiece = makePiece(PAWN, state->turn);
    const int enpassPiece = makePiece(PAWN, !state->turn);

    state->halfMoveCounter = 0;

    state->board_.Pawns() ^= (1ull << from) ^ (1ull << to);
    state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << to);

    state->board_.Pawns() ^= (1ull << ep);
    state->board_.colors_[!state->turn] ^= (1ull << ep);

    state->board_.at_[from] = EMPTY;
    state->board_.at_[to] = fromPiece;
    state->board_.at_[ep] = EMPTY;
    undo->capturePiece = enpassPiece;
    if (state->matIndex & FlagUnusualMaterial)
        state->matIndex = MatIndex<false>(state->board_);
    else  // capture never creates unusual material
        state->matIndex -= MatIndices[enpassPiece];

    state->psqtmat += PSQT[fromPiece][to]
        - PSQT[fromPiece][from]
        - PSQT[enpassPiece][ep];

    state->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[enpassPiece][ep]
        ^ ZobristTurnKey;

    state->pkhash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[enpassPiece][ep];

    assert(TypeOf(fromPiece) == PAWN);
    assert(TypeOf(enpassPiece) == PAWN);

    nnue_push(state);
    nnue_move_piece(state, fromPiece, from, to);
    nnue_remove_piece(state, enpassPiece, ep);
}

void applyPromotionMove(State* state, uint16_t move, Undo* undo) 
{
    const int from = MoveFrom(move);
    const int to = MoveTo(move);

    const int fromPiece = state->board_.at_[from];
    const int toPiece = state->board_.at_[to];
    const int promoPiece = makePiece(MovePromoPiece(move), state->turn);

    const int toType = TypeOf(toPiece);
    const int toColour = ColorOf(toPiece);
    const int promotype = MovePromoPiece(move);

    state->halfMoveCounter = 0;

    state->board_.Pawns() ^= (1ull << from);
    state->board_.pieces_[promotype] ^= (1ull << to);
    state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << to);

    state->board_.pieces_[toType] ^= (1ull << to);
    state->board_.colors_[toColour] ^= (1ull << to);
    bool unusual = promotype == BISHOP
            ? Multiple(state->board_.pieces_[promotype] & state->board_.colors_[state->turn] & (HasBit(DarkArea, to) ? DarkArea : LightArea))
            : popcnt(state->board_.pieces_[promotype] & state->board_.colors_[state->turn]) > 2;

    state->board_.at_[from] = EMPTY;
    state->board_.at_[to] = promoPiece;
    undo->capturePiece = toPiece;
    if ((state->matIndex & FlagUnusualMaterial) || unusual)
        state->matIndex = MatIndex<true>(state->board_);
    else
    {
        state->matIndex -= MatIndices[fromPiece];
        state->matIndex += (promotype == BISHOP && HasBit(DarkArea, to) ? 4 : 1) * MatIndices[promoPiece];
        state->matIndex -= (toType == BISHOP && HasBit(DarkArea, to) ? 4 : 1) * MatIndices[toPiece];
    }

    state->castleRooks &= CornersToMask[state->castleMasks[to]];
    updateCastleZobrist(state, undo->castleRooks, state->castleRooks);

    state->psqtmat += PSQT[promoPiece][to]
        - PSQT[fromPiece][from]
        - PSQT[toPiece][to];

    state->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[promoPiece][to]
        ^ ZobristKeys[toPiece][to]
        ^ ZobristTurnKey;

    state->pkhash ^= ZobristKeys[fromPiece][from];

    assert(TypeOf(fromPiece) == PAWN);
    assert(TypeOf(toPiece) != PAWN);
    assert(TypeOf(toPiece) != KING);

    nnue_push(state);
    nnue_remove_piece(state, fromPiece, from);
    nnue_remove_piece(state, toPiece, to);
    nnue_add_piece(state, promoPiece, to);
}

void applyNullMove(State* state, Undo* undo) 
{
    // Save information which is hard to recompute
    undo->hash = state->hash;
    undo->threats = state->threats;
    undo->epSquare = state->epSquare;
    undo->halfMoveCounter = state->halfMoveCounter++;

    // NULL moves simply swap the turn only
    state->turn = !state->turn;
    state->history[state->numMoves++] = state->hash;
    state->fullMoveCounter++;

    // Update the hash for turn and changes to enpass square
    state->hash ^= ZobristTurnKey;
    if (state->epSquare != -1) {
        state->hash ^= ZobristEnpassKeys[FileOf(state->epSquare)];
        state->epSquare = -1;
    }

    state->threats = allAttackedSquares(state->board_, !state->turn);
}

void applyMove(State* state, uint16_t move, Undo* undo)
{
    static void (*table[4])(State*, uint16_t, Undo*) = {
        applyNormalMove, applyCastleMove,
        applyEnpassMove, applyPromotionMove
    };

    // Save information which is hard to recompute
    undo->hash = state->hash;
    undo->pkhash = state->pkhash;
    undo->kingAttackers = state->kingAttackers;
    undo->threats = state->threats;
    undo->castleRooks = state->castleRooks;
    undo->epSquare = state->epSquare;
    undo->halfMoveCounter = state->halfMoveCounter;
    undo->psqtmat = state->psqtmat;
    undo->matIndex = state->matIndex;

    // Store hash history for repetition checking
    state->history[state->numMoves++] = state->hash;
    state->fullMoveCounter++;

    // Update the hash for before changing the enpass square
    if (state->epSquare != -1)
        state->hash ^= ZobristEnpassKeys[FileOf(state->epSquare)];

    // Run the correct move application function
    table[MoveType(move) >> 12](state, move, undo);
    if (!(state->matIndex & FlagUnusualMaterial))
        Prefetch<1>(&MaterialInfo[state->matIndex]);

    // No function updated epsquare so we reset
    if (state->epSquare == undo->epSquare)
        state->epSquare = -1;

    // No function updates this so we do it here
    state->turn = !state->turn;

    // Need king attackers for move generation
    state->kingAttackers = attackersToKingSquare(*state);

    // Need squares attacked by the opposing player
    state->threats = allAttackedSquares(state->board_, !state->turn);
}


void revertMove(State* state, uint16_t move, Undo* undo)
{
    const int to = MoveTo(move);
    const int from = MoveFrom(move);

    // Revert information which is hard to recompute
    state->hash = undo->hash;
    state->pkhash = undo->pkhash;
    state->kingAttackers = undo->kingAttackers;
    state->threats = undo->threats;
    state->castleRooks = undo->castleRooks;
    state->epSquare = undo->epSquare;
    state->halfMoveCounter = undo->halfMoveCounter;
    state->psqtmat = undo->psqtmat;
    state->matIndex = undo->matIndex;

    // Swap turns and update the history index
    state->turn = 1 ^ state->turn;
    state->numMoves--;
    state->fullMoveCounter--;

    // Update Accumulator pointer
    nnue_pop(state);

    if (MoveType(move) == NORMAL_MOVE) 
    {
        const int fromType = TypeOf(state->board_.at_[to]);
        const int toType = TypeOf(undo->capturePiece);
        const int toColour = ColorOf(undo->capturePiece);

        state->board_.pieces_[fromType] ^= (1ull << from) ^ (1ull << to);
        state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << to);

        state->board_.pieces_[toType] ^= (1ull << to);
        state->board_.colors_[toColour] ^= (1ull << to);

        state->board_.at_[from] = state->board_.at_[to];
        state->board_.at_[to] = undo->capturePiece;
    }

    else if (MoveType(move) == CASTLE_MOVE) 
    {
        const int rFrom = to;
        const int rTo = castleRookTo(from, rFrom);
        const int _to = castleKingTo(from, rFrom);

        state->board_.Kings() ^= (1ull << from) ^ (1ull << _to);
        state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << _to);

        state->board_.Rooks() ^= (1ull << rFrom) ^ (1ull << rTo);
        state->board_.colors_[state->turn] ^= (1ull << rFrom) ^ (1ull << rTo);

        state->board_.at_[_to] = EMPTY;
        state->board_.at_[rTo] = EMPTY;

        state->board_.at_[from] = makePiece(KING, state->turn);
        state->board_.at_[rFrom] = makePiece(ROOK, state->turn);
    }

    else if (MoveType(move) == PROMOTION_MOVE) 
    {
        const int toType = TypeOf(undo->capturePiece);
        const int toColour = ColorOf(undo->capturePiece);
        const int promotype = MovePromoPiece(move);

        state->board_.Pawns() ^= (1ull << from);
        state->board_.pieces_[promotype] ^= (1ull << to);
        state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << to);

        state->board_.pieces_[toType] ^= (1ull << to);
        state->board_.colors_[toColour] ^= (1ull << to);

        state->board_.at_[from] = makePiece(PAWN, state->turn);
        state->board_.at_[to] = undo->capturePiece;
    }

    else  // (MoveType(move) == ENPASS_MOVE)
    {
        assert(MoveType(move) == ENPASS_MOVE);

        const int ep = to - 8 + (state->turn << 4);

        state->board_.Pawns() ^= (1ull << from) ^ (1ull << to);
        state->board_.colors_[state->turn] ^= (1ull << from) ^ (1ull << to);

        state->board_.Pawns() ^= (1ull << ep);
        state->board_.colors_[!state->turn] ^= (1ull << ep);

        state->board_.at_[from] = state->board_.at_[to];
        state->board_.at_[to] = EMPTY;
        state->board_.at_[ep] = undo->capturePiece;
    }
}

void revertNullMove(State* state, Undo* undo) 
{
    // Revert information which is hard to recompute
    state->hash = undo->hash;
    state->threats = undo->threats;
    state->epSquare = undo->epSquare;
    state->halfMoveCounter = undo->halfMoveCounter;

    // NULL moves simply swap the turn only
    state->turn = !state->turn;
    state->numMoves--;
    state->fullMoveCounter--;
}

void revert(Thread* thread, State* state, uint16_t move) 
{
    if (move == NULL_MOVE)
        revertNullMove(state, &thread->undoStack[--thread->height]);
    else
        revertMove(state, move, &thread->undoStack[--thread->height]);
}


bool moveExaminedByMultiPV(Thread* thread, uint16_t move) 
{
    // Check to see if this move was already selected as the
    // best move in a previous iteration of this search depth

    for (int i = 0; i < thread->multiPV; i++)
        if (thread->bestMoves[i] == move)
            return true;

    return false;
}

bool moveIsInRootMoves(const Limits& limits, uint16_t move) 
{
    // We do two things: 1) Check to make sure we are not using a move which
    // has been flagged as excluded thanks to Syzygy probing. 2) Check to see
    // if we are doing a "go searchmoves <>"  command, in which case we have
    // to limit our search to the provided moves.

    for (int i = 0; i < MAX_MOVES; i++)
        if (move == limits.excludedMoves[i])
            return false;

    if (!limits.limitedByMoves)
        return true;

    for (int i = 0; i < MAX_MOVES; i++)
        if (move == limits.searchMoves[i])
            return true;

    return false;
}

bool moveIsTactical(const Board_& board, uint16_t move) 
{
    // We can use a simple bit trick since we assert that only
    // the enpass and promotion moves will ever have the 13th bit,
    // (ie 2 << 12) set. We use (2 << 12) in order to match move.h
    assert(ENPASS_MOVE & PROMOTION_MOVE & (2 << 12));
    assert(!((NORMAL_MOVE | CASTLE_MOVE) & (2 << 12)));

    // Check for captures, promotions, or enpassant. Castle moves may appear to be
    // tactical, since the King may move to its own square, or the rooks square
    return (board.at_[MoveTo(move)] != EMPTY && MoveType(move) != CASTLE_MOVE)
        || (move & ENPASS_MOVE & PROMOTION_MOVE);
}

int moveEstimatedValue(const Board_& board, uint16_t move) 
{
    // Start with the value of the piece on the target square
    int value = SEEPieceValues[TypeOf(board.at_[MoveTo(move)])];

    // Factor in the new piece's value and remove our promoted pawn
    if (MoveType(move) == PROMOTION_MOVE)
        value += SEEPieceValues[MovePromoPiece(move)] - SEEPieceValues[PAWN];

    // Target square is encoded as empty for enpass moves
    else if (MoveType(move) == ENPASS_MOVE)
        value = SEEPieceValues[PAWN];

    // We encode Castle moves as KxR, so the initial step is wrong
    else if (MoveType(move) == CASTLE_MOVE)
        value = 0;

    return value;
}

int moveBestCaseValue(const State& state) 
{
    // Assume the opponent has at least a pawn
    int value = SEEPieceValues[PAWN];
    uint64 mask = Filled;

    // Check for a potential pawn promotion
    if (state.board_.Pawns(state.turn) & (state.turn == WHITE ? Line[6] : Line[1]))
    {
        value = SEEPieceValues[QUEEN];
        mask = state.turn == WHITE ? Line[7] : Line[0];
    }

    // Check for a higher value target
    for (int piece = QUEEN; piece > PAWN; piece--)
        if (mask & state.board_.pieces_[piece] & state.board_.colors_[!state.turn])
        {
            value += SEEPieceValues[piece] - SEEPieceValues[PAWN]; 
            break;
        }

    return value;
}

int moveIsPseudoLegal(const State& state, uint16_t move)
{
    int from = MoveFrom(move);
    int type = MoveType(move);
    int ftype = TypeOf(state.board_.at_[from]);

    uint64 friendly = state.board_.colors_[state.turn];
    uint64 enemy = state.board_.colors_[!state.turn];
    uint64 castles = friendly & state.castleRooks;
    uint64 occupied = friendly | enemy;
    uint64 attacks, forward, mask;

    // Quick check against obvious illegal moves, such as our special move values,
    // moving a piece that is not ours, normal move and enpass moves that have bits
    // set which would otherwise indicate that the move is a castle or a promotion
    if ((move == NONE_MOVE || move == NULL_MOVE)
        || (ColorOf(state.board_.at_[from]) != state.turn)
        || (MovePromoType(move) != PROMOTE_TO_KNIGHT && type == NORMAL_MOVE)
        || (MovePromoType(move) != PROMOTE_TO_KNIGHT && type == ENPASS_MOVE))
        return 0;

    // Knight, Bishop, Rook, and Queen moves are legal so long as the
    // move type is NORMAL and the destination is an attacked square

    if (ftype == KNIGHT)
        return type == NORMAL_MOVE
        && HasBit(knightAttacks(from) & ~friendly, MoveTo(move));

    if (ftype == BISHOP)
        return type == NORMAL_MOVE
        && HasBit(bishopAttacks(from, occupied) & ~friendly, MoveTo(move));

    if (ftype == ROOK)
        return type == NORMAL_MOVE
        && HasBit(rookAttacks(from, occupied) & ~friendly, MoveTo(move));

    if (ftype == QUEEN)
        return type == NORMAL_MOVE
        && HasBit(queenAttacks(from, occupied) & ~friendly, MoveTo(move));

    if (ftype == PAWN) 
    {
        // Throw out castle moves with our pawn
        if (type == CASTLE_MOVE)
            return 0;

        // Look at the squares which our pawn threatens
        attacks = pawnAttacks(state.turn, from);

        // Enpass moves are legal if our to square is the enpass
        // square and we could attack a piece on the enpass square
        if (type == ENPASS_MOVE)
            return MoveTo(move) == state.epSquare && HasBit(attacks, MoveTo(move));

        // Compute simple pawn advances
        forward = pawnAdvance(1ull << from, occupied, state.turn);

        // Promotion moves are legal if we can move to one of the promotion
        // ranks, defined by PROMOTION_RANKS, independent of moving colour
        if (type == PROMOTION_MOVE)
            return HasBit(PROMOTION_RANKS & ((attacks & enemy) | forward), MoveTo(move));

        // Add the double advance to forward
        forward |= pawnAdvance(forward & (!state.turn ? Line[2] : Line[5]), occupied, state.turn);

        // Normal moves are legal if we can move there
        return HasBit(~PROMOTION_RANKS & ((attacks & enemy) | forward), MoveTo(move));
    }

    // The colour check should (assuming state.board_.at_ only contains
    // pieces and EMPTY flags) ensure that ftype is an actual piece,
    // which at this point the only piece left to check is the King
    assert(ftype == KING);

    // Normal moves are legal if the to square is a valid target
    if (type == NORMAL_MOVE)
        return HasBit(kingAttacks(from) & ~friendly, MoveTo(move));

    // Kings cannot enpass or promote
    if (type != CASTLE_MOVE)
        return 0;

    // Verifying a castle move can be difficult, so instead we will just
    // attempt to generate the (two) possible castle moves for the given
    // player. If one matches, we can then verify the pseudo legality
    // using the same code as from movegen.c

    while (castles && !state.kingAttackers) 
    {
        // Figure out which pieces are moving to which squares
        int rook = poplsb(&castles), king = from;
        int rookTo = castleRookTo(king, rook), kingTo = castleKingTo(king, rook);

        // Make sure the move actually matches what we have
        if (move != MoveMake(king, rook, CASTLE_MOVE)) continue;

        // Castle is illegal if we would go over a piece
        mask = Between[king][kingTo] | (1ull << kingTo);
        mask |= Between[rook][rookTo] | (1ull << rookTo);
        mask &= ~((1ull << king) | (1ull << rook));
        if (occupied & mask) return 0;

        // Castle is illegal if we move through a checking threat
        mask = Between[king][kingTo];
        while (mask)
            if (squareIsAttacked(state.board_, state.turn, poplsb(&mask)))
                return 0;

        return 1; // All requirments are met
    }

    return 0;
}

int moveWasLegal(const State& state) 
{
    // Grab the last player's King's square and verify safety
    int sq = lsb(state.board_.colors_[!state.turn] & state.board_.Kings());
    assert(state.board_.at_[sq] == makePiece(KING, !state.turn));
    return !squareIsAttacked(state.board_, !state.turn, sq);
}

int moveIsLegal(State* state, uint16_t move)
{
    if (!moveIsPseudoLegal(*state, move))
        return 0;

    Undo undo;
    applyMove(state, move, &undo);
    int legal = moveWasLegal(*state);
    revertMove(state, move, &undo);

    return legal;
}

TTable Table; // Global Transposition Table

/// Trivial helper functions to Transposition Table handleing

void tt_update() { Table.generation += TT_MASK_BOUND + 1; }
void tt_prefetch(uint64 hash) { Prefetch<2>(&Table.buckets[hash & Table.hashMask]); }



/// more move.c

int apply(Thread* thread, State* state, uint16_t move)
{
    NodeState* const ns = &thread->states[thread->height];

    // NULL moves are only tried when legal
    if (move == NULL_MOVE) {

        ns->movedPiece = EMPTY;
        ns->tactical = false;
        ns->continuations = NULL;
        ns->move = NULL_MOVE;

        // Prefetch the next tt-entry as soon as we have the Key
        applyNullMove(state, &thread->undoStack[thread->height]);
        tt_prefetch(state->hash);
    }
    else 
    {
        ns->movedPiece = TypeOf(state->board_.at_[MoveFrom(move)]);
        ns->tactical = moveIsTactical(state->board_, move);
        ns->continuations = &thread->continuation[ns->tactical][ns->movedPiece][MoveTo(move)];
        ns->move = move;

        // Prefetch the next tt-entry as soon as we have the Key
        applyMove(state, move, &thread->undoStack[thread->height]);
        tt_prefetch(state->hash);

        // Reject the move if it was illegal
        if (!moveWasLegal(*state))
            return revertMove(state, move, &thread->undoStack[thread->height]), 0;
    }

    // Advance the Stack before updating
    thread->height++;

    return 1;
}

void applyLegal(Thread* thread, State* state, uint16_t move)
{
    NodeState* const ns = &thread->states[thread->height];

    ns->movedPiece = TypeOf(state->board_.at_[MoveFrom(move)]);
    ns->tactical = moveIsTactical(state->board_, move);
    ns->continuations = &thread->continuation[ns->tactical][ns->movedPiece][MoveTo(move)];
    ns->move = move;

    // Assumed that this move is legal
    applyMove(state, move, &thread->undoStack[thread->height]);
    assert(moveWasLegal(*state));

    // Advance the Stack before updating
    thread->height++;
}




/// history.c

inline int stat_bonus(int depth) {

    // Approximately verbatim stat bonus formula from Stockfish
    return depth > 13 ? 32 : 16 * depth * depth + 128 * Max(depth - 1, 0);
}

inline void update_history(score_t* current, int depth, bool good)
{
    // HistoryDivisor is essentially the max value of history
    const int delta = good ? stat_bonus(depth) : -stat_bonus(depth);
    *current += delta - *current * abs(delta) / HistoryDivisor;
}


inline int history_captured_piece(Thread* thread, uint16_t move) 
{
    // Handle Enpassant; Consider promotions as Pawn Captures
    return MoveType(move) != NORMAL_MOVE
        ? PAWN
        : TypeOf(thread->state.board_.at_[MoveTo(move)]);
}

score_t* underlying_capture_history(Thread* thread, uint16_t move)
{
    const int captured = history_captured_piece(thread, move);
    const int piece = TypeOf(thread->state.board_.at_[MoveFrom(move)]);

    // Determine if piece evades and/or enters a threat
    const bool threat_from = HasBit(thread->state.threats, MoveFrom(move));
    const bool threat_to = HasBit(thread->state.threats, MoveTo(move));

    assert(PAWN <= captured && captured <= QUEEN);
    assert(PAWN <= piece && piece <= KING);

    return &thread->chistory[piece][threat_from][threat_to][MoveTo(move)][captured];
}

void underlying_quiet_history(Thread* thread, uint16_t move, score_t* histories[3])
{
    static score_t NULL_HISTORY; // Always zero to handle missing CM/FM history

    NodeState* const ns = &thread->states[thread->height];
    const uint64 threats = thread->state.threats;

    // Extract information from this move
    const int to = MoveTo(move);
    const int from = MoveFrom(move);
    const int piece = TypeOf(thread->state.board_.at_[from]);

    // Determine if piece evades and/or enters a threat
    const bool threat_from = HasBit(threats, from);
    const bool threat_to = HasBit(threats, to);

    // Set Counter Move History if it exists
    histories[0] = (ns - 1)->continuations == NULL
        ? &NULL_HISTORY : &(*(ns - 1)->continuations)[0][piece][to];

    // Set Followup Move History if it exists
    histories[1] = (ns - 2)->continuations == NULL
            ? &NULL_HISTORY 
            : &(*(ns - 2)->continuations)[1][piece][to];

    // Set Butterfly History, which will always exist
    histories[2] = &thread->history[thread->state.turn][threat_from][threat_to][from][to];
}


int get_quiet_history(Thread* thread, uint16_t move, int* cmhist, int* fmhist) 
{
    score_t* histories[3];
    underlying_quiet_history(thread, move, histories);

    *cmhist = *histories[0]; *fmhist = *histories[1];
    return *histories[0] + *histories[1] + *histories[2];
}

void get_quiet_histories(Thread* thread, uint16_t* moves, int* scores, int start, int length) 
{
    int null_hist; // cmhist & fmhist are set, although ignored

    for (int i = start; i < start + length; i++)
        scores[i] = get_quiet_history(thread, moves[i], &null_hist, &null_hist);
}

void update_quiet_histories(Thread* thread, uint16_t* moves, int length, int depth) 
{
    NodeState* const ns = &thread->states[thread->height];

    // We found a low-depth cutoff too easily
    if (!depth || (length == 1 && depth <= 3))
        return;

    for (int i = 0; i < length; i++) {

        score_t* histories[3];
        underlying_quiet_history(thread, moves[i], histories);

        // Update Counter Move History if it exists
        if ((ns - 1)->continuations != NULL)
            update_history(histories[0], depth, i == length - 1);

        // Update Followup Move History if it exists
        if ((ns - 2)->continuations != NULL)
            update_history(histories[1], depth, i == length - 1);

        // Update Butterfly History, which always exists
        update_history(histories[2], depth, i == length - 1);
    }
}


uint64 discoveredAttacks(const Board_& board, int sq, int US)
{
    uint64 enemy = board.colors_[!US];
    uint64 occupied = board.colors_[US] | enemy;

    uint64 rAttacks = rookAttacks(sq, occupied);
    uint64 bAttacks = bishopAttacks(sq, occupied);

    uint64 rooks = enemy & board.Rooks() & ~rAttacks;
    uint64 bishops = enemy & board.Bishops() & ~bAttacks;

    return (rooks & rookAttacks(sq, occupied & ~rAttacks))
            | (bishops & bishopAttacks(sq, occupied & ~bAttacks));
}


/// movegen.c


typedef uint64(*JumperFunc)(int);
typedef uint64(*SliderFunc)(int, uint64);

uint16_t* buildEnpassMoves(uint16_t* moves, uint64 attacks, int epsq) {

    while (attacks)
        *(moves++) = MoveMake(poplsb(&attacks), epsq, ENPASS_MOVE);

    return moves;
}

uint16_t* buildPawnMoves(uint16_t* moves, uint64 attacks, int delta) {

    while (attacks) {
        int sq = poplsb(&attacks);
        *(moves++) = MoveMake(sq + delta, sq, NORMAL_MOVE);
    }

    return moves;
}

uint16_t* buildPawnPromotions(uint16_t* moves, uint64 attacks, int delta) {

    while (attacks) {
        int sq = poplsb(&attacks);
        *(moves++) = MoveMake(sq + delta, sq, QUEEN_PROMO_MOVE);
        *(moves++) = MoveMake(sq + delta, sq, ROOK_PROMO_MOVE);
        *(moves++) = MoveMake(sq + delta, sq, BISHOP_PROMO_MOVE);
        *(moves++) = MoveMake(sq + delta, sq, KNIGHT_PROMO_MOVE);
    }

    return moves;
}

uint16_t* buildNormalMoves(uint16_t* moves, uint64 attacks, int sq) {

    while (attacks)
        *(moves++) = MoveMake(sq, poplsb(&attacks), NORMAL_MOVE);

    return moves;
}

uint16_t* buildJumperMoves(JumperFunc F, uint16_t* moves, uint64 pieces, uint64 targets) {

    while (pieces) {
        int sq = poplsb(&pieces);
        moves = buildNormalMoves(moves, F(sq) & targets, sq);
    }

    return moves;
}

uint16_t* buildSliderMoves(SliderFunc F, uint16_t* moves, uint64 pieces, uint64 targets, uint64 occupied) {

    while (pieces) {
        int sq = poplsb(&pieces);
        moves = buildNormalMoves(moves, F(sq, occupied) & targets, sq);
    }

    return moves;
}


ptrdiff_t genAllNoisyMoves(State* state, uint16_t* moves)
{
    const uint16_t* start = moves;

    const int Left = state->turn == WHITE ? -7 : 7;
    const int Right = state->turn == WHITE ? -9 : 9;
    const int Forward = state->turn == WHITE ? -8 : 8;

    uint64 destinations, pawnEnpass, pawnLeft, pawnRight;
    uint64 pawnPromoForward, pawnPromoLeft, pawnPromoRight;

    uint64 us = state->board_.colors_[state->turn];
    uint64 them = state->board_.colors_[!state->turn];
    uint64 occupied = us | them;

    uint64 pawns = us & (state->board_.Pawns());
    uint64 knights = us & (state->board_.Knights());
    uint64 bishops = us & (state->board_.Bishops());
    uint64 rooks = us & (state->board_.Rooks());
    uint64 kings = us & (state->board_.Kings());

    // Merge together duplicate piece ideas
    bishops |= us & state->board_.Queens();
    rooks |= us & state->board_.Queens();

    // Double checks can only be evaded by moving the King
    if (Multiple(state->kingAttackers))
        return buildJumperMoves(&kingAttacks, moves, kings, them) - start;

    // When checked, we may only uncheck by capturing the checker
    destinations = state->kingAttackers ? state->kingAttackers : them;

    // Compute bitboards for each type of Pawn movement
    pawnEnpass = pawnEnpassCaptures(pawns, state->epSquare, state->turn);
    pawnLeft = pawnLeftAttacks(pawns, them, state->turn);
    pawnRight = pawnRightAttacks(pawns, them, state->turn);
    pawnPromoForward = pawnAdvance(pawns, occupied, state->turn) & PROMOTION_RANKS;
    pawnPromoLeft = pawnLeft & PROMOTION_RANKS; pawnLeft &= ~PROMOTION_RANKS;
    pawnPromoRight = pawnRight & PROMOTION_RANKS; pawnRight &= ~PROMOTION_RANKS;

    // Generate moves for all the Pawns, so long as they are noisy
    moves = buildEnpassMoves(moves, pawnEnpass, state->epSquare);
    moves = buildPawnMoves(moves, pawnLeft & destinations, Left);
    moves = buildPawnMoves(moves, pawnRight & destinations, Right);
    moves = buildPawnPromotions(moves, pawnPromoForward, Forward);
    moves = buildPawnPromotions(moves, pawnPromoLeft, Left);
    moves = buildPawnPromotions(moves, pawnPromoRight, Right);

    // Generate moves for the remainder of the pieces, so long as they are noisy
    moves = buildJumperMoves(&knightAttacks, moves, knights, destinations);
    moves = buildSliderMoves(&bishopAttacks, moves, bishops, destinations, occupied);
    moves = buildSliderMoves(&rookAttacks, moves, rooks, destinations, occupied);
    moves = buildJumperMoves(&kingAttacks, moves, kings, them);

    return moves - start;
}

ptrdiff_t genAllQuietMoves(State* state, uint16_t* moves)
{
    const uint16_t* start = moves;

    const int Forward = state->turn == WHITE ? -8 : 8;
    const uint64 Rank3Relative = state->turn == WHITE ? Line[2] : Line[5];

    int rook, king, rookTo, kingTo, attacked;
    uint64 destinations, pawnForwardOne, pawnForwardTwo, mask;

    uint64 us = state->board_.colors_[state->turn];
    uint64 occupied = us | state->board_.colors_[!state->turn];
    uint64 castles = us & state->castleRooks;

    uint64 pawns = us & (state->board_.Pawns());
    uint64 knights = us & (state->board_.Knights());
    uint64 bishops = us & (state->board_.Bishops());
    uint64 rooks = us & (state->board_.Rooks());
    uint64 kings = us & (state->board_.Kings());

    // Merge together duplicate piece ideas
    bishops |= us & state->board_.Queens();
    rooks |= us & state->board_.Queens();

    // Double checks can only be evaded by moving the King
    if (Multiple(state->kingAttackers))
        return buildJumperMoves(&kingAttacks, moves, kings, ~occupied) - start;

    // When checked, we must block the checker with non-King pieces
    destinations = !state->kingAttackers
        ? ~occupied
        : Between[lsb(kings)][lsb(state->kingAttackers)];

    // Compute bitboards for each type of Pawn movement
    pawnForwardOne = pawnAdvance(pawns, occupied, state->turn) & ~PROMOTION_RANKS;
    pawnForwardTwo = pawnAdvance(pawnForwardOne & Rank3Relative, occupied, state->turn);

    // Generate moves for all the pawns, so long as they are quiet
    moves = buildPawnMoves(moves, pawnForwardOne & destinations, Forward);
    moves = buildPawnMoves(moves, pawnForwardTwo & destinations, Forward * 2);

    // Generate moves for the remainder of the pieces, so long as they are quiet
    moves = buildJumperMoves(&knightAttacks, moves, knights, destinations);
    moves = buildSliderMoves(&bishopAttacks, moves, bishops, destinations, occupied);
    moves = buildSliderMoves(&rookAttacks, moves, rooks, destinations, occupied);
    moves = buildJumperMoves(&kingAttacks, moves, kings, ~occupied);

    // Attempt to generate a castle move for each rook
    while (castles && !state->kingAttackers) {

        // Figure out which pieces are moving to which squares
        rook = poplsb(&castles), king = lsb(kings);
        rookTo = castleRookTo(king, rook);
        kingTo = castleKingTo(king, rook);
        attacked = 0;

        // Castle is illegal if we would go over a piece
        mask = Between[king][kingTo] | (1ull << kingTo);
        mask |= Between[rook][rookTo] | (1ull << rookTo);
        mask &= ~((1ull << king) | (1ull << rook));
        if (occupied & mask) continue;

        // Castle is illegal if we move through a checking threat
        mask = Between[king][kingTo];
        while (mask)
            if (squareIsAttacked(state->board_, state->turn, poplsb(&mask)))
            {
                attacked = 1; break;
            }
        if (attacked) continue;

        // All conditions have been met. Identify which side we are castling to
        *(moves++) = MoveMake(king, rook, CASTLE_MOVE);
    }

    return moves - start;
}

ptrdiff_t genAllLegalMoves(State* state, uint16_t* moves)
{
    Undo undo[1];
    int size = 0;
    uint16_t pseudoMoves[MAX_MOVES];

    // Call genAllNoisyMoves() & genAllNoisyMoves()
    ptrdiff_t pseudo = genAllNoisyMoves(state, pseudoMoves);
    pseudo += genAllQuietMoves(state, pseudoMoves + pseudo);

    // Check each move for legality before copying
    for (int i = 0; i < pseudo; i++) {
        applyMove(state, pseudoMoves[i], undo);
        if (moveWasLegal(*state)) moves[size++] = pseudoMoves[i];
        revertMove(state, pseudoMoves[i], undo);
    }

    return size;
}

int legalMoveCount(State* state)
{
    // Count of the legal number of moves for a given position

    uint16_t moves[MAX_MOVES];
    return static_cast<int>(genAllLegalMoves(state, moves));
}


/// movepicker.c


uint16_t pop_move(int* size, uint16_t* moves, int* values, int index) 
{
    uint16_t popped = moves[index];
    moves[index] = moves[--*size];
    values[index] = values[*size];
    return popped;
}

int best_index(MovePicker* mp, int start, int end) 
{
    int best = start;

    for (int i = start + 1; i < end; i++)
        if (mp->values[i] > mp->values[best])
            best = i;

    return best;
}


void get_refutation_moves(Thread* thread, KillerMoves* killers, uint16_t* counter) 
{
    // At each ply, we should have N_KILLER potential Killer moves that have produced cutoffs
    // at the same ply in sibling nodes. Additionally, we may have a counter move, which
    // refutes the previously moved piece's destination square, somewhere in the search tree

    NodeState* const prev = &thread->states[thread->height - 1];

    *counter = (prev->move == NONE_MOVE || prev->move == NULL_MOVE) 
            ? NONE_MOVE
            : thread->cmtable[!thread->state.turn][prev->movedPiece][MoveTo(prev->move)];
    *killers = thread->killers[thread->height];
}


void init_picker(MovePicker* mp, Thread* thread, uint16_t tt_move) 
{
    // Start with the tt-move
    mp->stage = STAGE_TABLE;
    mp->tt_move = tt_move;

    // Lookup our refutations (killers and counter moves)
    get_refutation_moves(thread, &mp->killers, &mp->counter);

    // General housekeeping
    mp->threshold = 0;
    mp->type = NORMAL_PICKER;

    // Skip over the TT-move if it is illegal
    mp->stage += !moveIsPseudoLegal(thread->state, tt_move);
}

int staticExchangeEvaluation(State* state, uint16_t move, int threshold)
{
    // Unpack move information
    int from = MoveFrom(move);
    int to = MoveTo(move);
    int type = MoveType(move);

    // Next victim is moved piece or promotion type
    int nextVictim = type != PROMOTION_MOVE
            ? TypeOf(state->board_.at_[from])
            : MovePromoPiece(move);

    // Balance is the value of the move minus threshold. Function
    // call takes care for Enpass, Promotion and Castling moves.
    int balance = moveEstimatedValue(state->board_, move) - threshold;

    // Best case still fails to beat the threshold
    if (balance < 0) return 0;

    // Worst case is losing the moved piece
    balance -= SEEPieceValues[nextVictim];

    // If the balance is positive even if losing the moved piece,
    // the exchange is guaranteed to beat the threshold.
    if (balance >= 0) return 1;

    // Grab sliders for updating revealed attackers
    uint64 bishops = state->board_.Bishops() | state->board_.Queens();
    uint64 rooks = state->board_.Rooks() | state->board_.Queens();

    // Let occupied suppose that the move was actually made
    uint64 occupied = (state->board_.colors_[WHITE] | state->board_.colors_[BLACK]);
    occupied = (occupied ^ (1ull << from)) | (1ull << to);
    if (type == ENPASS_MOVE) occupied ^= (1ull << state->epSquare);

    // Get all pieces which attack the target square. And with occupied
    // so that we do not let the same piece attack twice
    uint64 attackers = allAttackersToSquare(state->board_, occupied, to) & occupied;

    // Now our opponents turn to recapture
    int colour = !state->turn;

    while (1) 
    {
        // If we have no more attackers left we lose
        uint64 myAttackers = attackers & state->board_.colors_[colour];
        if (myAttackers == 0ull) break;

        // Find our weakest piece to attack with
        for (nextVictim = PAWN; nextVictim <= QUEEN; nextVictim++)
            if (myAttackers & state->board_.pieces_[nextVictim])
                break;

        // Remove this attacker from the occupied
        occupied ^= (1ull << lsb(myAttackers & state->board_.pieces_[nextVictim]));

        // A diagonal move may reveal bishop or queen attackers
        if (nextVictim == PAWN || nextVictim == BISHOP || nextVictim == QUEEN)
            attackers |= bishopAttacks(to, occupied) & bishops;

        // A vertical or horizontal move may reveal rook or queen attackers
        if (nextVictim == ROOK || nextVictim == QUEEN)
            attackers |= rookAttacks(to, occupied) & rooks;

        // Make sure we did not add any already used attacks
        attackers &= occupied;

        // Swap the turn
        colour ^= 1;

        // Negamax the balance and add the value of the next victim
        balance = -balance - 1 - SEEPieceValues[nextVictim];

        // If the balance is non negative after giving away our piece then we win
        if (balance >= 0) 
        {
            // As a slight speed up for move legality checking, if our last attacking
            // piece is a king, and our opponent still has attackers, then we've
            // lost as the move we followed would be illegal
            if (nextVictim == KING && (attackers & state->board_.colors_[colour]))
                colour ^= 1;

            break;
        }
    }

    // Side to move after the loop loses
    return state->turn != colour;
}

void init_noisy_picker(MovePicker* mp, Thread* thread, uint16_t tt_move, int threshold)
{
    // Start with the tt-move potentially
    mp->stage = STAGE_TABLE;
    mp->tt_move = tt_move;

    // Skip all of the refutation moves
    std::fill(mp->killers.begin(), mp->killers.end(), NONE_MOVE);
    mp->counter = NONE_MOVE;

    // General housekeeping
    mp->threshold = threshold;
    mp->type = NOISY_PICKER;

    // Skip over the TT-move unless its a threshold-winning capture
    mp->stage += !moveIsTactical(thread->state.board_, tt_move)
        || !moveIsPseudoLegal(thread->state, tt_move)
        || !staticExchangeEvaluation(&thread->state, tt_move, threshold);
}

int get_capture_history(Thread* thread, uint16_t move) 
{
    // Inflate Queen Promotions beyond the range of reductions
    return  64000 * (MovePromoPiece(move) == QUEEN)
        + *underlying_capture_history(thread, move);
}

void get_capture_histories(Thread* thread, uint16_t* moves, int* scores, int start, int length) 
{
    // Grab histories for all of the capture moves. Since this is used for sorting,
    // we include an MVV-LVA factor to improve sorting. Additionally, we add 64k to
    // the history score to ensure it is >= 0 to differentiate good from bad later on

    constexpr array<int, 5> MVVAugment = { 0, 2400, 2400, 4800, 9600 };

    for (int i = start; i < start + length; i++)
        scores[i] = 64000 + get_capture_history(thread, moves[i])
                + MVVAugment[history_captured_piece(thread, moves[i])];
}

uint16_t select_next(MovePicker* mp, Thread* thread, int skip_quiets)
{
    State* state = &thread->state;

    switch (mp->stage) 
    {
    case STAGE_TABLE:

        // Play table move ( Already shown to be legal )
        mp->stage = STAGE_GENERATE_NOISY;
        return mp->tt_move;

    case STAGE_GENERATE_NOISY:

        // Generate and evaluate noisy moves. mp->split sets a break point
        // to seperate the noisy from the quiet moves, so that we can skip
        // some of the noisy moves during STAGE_GOOD_NOISY and return later
        mp->noisy_size = mp->split = static_cast<int>(genAllNoisyMoves(state, mp->moves));
        get_capture_histories(thread, mp->moves, mp->values, 0, mp->noisy_size);
        mp->stage = STAGE_GOOD_NOISY;

        [[ fallthrough ]];

    case STAGE_GOOD_NOISY:

        // Check to see if there are still more noisy moves
        while (mp->noisy_size) 
        {
            // Grab the next best move index
            int best = best_index(mp, 0, mp->noisy_size);

            // Values below zero are flagged as failing an SEE (bad noisy)
            if (mp->values[best] < 0)
                break;

            // Skip moves which fail to beat our SEE margin. We flag those moves
            // as failed with the value (-1), and then repeat the selection process
            if (!staticExchangeEvaluation(state, mp->moves[best], mp->threshold)) {
                mp->values[best] = -1;
                continue;
            }

            // Reduce effective move list size
            uint16_t best_move = pop_move(&mp->noisy_size, mp->moves, mp->values, best);

            // Don't play the table move twice
            if (best_move == mp->tt_move)
                continue;

            // Don't play the refutation moves twice
            for (auto& k : mp->killers)
                if (k == best_move)
                    k = NONE_MOVE;
            if (best_move == mp->counter) mp->counter = NONE_MOVE;

            return best_move;
        }

        // Jump to bad noisy moves when skipping quiets
        if (skip_quiets) {
            mp->stage = STAGE_BAD_NOISY;
            return select_next(mp, thread, skip_quiets);
        }

        mp->stage = STAGE_GENERATE_KILLER;

        [[fallthrough]];

    case STAGE_GENERATE_KILLER:

        // Play killer move if not yet played, and pseudo legal
        mp->stage = STAGE_KILLER;
        mp->i_killer = 0;

        [[ fallthrough ]];

    case STAGE_KILLER:

        // Play killer move if not yet played, and pseudo legal
        mp->stage = STAGE_BAD_NOISY;
        if (!skip_quiets)
        {
            mp->stage = STAGE_COUNTER_MOVE;
            while (mp->i_killer < N_KILLER)
            {
                auto k = mp->killers[mp->i_killer++];
                if (!skip_quiets && k != mp->tt_move && moveIsPseudoLegal(*state, k))
                {
                    if (mp->i_killer < N_KILLER)
                        mp->stage = STAGE_KILLER;
                    return k;
                }
            }
        }

        [[ fallthrough ]];

    case STAGE_COUNTER_MOVE:

        // Play counter move if not yet played, and pseudo legal
        mp->stage = STAGE_GENERATE_QUIET;
        if (!skip_quiets
            && mp->counter != mp->tt_move
            && std::find(mp->killers.begin(), mp->killers.end(), mp->counter) == mp->killers.end()
            && moveIsPseudoLegal(*state, mp->counter))
            return mp->counter;

        [[ fallthrough ]];

    case STAGE_GENERATE_QUIET:

        // Generate and evaluate all quiet moves when not skipping them
        if (!skip_quiets) {
            mp->quiet_size = static_cast<int>(genAllQuietMoves(state, mp->moves + mp->split));
            get_quiet_histories(thread, mp->moves, mp->values, mp->split, mp->quiet_size);
        }

        mp->stage = STAGE_QUIET;

        [[ fallthrough ]];

    case STAGE_QUIET:

        // Check to see if there are still more quiet moves
        while (!skip_quiets && mp->quiet_size) 
        {
            // Select next best quiet and reduce the effective move list size
            int best = best_index(mp, mp->split, mp->split + mp->quiet_size) - mp->split;
            uint16_t best_move = pop_move(&mp->quiet_size, mp->moves + mp->split, mp->values + mp->split, best);

            // Don't play a move more than once
            if (best_move == mp->tt_move || std::find(mp->killers.begin(), mp->killers.end(), best_move) != mp->killers.end()
                    || best_move == mp->counter)
                continue;

            return best_move;
        }

        // Out of quiet moves, only bad quiets remain
        mp->stage = STAGE_BAD_NOISY;

        [[ fallthrough ]];

    case STAGE_BAD_NOISY:

        // Check to see if there are still more noisy moves
        while (mp->noisy_size && mp->type != NOISY_PICKER) 
        {
            // Reduce effective move list size
            uint16_t best_move = pop_move(&mp->noisy_size, mp->moves, mp->values, 0);

            // Don't play a move more than once
            if (best_move == mp->tt_move || std::find(mp->killers.begin(), mp->killers.end(), best_move) != mp->killers.end() || best_move == mp->counter)
                continue;

            return best_move;
        }

        mp->stage = STAGE_DONE;

        [[ fallthrough ]];

    case STAGE_DONE:
        return NONE_MOVE;

    default:
        return NONE_MOVE;
    }
}




/// state.c



void clearBoard(State* state) 
{
    // Wipe the entire state structure, and also set all of
    // the pieces on the state to be EMPTY. Ideally, before
    // this state is used again we will call boardFromFEN()

    memset(state, 0, sizeof(State));
    memset(&state->board_.at_, EMPTY, sizeof(state->board_.at_));
}

int stringToSquare(char* str) 
{
    // Helper for reading the enpass square from a FEN. If no square
    // is provided, Ethereal will use -1 to represent this internally

    return str[0] == '-' ? -1 : square(str[1] - '1', str[0] - 'a');
}

void boardToFEN(State* state, char* fen) 
{
    char str[3];

    // Piece placement
    for (int r = N_RANKS - 1; r >= 0; r--) 
    {
        int cnt = 0;

        for (int f = 0; f < N_FILES; f++) 
        {
            const int s = square(r, f);
            const int p = state->board_.at_[s];

            if (p != EMPTY) {
                if (cnt)
                    *fen++ = cnt + '0';

                *fen++ = PieceLabel[ColorOf(p)][TypeOf(p)];
                cnt = 0;
            }
            else
                cnt++;
        }

        if (cnt)
            *fen++ = cnt + '0';

        *fen++ = r == 0 ? ' ' : '/';
    }

    // Turn of play
    *fen++ = state->turn == WHITE ? 'w' : 'b';
    *fen++ = ' ';

    // Castle rights for White
    uint64 castles = state->board_.colors_[WHITE] & state->castleRooks;
    while (castles) {
        int sq = popmsb(&castles);
        if (state->chess960) *fen++ = 'A' + FileOf(sq);
        else if (HasBit(File[7], sq)) *fen++ = 'K';
        else if (HasBit(File[0], sq)) *fen++ = 'Q';
    }

    // Castle rights for Black
    castles = state->board_.colors_[BLACK] & state->castleRooks;
    while (castles) {
        int sq = popmsb(&castles);
        if (state->chess960) *fen++ = 'a' + FileOf(sq);
        else if (HasBit(File[7], sq)) *fen++ = 'k';
        else if (HasBit(File[0], sq)) *fen++ = 'q';
    }

    // Check for empty Castle rights
    if (!state->castleRooks)
        *fen++ = '-';

    // En passant square, Half Move Counter, and Full Move Counter
    squareToString(state->epSquare, str);
    printf(fen, " %s %d %d", str, state->halfMoveCounter, state->fullMoveCounter);
}

void printBoard(State* state) 
{
    char fen[256];

    // Print each row of the state, starting from the top
    for (int sq = square(N_RANKS - 1, 0); sq >= 0; sq -= N_FILES) {

        printf("\n     |----|----|----|----|----|----|----|----|\n");
        printf("   %d ", 1 + sq / 8);

        // Print each square in a row, starting from the left
        for (int i = 0; i < 8; i++) {

            int colour = ColorOf(state->board_.at_[sq + i]);
            int type = TypeOf(state->board_.at_[sq + i]);

            switch (colour) {
            case WHITE: printf("| *%c ", PieceLabel[colour][type]); break;
            case BLACK: printf("|  %c ", PieceLabel[colour][type]); break;
            default: printf("|    "); break;
            }
        }

        printf("|");
    }

    printf("\n     |----|----|----|----|----|----|----|----|");
    printf("\n        A    B    C    D    E    F    G    H\n");

    // Print FEN
    boardToFEN(state, fen);
    printf("\n%s\n\n", fen);
}

bool playerHasNonPawnMaterial(const Board_& board, int turn) 
{
    uint64 friendly = board.colors_[turn];
    uint64 kings = board.Kings();
    uint64 pawns = board.Pawns();
    return (friendly & (kings | pawns)) != friendly;
}

bool boardDrawnByFiftyMoveRule(State* state)
{
    // Fifty move rule triggered. BUG: We do not account for the case
    // when the fifty move rule occurs as checkmate is delivered, which
    // should not be considered a drawn position, but a checkmated one.
    return state->halfMoveCounter >= 100;
}

bool boardDrawnByRepetition(State* state, int height)
{
    int reps = 0;

    // Look through hash histories for our moves
    for (int i = state->numMoves - 2; i >= 0; i -= 2)
    {
        // No draw can occur before a zeroing move
        if (i < state->numMoves - state->halfMoveCounter)
            break;

        // Check for matching hash with a two fold after the root,
        // or a three fold which occurs in part before the root move
        if (state->history[i] == state->hash
            && (i > state->numMoves - height || ++reps == 2))
            return 1;
    }

    return 0;
}

bool boardDrawnByInsufficientMaterial(const Board_& board)
{
    // Check for KvK, KvN, KvB, and KvNN.

    return !(board.Pawns() | board.Rooks() | board.Queens())
            && (!Multiple(board.colors_[WHITE]) || !Multiple(board.colors_[BLACK]))
            && (!Multiple(board.Knights() | board.Bishops())
                    || (!board.Bishops() && popcount(board.Knights()) <= 2));
}

bool boardIsDrawn(State* state, int height) 
{
    // Drawn if any of the three possible cases
    return boardDrawnByFiftyMoveRule(state)
            || boardDrawnByRepetition(state, height)
            || boardDrawnByInsufficientMaterial(state->board_);
}

/// timeman.c

int MoveOverhead = 300; // Set by UCI options

double get_real_time() {
#if defined(_WIN32) || defined(_WIN64)
    return static_cast<double>(chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now().time_since_epoch()).count());
#else
    struct timeval tv;
    double secsInMilli, usecsInMilli;

    gettimeofday(&tv, NULL);
    secsInMilli = ((double)tv.tv_sec) * 1000;
    usecsInMilli = tv.tv_usec / 1000;

    return secsInMilli + usecsInMilli;
#endif
}

double elapsed_time(const TimeManager* tm) {
    return get_real_time() - tm->start_time;
}


void tm_init(const Limits* limits, TimeManager* tm) 
{
    tm->pv_stability = 0; // Clear our stability time usage heuristic
    tm->start_time = limits->start; // Save off the start time of the search
    tm->nodes = {}; // Clear Node counters

    // Allocate time if Ethereal is handling the clock
    if (limits->limitedBySelf) 
    {
        // Playing using X / Y + Z time control
        if (limits->mtg >= 0) {
            tm->ideal_usage = 1.80 * (limits->time - MoveOverhead) / (limits->mtg + 5) + limits->inc;
            tm->max_usage = 10.00 * (limits->time - MoveOverhead) / (limits->mtg + 10) + limits->inc;
        }

        // Playing using X + Y time controls
        else {
            tm->ideal_usage = 2.50 * ((limits->time - MoveOverhead) + 25 * limits->inc) / 50;
            tm->max_usage = 10.00 * ((limits->time - MoveOverhead) + 25 * limits->inc) / 50;
        }

        // Cap time allocations using the move overhead
        tm->ideal_usage = Min(tm->ideal_usage, limits->time - MoveOverhead);
        tm->max_usage = Min(tm->max_usage, limits->time - MoveOverhead);
    }

    // Interface told us to search for a predefined duration
    if (limits->limitedByTime) {
        tm->ideal_usage = limits->timeLimit;
        tm->max_usage = limits->timeLimit;
    }
}

void tm_update(const Thread* thread, const Limits* limits, TimeManager* tm) {

    // Don't update our Time Managment plans at very low depths
    if (!limits->limitedBySelf || thread->completed < 4)
        return;

    // Track how long we've kept the same best move between iterations
    const uint16_t this_move = thread->pvs[thread->completed - 0].line[0];
    const uint16_t last_move = thread->pvs[thread->completed - 1].line[0];
    tm->pv_stability = (this_move == last_move) ? Min(10, tm->pv_stability + 1) : 0;
}

bool tm_finished(const Thread* thread, const TimeManager* tm) {

    // Don't terminate early at very low depths
    if (thread->completed < 4) return FALSE;

    // Scale time between 80% and 120%, based on stable best moves
    const double pv_factor = 1.20 - 0.04 * tm->pv_stability;

    // Scale time between 75% and 125%, based on score fluctuations
    const double score_change = thread->pvs[thread->completed - 3].score
        - thread->pvs[thread->completed - 0].score;
    const double score_factor = Max(0.75, Min(1.25, 0.05 * score_change));

    // Scale time between 50% and 240%, based on where nodes have been spent
    int move = thread->pvs[thread->completed - 0].line[0];
    const uint64 best_nodes = tm->nodes[move & 0xFFF];
    const double non_best_pct = 1.0 - ((double)best_nodes / thread->nodes);
    const double nodes_factor = Max(0.50, 2 * non_best_pct + 0.4);

    return elapsed_time(tm) > tm->ideal_usage * pv_factor * score_factor * nodes_factor;
}

bool tm_stop_early(const Thread* thread) {

    /// Quit early IFF we've surpassed our max time or nodes, and have
    /// finished at least a depth 1 search to ensure we have a best move

    const Limits* limits = thread->limits;

    if (limits->limitedByNodes)
        return thread->depth > 1
        && thread->nodes >= limits->nodeLimit / thread->nthreads;

    return  thread->depth > 1
        && (thread->nodes & 1023) == 1023
        && (limits->limitedBySelf || limits->limitedByTime)
        && elapsed_time(thread->tm) >= thread->tm->max_usage;
}


/// uci.h

#define VERSION_ID "14.24"

#ifndef LICENSE_OWNER
#define LICENSE_OWNER "Unlicensed"
#endif

#if USE_NNUE
#define ETHEREAL_VERSION VERSION_ID" (NNUE)"
#elif defined(USE_PEXT)
#define ETHEREAL_VERSION VERSION_ID" (PEXT)"
#elif defined(USE_POPCNT)
#define ETHEREAL_VERSION VERSION_ID" (POPCNT)"
#else
#define ETHEREAL_VERSION VERSION_ID
#endif



/// syzygy.c

unsigned TB_PROBE_DEPTH; // Set by UCI options

uint16_t convertPyrrhicMove(State* state, unsigned result) 
{
    // Extract Pyrrhic's move representation
    unsigned to = TB_GET_TO(result);
    unsigned from = TB_GET_FROM(result);
    unsigned ep = TB_GET_EP(result);
    unsigned promo = TB_GET_PROMOTES(result);

    // Convert the move notation. Care that Pyrrhic's promotion flags are inverted
    if (ep == 0u && promo == 0u) return MoveMake(from, to, NORMAL_MOVE);
    else if (ep != 0u)           return MoveMake(from, state->epSquare, ENPASS_MOVE);
    else /* if (promo != 0u) */  return MoveMake(from, to, PROMOTION_MOVE | ((4 - promo) << 14));
}

void removeBadWDL(State* state, Limits* limits, unsigned result, unsigned* results) 
{
    // Remove for any moves that fail to maintain the ideal WDL outcome
    for (int i = 0; i < MAX_MOVES && results[i] != TB_RESULT_FAILED; i++)
        if (TB_GET_WDL(results[i]) != TB_GET_WDL(result))
            limits->excludedMoves[i] = convertPyrrhicMove(state, results[i]);
}


void tablebasesProbeDTZ(State* state, Limits* limits) 
{
    unsigned results[MAX_MOVES];
    uint64 white = state->board_.colors_[WHITE];
    uint64 black = state->board_.colors_[BLACK];

    // We cannot probe when there are castling rights, or when
    // we have more pieces than our largest Tablebase has pieces
    if (state->castleRooks || popcount(white | black) > TB_LARGEST)
        return;

    // Tap into Pyrrhic's API. Pyrrhic takes the state representation and the
    // fifty move rule counter, followed by the enpass square (0 if none set),
    // and the turn Pyrrhic defines WHITE as 1, and BLACK as 0, which is the
    // opposite of how Ethereal defines them

    unsigned result = tb_probe_root(
        state->board_.colors_[WHITE], state->board_.colors_[BLACK],
        state->board_.Kings(), state->board_.Queens(),
        state->board_.Rooks(), state->board_.Bishops(),
        state->board_.Knights(), state->board_.Pawns(),
        state->halfMoveCounter, state->epSquare == -1 ? 0 : state->epSquare,
        state->turn == WHITE ? 1 : 0, results
    );

    // Probe failed, or we are already in a finished position.
    if (result == TB_RESULT_FAILED
            || result == TB_RESULT_CHECKMATE
            || result == TB_RESULT_STALEMATE)
        return;

    // Remove any moves that fail to maintain optimal WDL
    removeBadWDL(state, limits, result, results);
}

unsigned tablebasesProbeWDL(State* state, int depth, int height) 
{
    uint64 white = state->board_.colors_[WHITE];
    uint64 black = state->board_.colors_[BLACK];

    // Never take a Syzygy Probe in a Root node, in a node with Castling rights,
    // in a node which was not just zero'ed by a Pawn Move or Capture, or in a
    // node which has more pieces than our largest found Tablebase can handle

    if (height == 0
            || state->castleRooks
            || state->halfMoveCounter
            || popcount(white | black) > TB_LARGEST)
        return TB_RESULT_FAILED;


    // We also will avoid probing beneath the provided TB_PROBE_DEPTH, except
    // for when our state has even fewer pieces than the largest Tablebase is
    // able to handle. Namely, when we have a 7man Tablebase, we will always
    // probe the 6man Tablebase if possible, irregardless of TB_PROBE_DEPTH

    if (depth < (int)TB_PROBE_DEPTH && popcount(white | black) == TB_LARGEST)
        return TB_RESULT_FAILED;


    // Tap into Pyrrhic's API. Pyrrhic takes the state representation, followed
    // by the enpass square (0 if none set), and the turn. Pyrrhic defines WHITE
    // as 1, and BLACK as 0, which is the opposite of how Ethereal defines them

    return tb_probe_wdl(
        state->board_.colors_[WHITE], state->board_.colors_[BLACK],
        state->board_.Kings(), state->board_.Queens(),
        state->board_.Rooks(), state->board_.Bishops(),
        state->board_.Knights(), state->board_.Pawns(),
        state->epSquare == -1 ? 0 : state->epSquare,
        state->turn == WHITE ? 1 : 0
    );
}

/// Roc material

// T(pawn), pawn, knight, bishop, rook, queen
namespace MatQuad
{
    namespace Me
    { 
        constexpr int PP = -33, PN = 17, PB = -23, PR = -155, PQ = -247,
                NN = 15, NB = 296, NR = -105, NQ = -83,
                BB = -162, BR = 327, BQ = 315,
                RR = -861, RQ = -1013,
                QQ = -4096;
    }
    namespace Opp
    {
        constexpr int PN = -14, PB = -96, PR = -20, PQ = -278,
                NB = 35, NR = 39, NQ = 49, 
                BR = 9, BQ = -2, RQ = 75;
    }
}
const int BishopPairQuad[9] = { // tuner: type=array, var=1000, active=0
    -38, 164, 99, 246, -84, -57, -184, 88, -186
};
constexpr array<int, 6> MatClosed = { -20, 22, -33, 18, -2, 26 };



/// evaluate.h


#ifdef TUNE
#define TRACE (1)
#else
#define TRACE (0)
#endif


constexpr int SCALE_NORMAL = 32;
void initMaterial()
{
    constexpr int
        SCALE_DRAW = 0,
        SCALE_OCB_BISHOPS_ONLY = 16,
        SCALE_OCB_ONE_KNIGHT = 26,
        SCALE_OCB_ONE_ROOK = 24,
        SCALE_LONE_QUEEN = 22,
        SCALE_LARGE_PAWN_ADV = 36,
        SCALE_BQ = 28;

    PerMaterial defaultMat;
    defaultMat.scale = { SCALE_NORMAL, SCALE_NORMAL };
    defaultMat.matQuad = 0;

    for (int ii = 0; ii < TotalMat; ++ii)
    {
        PerMaterial& mat = MaterialInfo[ii] = defaultMat;
        array<int, 2> queens = { (ii / MatCodeWQ) % 3, (ii / MatCodeBQ) % 3 };
        array<int, 2> rooks = { (ii / MatCodeWR) % 3, (ii / MatCodeBR) % 3 };
        array<int, 2> lights = { (ii / MatCodeWL) % 2, (ii / MatCodeBL) % 2 };
        array<int, 2> darks = { (ii / MatCodeWD) % 2, (ii / MatCodeBD) % 2 };
        array<int, 2> knights = { (ii / MatCodeWN) % 3, (ii / MatCodeBN) % 3 };
        array<int, 2> pawns = { (ii / MatCodeWP) % 9, (ii / MatCodeBP) % 9 };

        array<int, 2> majors = { queens[0] + rooks[0], queens[1] + rooks[1] };
        array<int, 2> bishops = { lights[0] + darks[0], lights[1] + darks[1] };
        array<int, 2> minors = { bishops[0] + knights[0], bishops[1] + knights[1] };

        mat.phase = 4 * (queens[0] + queens[1]) + 2 * (rooks[0] + rooks[1]) + minors[0] + minors[1];
        for (int me = 0; me < 2; ++me)
        {
            using namespace MatQuad;
            mat.matQuad += pawns[me] * (Me::PP * pawns[me] + Me::PN * knights[me] + Me::PB * bishops[me] + Me::PR * rooks[me] + Me::PQ * queens[me]);
            mat.matQuad += knights[me] * (Me::NN * knights[me] + Me::NB * bishops[me] + Me::NR * rooks[me] + Me::NQ * queens[me]);
            mat.matQuad += bishops[me] * (Me::BB * bishops[me] + Me::BR * rooks[me] + Me::BQ * queens[me]);
            mat.matQuad += rooks[me] * (Me::RR * rooks[me] + Me::RQ * queens[me]);
            mat.matQuad += queens[me] * (Me::QQ * queens[me]);
            mat.matQuad += pawns[me] * (Opp::PN * knights[opp] + Opp::PB * bishops[opp] + Opp::PR * rooks[opp] + Opp::PQ * queens[opp]);
            mat.matQuad += knights[me] * (Opp::NB * bishops[opp] + Opp::NR * rooks[opp] + Opp::NQ * queens[opp]);
            mat.matQuad += bishops[me] * (Opp::BR * rooks[opp] + Opp::BQ * queens[opp]);
            mat.matQuad += rooks[me] * (Opp::RQ * queens[opp]);
            mat.matQuad *= -1;  // so black will be subtracted
        }
        mat.matQuad = (mat.matQuad) / 100;

        if (bishops[0] * bishops[1] == 1 && lights[0] != lights[1])
        {
            // Scale factor for OCB + knights
            if (majors[0] + majors[1] == 0)
            {
                if (knights[0] * knights[1] == 1)
                    mat.scale = { SCALE_OCB_ONE_KNIGHT, SCALE_OCB_ONE_KNIGHT };
                else if (knights[0] + knights[1] == 0)
                    mat.scale = { SCALE_OCB_BISHOPS_ONLY, SCALE_OCB_BISHOPS_ONLY };
            }
            if (queens[0] + queens[1] + knights[0] + knights[1] == 0)
            {
                if (rooks[0] * rooks[1] == 1)
                    mat.scale = { SCALE_OCB_ONE_ROOK, SCALE_OCB_ONE_ROOK };
            }
        }

        if (queens[0] + queens[1] == 1)
        {
            int qSide = queens[1];
            if (rooks[qSide] + minors[qSide] == 0)
                mat.scale[qSide] = SCALE_LONE_QUEEN;
        }
        else if (queens[0] * queens[1] == 1)
        {
            if (bishops[0] * bishops[1] == 1)
                mat.scale = { SCALE_BQ, SCALE_BQ };
        }

        for (int me = 0; me < 2; ++me)
        {
            if (minors[me] == 1 && majors[me] + pawns[me] == 0)
                mat.scale[me] = SCALE_DRAW;

            if (queens[0] + queens[1] == 0)
            {
                // Scale up lone pieces with massive pawn advantages
                if (rooks[0] + minors[0] < 2
                        && rooks[1] + minors[1] < 2
                        && pawns[me] > 2 + pawns[1 - me])
                    mat.scale[me] = SCALE_LARGE_PAWN_ADV;

                // Rook-vs-minor is hard to win with a pawn deficit, very easy with pawn surplus
                if (rooks[me] * minors[opp] == 1 && rooks[opp] + minors[me] == 0)
                {
                    if (pawns[me] < pawns[opp] && pawns[me] < 3)
                        mat.scale[me] = pawns[me] ? 22 + 4 * pawns[me] : 1;
                    else if (pawns[me] > pawns[opp])
                        mat.scale[me] = SCALE_NORMAL + 4 * (pawns[me] - pawns[opp]);
                }
                // rook+minor vs rook, or two minors vs piece, is not winnable unless we have a pawn
                if (pawns[me] == 0 && rooks[me] == rooks[opp] && minors[me] == 1 + minors[opp])
                    mat.scale[me] = Max(1, 5 * rooks[me] + 4 * minors[me] - 7);
            }
        }

        // finally, the default if nothing special has been done
        for (int me = 0; me < 2; ++me)
        {
            if (mat.scale[me] == SCALE_NORMAL && pawns[me] < 5)
                mat.scale[me] = 24 + 2 * pawns[me];
        }
    }
}


struct EvalTrace {
    array<int, N_COLORS> PawnValue, KnightValue, BishopValue, RookValue, QueenValue, KingValue;
    array<array<int, N_COLORS>, N_SQUARES> PawnPSQT, KnightPSQT, BishopPSQT, RookPSQT, QueenPSQT, KingPSQT;
    int PawnCandidatePasser[2][8][N_COLORS];
    int PawnIsolated[8][N_COLORS];
    int PawnStacked[2][8][N_COLORS];
    int PawnBackwards[2][8][N_COLORS];
    int PawnConnected32[32][N_COLORS];
    int KnightOutpost[2][2][N_COLORS];
    int KnightBehindPawn[N_COLORS];
    int KnightInSiberia[4][N_COLORS];
    int KnightMobility[9][N_COLORS];
    int BishopPair[N_COLORS];
    int BishopRammedPawns[N_COLORS];
    int BishopOutpost[2][2][N_COLORS];
    int BishopBehindPawn[N_COLORS];
    int BishopLongDiagonal[N_COLORS];
    int BishopMobility[14][N_COLORS];
    int RookFile[2][N_COLORS];
    int RookOnSeventh[N_COLORS];
    int RookMobility[15][N_COLORS];
    int QueenRelativePin[N_COLORS];
    int QueenMobility[28][N_COLORS];
    int KingPawnFileProximity[8][N_COLORS];
    int KingDefenders[12][N_COLORS];
    int KingShelter[2][8][8][N_COLORS];
    int KingStorm[2][4][8][N_COLORS];
    int SafetyKnightWeight[N_COLORS];
    int SafetyBishopWeight[N_COLORS];
    int SafetyRookWeight[N_COLORS];
    int SafetyQueenWeight[N_COLORS];
    int SafetyAttackValue[N_COLORS];
    int SafetyWeakSquares[N_COLORS];
    int SafetyNoEnemyQueens[N_COLORS];
    int SafetySafeQueenCheck[N_COLORS];
    int SafetySafeRookCheck[N_COLORS];
    int SafetySafeBishopCheck[N_COLORS];
    int SafetySafeKnightCheck[N_COLORS];
    int SafetyAdjustment[N_COLORS];
    int SafetyShelter[2][8][N_COLORS];
    int SafetyStorm[2][8][N_COLORS];
    int PassedPawn[2][2][8][N_COLORS];
    int PassedFriendlyDistance[8][N_COLORS];
    int PassedEnemyDistance[8][N_COLORS];
    int PassedSafePromotionPath[N_COLORS];
    int ThreatWeakPawn[N_COLORS];
    int ThreatMinorAttackedByPawn[N_COLORS];
    int ThreatMinorAttackedByMinor[N_COLORS];
    int ThreatMinorAttackedByMajor[N_COLORS];
    int ThreatRookAttackedByLesser[N_COLORS];
    int ThreatMinorAttackedByKing[N_COLORS];
    int ThreatRookAttackedByKing[N_COLORS];
    int ThreatQueenAttackedByOne[N_COLORS];
    int ThreatOverloadedPieces[N_COLORS];
    int ThreatByPawnPush[N_COLORS];
    int SpaceRestrictPiece[N_COLORS];
    int SpaceRestrictEmpty[N_COLORS];
    int SpaceCenterControl[N_COLORS];
    int ClosednessKnightAdjustment[9][N_COLORS];
    int ClosednessRookAdjustment[9][N_COLORS];
    int ComplexityTotalPawns[N_COLORS];
    int ComplexityPawnFlanks[N_COLORS];
    int ComplexityPawnEndgame[N_COLORS];
    int ComplexityAdjustment[N_COLORS];
    packed_t eval, complexity;
    int factor;
    packed_t safety[N_COLORS];
};

struct EvalInfo 
{
    array<array<uint64, N_PIECES>, N_COLORS> attackedBy;
    array<uint64, N_COLORS> pawnAttacks, pawnAttacksBy2, rammedPawns, blockedPawns;
    array<uint64, N_COLORS> kingAreas, mobilityAreas, attacked, attackedBy2;
    array<uint64, N_COLORS> occupiedMinusBishops, occupiedMinusRooks;
    array<packed_t, N_COLORS> kingAttackersWeight, pkeval, pksafety;
    uint64 passedPawns;
    array<int, N_COLORS> kingSquare, kingAttacksCount, kingAttackersCount;
    PKEntry* pkentry;

    // Roc parts

};

/// nnue/nnue.h

#if USE_NNUE

void nnue_init(const char* fname);
void nnue_incbin_init();
int nnue_evaluate(Thread* thread, State* state);

#else

INLINE void nnue_init(const char* fname) {
    (void)fname; printf("info string Error: NNUE is disabled for this binary\n");
}

INLINE void nnue_incbin_init() { }

INLINE int nnue_evaluate(Thread*, State*) { return 0; }

#endif


/// nnue/nnue.c

#include "incbin/incbin.h"
#include "archs/avx2.h"

#define SHIFT_L0 6
#define SHIFT_L1 5

#ifdef EVALFILE
const char* NNUEDefault = EVALFILE;
INCBIN(IncWeights, EVALFILE);
#endif

ALIGN64 int16_t in_weights[INSIZE * KPSIZE];
ALIGN64 int8_t  l1_weights[L1SIZE * L2SIZE];
ALIGN64 float   l2_weights[L2SIZE * L3SIZE];
ALIGN64 float   l3_weights[L3SIZE * OUTSIZE];

ALIGN64 int16_t in_biases[KPSIZE];
ALIGN64 int32_t l1_biases[L2SIZE];
ALIGN64 float   l2_biases[L3SIZE];
ALIGN64 float   l3_biases[OUTSIZE];

static int NNUE_LOADED = 0;

void scale_weights() 
{
    // Delayed dequantization of the results of L1 forces an upshift in
    // biases of L2 and L3 to compensate. This saves SRAI calls, as well as
    // increases the precision of each layer, with no clear downsides.

    for (int i = 0; i < L3SIZE; i++)
        l2_biases[i] *= (1 << SHIFT_L1);

    for (int i = 0; i < OUTSIZE; i++)
        l3_biases[i] *= (1 << SHIFT_L1);
}

template<class E_> void e_transpose(E_* matrix, int rows, int cols) {

    // Typical Matrix Transposition using int8_t. Ethereal's trainer
    // stores weights in a way to allow faster updates, not computes

    vector<E_> cpy(rows * cols);

    for (int i = 0; i < rows; i++)
        for (int j = 0; j < cols; j++)
            cpy[j * rows + i] = matrix[i * cols + j];

    memcpy(matrix, &cpy[0], sizeof(int8_t) * rows * cols);
}

void shuffle_input_layer() 
{
#if defined(USE_AVX2)

    __m256i* wgt = (__m256i*) in_weights;
    __m256i* bia = (__m256i*) in_biases;

    // Interleave adjacent 256-bit chunks of 2-byte values. During
    // halfkp_relu() adjacent chunks are split, with the A-half of
    // chunk 1 swapping with A-half of chunk 2. This is done to both
    // the weights and the biases, to avoid unshuffling them later.

    for (int i = 0; i < KPSIZE / vepi16_cnt; i += 2) {

        __m128i half1 = _mm256_extracti128_si256(bia[i + 0], 1);
        __m128i half2 = _mm256_extracti128_si256(bia[i + 1], 0);

        bia[i + 0] = _mm256_inserti128_si256(bia[i + 0], half2, 1);
        bia[i + 1] = _mm256_inserti128_si256(bia[i + 1], half1, 0);
    }

    for (int i = 0; i < INSIZE * KPSIZE / vepi16_cnt; i += 2) {

        __m128i half1 = _mm256_extracti128_si256(wgt[i + 0], 1);
        __m128i half2 = _mm256_extracti128_si256(wgt[i + 1], 0);

        wgt[i + 0] = _mm256_inserti128_si256(wgt[i + 0], half2, 1);
        wgt[i + 1] = _mm256_inserti128_si256(wgt[i + 1], half1, 0);
    }

#endif
}

void abort_nnue(const char* reason) {
    printf("info string %s\n", reason);
    fflush(stdout); exit(EXIT_FAILURE);
}


INLINE void maddubs_x4(vepi32* acc, const vepi8* inp, const vepi8* wgt, int i, int j, int k) 
{
    constexpr int InChunks = L1SIZE / vepi8_cnt;

    vepi16 sum0 = vepi16_maubs(inp[j + 0], wgt[InChunks * (i * 8 + k) + j + 0]);
    vepi16 sum1 = vepi16_maubs(inp[j + 1], wgt[InChunks * (i * 8 + k) + j + 1]);
    vepi16 sum2 = vepi16_maubs(inp[j + 2], wgt[InChunks * (i * 8 + k) + j + 2]);
    vepi16 sum3 = vepi16_maubs(inp[j + 3], wgt[InChunks * (i * 8 + k) + j + 3]);

    vepi16 sumX = vepi16_add(sum0, vepi16_add(sum1, vepi16_add(sum2, sum3)));
    *acc = vepi32_add(*acc, vepi16_madd(vepi16_one, sumX));
}


INLINE void halfkp_relu(NNUEAccumulator* accum, uint8_t* outputs, int turn) {

    // The accumulation of king-piece values has already been computed.
    // Perform the ReLU operation on each accumuatlor, and place them
    // such that the side-to-move is first, then the non-side-to-move

    assert(KPSIZE % 64 == 0);

    vepi16* in_white = (vepi16*)&accum->values[WHITE];
    vepi16* in_black = (vepi16*)&accum->values[BLACK];

    vepi8* out_white = (vepi8*)(turn == WHITE ? outputs : &outputs[KPSIZE]);
    vepi8* out_black = (vepi8*)(turn == BLACK ? outputs : &outputs[KPSIZE]);

    for (int i = 0; i < KPSIZE / vepi8_cnt; i += 2) {

        vepi16 shift0A = vepi16_srai(in_white[(i + 0) * 2 + 0], SHIFT_L0);
        vepi16 shift0B = vepi16_srai(in_white[(i + 0) * 2 + 1], SHIFT_L0);
        vepi16 shift1A = vepi16_srai(in_white[(i + 1) * 2 + 0], SHIFT_L0);
        vepi16 shift1B = vepi16_srai(in_white[(i + 1) * 2 + 1], SHIFT_L0);

        out_white[i + 0] = vepi16_packu(shift0A, shift0B);
        out_white[i + 1] = vepi16_packu(shift1A, shift1B);
    }

    for (int i = 0; i < KPSIZE / vepi8_cnt; i += 2) {

        vepi16 shift0A = vepi16_srai(in_black[(i + 0) * 2 + 0], SHIFT_L0);
        vepi16 shift0B = vepi16_srai(in_black[(i + 0) * 2 + 1], SHIFT_L0);
        vepi16 shift1A = vepi16_srai(in_black[(i + 1) * 2 + 0], SHIFT_L0);
        vepi16 shift1B = vepi16_srai(in_black[(i + 1) * 2 + 1], SHIFT_L0);

        out_black[i + 0] = vepi16_packu(shift0A, shift0B);
        out_black[i + 1] = vepi16_packu(shift1A, shift1B);
    }
}

INLINE void quant_affine_relu(int8_t* weights, int32_t* biases, uint8_t* inputs, float* outputs) {

    assert(L1SIZE % 64 == 0 && L2SIZE % 8 == 0);

    const int InChunks = L1SIZE / vepi8_cnt;
    const int OutChunks = L2SIZE / 8;

#if defined(USE_AVX2) || defined(USE_AVX)
    const vepi32 zero = vepi32_zero();
#elif defined(USE_SSSE3)
    const vps32  zero = vps32_zero();
#endif

    const vepi8* inp = (vepi8*)inputs;
    const vepi8* wgt = (vepi8*)weights;
    const vepi32* bia = (vepi32*)biases;
    vps32* const out = (vps32*)outputs;

    for (int i = 0; i < OutChunks; i++) {

        vepi32 acc0 = vepi32_zero();
        vepi32 acc1 = vepi32_zero();
        vepi32 acc2 = vepi32_zero();
        vepi32 acc3 = vepi32_zero();
        vepi32 acc4 = vepi32_zero();
        vepi32 acc5 = vepi32_zero();
        vepi32 acc6 = vepi32_zero();
        vepi32 acc7 = vepi32_zero();

        for (int j = 0; j < InChunks; j += 4) {
            maddubs_x4(&acc0, inp, wgt, i, j, 0);
            maddubs_x4(&acc1, inp, wgt, i, j, 1);
            maddubs_x4(&acc2, inp, wgt, i, j, 2);
            maddubs_x4(&acc3, inp, wgt, i, j, 3);
            maddubs_x4(&acc4, inp, wgt, i, j, 4);
            maddubs_x4(&acc5, inp, wgt, i, j, 5);
            maddubs_x4(&acc6, inp, wgt, i, j, 6);
            maddubs_x4(&acc7, inp, wgt, i, j, 7);
        }

        acc0 = vepi32_hadd(acc0, acc1);
        acc2 = vepi32_hadd(acc2, acc3);
        acc0 = vepi32_hadd(acc0, acc2);
        acc4 = vepi32_hadd(acc4, acc5);
        acc6 = vepi32_hadd(acc6, acc7);
        acc4 = vepi32_hadd(acc4, acc6);

#if defined(USE_AVX2)

        __m128i sumabcd1 = _mm256_extracti128_si256(acc0, 0);
        __m128i sumabcd2 = _mm256_extracti128_si256(acc0, 1);
        __m128i sumefgh1 = _mm256_extracti128_si256(acc4, 0);
        __m128i sumefgh2 = _mm256_extracti128_si256(acc4, 1);

        sumabcd1 = _mm_add_epi32(sumabcd1, sumabcd2);
        sumefgh1 = _mm_add_epi32(sumefgh1, sumefgh2);

        acc0 = _mm256_inserti128_si256(_mm256_castsi128_si256(sumabcd1), sumefgh1, 1);
        acc0 = _mm256_add_epi32(acc0, bia[i]);
        acc0 = _mm256_max_epi32(acc0, zero);
        out[i] = _mm256_cvtepi32_ps(acc0);

#elif defined (USE_AVX)

        __m128 ps0 = _mm_cvtepi32_ps(vepi32_max(zero, vepi32_add(bia[i * 2 + 0], acc0)));
        __m128 ps1 = _mm_cvtepi32_ps(vepi32_max(zero, vepi32_add(bia[i * 2 + 1], acc4)));

        out[i] = _mm256_insertf128_ps(out[i], ps0, 0);
        out[i] = _mm256_insertf128_ps(out[i], ps1, 1);

#elif defined (USE_SSSE3)

        out[i * 2 + 0] = vps32_max(zero, _mm_cvtepi32_ps(vepi32_add(bia[i * 2 + 0], acc0)));
        out[i * 2 + 1] = vps32_max(zero, _mm_cvtepi32_ps(vepi32_add(bia[i * 2 + 1], acc4)));

#endif
    }
}

INLINE void float_affine_relu(float* weights, float* biases, float* inputs, float* outputs) {

    assert(L2SIZE % 8 == 0 && L3SIZE % 8 == 0);

    const int InChunks = L2SIZE / vps32_cnt;
    const int OutChunks = L3SIZE / 8;

    const vps32 zero = vps32_zero();

    const vps32* inp = (vps32*)inputs;
    const vps32* bia = (vps32*)biases;
    const vps32* wgt = (vps32*)weights;
    vps32* const out = (vps32*)outputs;

    for (int i = 0; i < OutChunks; i++) {

        vps32 acc0 = vps32_mul(wgt[InChunks * (i * 8 + 0) + 0], inp[0]);
        vps32 acc1 = vps32_mul(wgt[InChunks * (i * 8 + 1) + 0], inp[0]);
        vps32 acc2 = vps32_mul(wgt[InChunks * (i * 8 + 2) + 0], inp[0]);
        vps32 acc3 = vps32_mul(wgt[InChunks * (i * 8 + 3) + 0], inp[0]);
        vps32 acc4 = vps32_mul(wgt[InChunks * (i * 8 + 4) + 0], inp[0]);
        vps32 acc5 = vps32_mul(wgt[InChunks * (i * 8 + 5) + 0], inp[0]);
        vps32 acc6 = vps32_mul(wgt[InChunks * (i * 8 + 6) + 0], inp[0]);
        vps32 acc7 = vps32_mul(wgt[InChunks * (i * 8 + 7) + 0], inp[0]);

        for (int j = 1; j < InChunks; j++) {
            acc0 = vps32_fma(wgt[InChunks * (i * 8 + 0) + j], inp[j], acc0);
            acc1 = vps32_fma(wgt[InChunks * (i * 8 + 1) + j], inp[j], acc1);
            acc2 = vps32_fma(wgt[InChunks * (i * 8 + 2) + j], inp[j], acc2);
            acc3 = vps32_fma(wgt[InChunks * (i * 8 + 3) + j], inp[j], acc3);
            acc4 = vps32_fma(wgt[InChunks * (i * 8 + 4) + j], inp[j], acc4);
            acc5 = vps32_fma(wgt[InChunks * (i * 8 + 5) + j], inp[j], acc5);
            acc6 = vps32_fma(wgt[InChunks * (i * 8 + 6) + j], inp[j], acc6);
            acc7 = vps32_fma(wgt[InChunks * (i * 8 + 7) + j], inp[j], acc7);
        }

        acc0 = vps32_hadd(acc0, acc1);
        acc2 = vps32_hadd(acc2, acc3);
        acc4 = vps32_hadd(acc4, acc5);
        acc6 = vps32_hadd(acc6, acc7);

        acc0 = vps32_hadd(acc0, acc2);
        acc4 = vps32_hadd(acc4, acc6);

#if defined(USE_AVX2) || defined(USE_AVX)

        __m128 sumabcd1 = _mm256_extractf128_ps(acc0, 0);
        __m128 sumabcd2 = _mm256_extractf128_ps(acc0, 1);
        __m128 sumefgh1 = _mm256_extractf128_ps(acc4, 0);
        __m128 sumefgh2 = _mm256_extractf128_ps(acc4, 1);

        sumabcd1 = _mm_add_ps(sumabcd1, sumabcd2);
        sumefgh1 = _mm_add_ps(sumefgh1, sumefgh2);

        acc0 = _mm256_insertf128_ps(_mm256_castps128_ps256(sumabcd1), sumefgh1, 1);
        out[i] = _mm256_max_ps(zero, _mm256_add_ps(bia[i], acc0));

#elif defined(USE_SSSE3)

        out[i * 2 + 0] = vps32_max(zero, vps32_add(bia[i * 2 + 0], acc0));
        out[i * 2 + 1] = vps32_max(zero, vps32_add(bia[i * 2 + 1], acc4));

#endif
    }
}

INLINE void output_transform(float* weights, float* biases, float* inputs, float* outputs) {

    assert(L3SIZE % 8 == 0);

    const int InChunks = L3SIZE / vps32_cnt;

    const vps32* inp = (vps32*)inputs;
    const vps32* wgt = (vps32*)weights;

    vps32 acc = vps32_mul(wgt[0], inp[0]);
    for (int i = 1; i < InChunks; i++)
        acc = vps32_fma(wgt[i], inp[i], acc);

#if defined(USE_AVX) || defined(USE_AVX2)

    const __m128 hiQuad = _mm256_extractf128_ps(acc, 1);
    const __m128 loQuad = _mm256_castps256_ps128(acc);
    const __m128 sumQuad = _mm_add_ps(loQuad, hiQuad);

#elif defined(USE_SSSE3)

    const __m128 sumQuad = acc;

#endif

    const __m128 hiDual = _mm_movehl_ps(sumQuad, sumQuad);
    const __m128 sumDual = _mm_add_ps(sumQuad, hiDual);

    const __m128 hi = _mm_shuffle_ps(sumDual, sumDual, 0x1);
    const __m128 sum = _mm_add_ss(sumDual, hi);

    *outputs = (_mm_cvtss_f32(sum) + *biases);
}

#if USE_NNUE

void nnue_init(const char* fname) 
{
    // Reads an NNUE file specified by a User. If the datasize does not match
    // the compiled NNUE configuration, abort. Afterwords, scale some weights
    // for speed optimizations, and transpose the weights in L1 and L2

    FILE* fin = fopen(fname, "rb");

    if (fread(in_biases, sizeof(int16_t), KPSIZE, fin) != (size_t)KPSIZE
        || fread(in_weights, sizeof(int16_t), INSIZE * KPSIZE, fin) != (size_t)INSIZE * KPSIZE)
        abort_nnue("Unable to read NNUE File");

    if (fread(l1_biases, sizeof(int32_t), L2SIZE, fin) != (size_t)L2SIZE
        || fread(l1_weights, sizeof(int8_t), L1SIZE * L2SIZE, fin) != (size_t)L1SIZE * L2SIZE)
        abort_nnue("Unable to read NNUE File");

    if (fread(l2_biases, sizeof(float), L3SIZE, fin) != (size_t)L3SIZE
        || fread(l2_weights, sizeof(float), L2SIZE * L3SIZE, fin) != (size_t)L2SIZE * L3SIZE)
        abort_nnue("Unable to read NNUE File");

    if (fread(l3_biases, sizeof(float), OUTSIZE, fin) != (size_t)OUTSIZE
        || fread(l3_weights, sizeof(float), L3SIZE * OUTSIZE, fin) != (size_t)L3SIZE * OUTSIZE)
        abort_nnue("Unable to read NNUE File");

    scale_weights();
    shuffle_input_layer();
    e_transpose(l1_weights, L1SIZE, L2SIZE);
    e_transpose(l2_weights, L2SIZE, L3SIZE);
    fclose(fin);

    NNUE_LOADED = 1;
}

void nnue_incbin_init() {

    // Inits from an NNUE file compiled into the binary. Assume the compiled
    // data is correct for the given NNUE config. Afterwords, scale some
    // weights for speed optimizations, and transpose the weights in L1 and L2

#ifdef EVALFILE

    int8_t* data8; int16_t* data16; int32_t* data32; float* dataf;

    // Input layer uses 16-bit Biases and Weights

    data16 = (int16_t*)gIncWeightsData;
    for (int i = 0; i < KPSIZE; i++)
        in_biases[i] = *(data16++);

    for (int i = 0; i < INSIZE * KPSIZE; i++)
        in_weights[i] = *(data16++);

    // Layer one uses 32-bit Biases and 8-bit Weights

    data32 = (int32_t*)data16;
    for (int i = 0; i < L2SIZE; i++)
        l1_biases[i] = *(data32++);

    data8 = (int8_t*)data32;
    for (int i = 0; i < L1SIZE * L2SIZE; i++)
        l1_weights[i] = *(data8++);

    // Layer two and uses Floating Point Biases and Weights

    dataf = (float*)data8;
    for (int i = 0; i < L3SIZE; i++)
        l2_biases[i] = *(dataf++);

    for (int i = 0; i < L2SIZE * L3SIZE; i++)
        l2_weights[i] = *(dataf++);

    // Layer three and uses Floating Point Biases and Weights

    for (int i = 0; i < OUTSIZE; i++)
        l3_biases[i] = *(dataf++);

    for (int i = 0; i < L3SIZE * OUTSIZE; i++)
        l3_weights[i] = *(dataf++);

    scale_weights();
    shuffle_input_layer();
    quant_transpose(l1_weights, L1SIZE, L2SIZE);
    float_transpose(l2_weights, L2SIZE, L3SIZE);

    NNUE_LOADED = 1;

#endif
}

int nnue_evaluate(Thread* thread, State* state) 
{
    int mg_eval, eg_eval;
    const uint64 white = state->board_.colors_[WHITE];
    const uint64 black = state->board_.colors_[BLACK];
    const uint64 kings = state->board_.Kings();

    if (!NNUE_LOADED)
        abort_nnue("NNUE File was not provided");

    // For optimizations, auto-flag KvK as drawn
    if (kings == (white | black)) return 0;

    // Optimized computation of various input indices
    int wrelksq = relativeSquare(WHITE, lsb(white & kings));
    int brelksq = relativeSquare(BLACK, lsb(black & kings));

    NNUEAccumulator* accum = thread->nnue->current;

    ALIGN64 uint8_t out8[L1SIZE];
    ALIGN64 float   outN1[L1SIZE];
    ALIGN64 float   outN2[L1SIZE];

    if (!accum->accurate[WHITE]) {

        // Possible to recurse and incrementally update each
        if (nnue_can_update(accum, state, WHITE))
            nnue_update_accumulator(accum, state, WHITE, wrelksq);

        // History is missing, we must refresh completely
        else
            nnue_refresh_accumulator(thread->nnue, accum, state, WHITE, wrelksq);
    }

    if (!accum->accurate[BLACK]) {

        // Possible to recurse and incrementally update each
        if (nnue_can_update(accum, state, BLACK))
            nnue_update_accumulator(accum, state, BLACK, brelksq);

        // History is missing, we must refresh completely
        else
            nnue_refresh_accumulator(thread->nnue, accum, state, BLACK, brelksq);
    }

    // Feed-forward the entire evaluation function
    halfkp_relu(accum, out8, state->turn);
    quant_affine_relu(l1_weights, l1_biases, out8, outN1);
    float_affine_relu(l2_weights, l2_biases, outN1, outN2);
    output_transform(l3_weights, l3_biases, outN2, outN1);

    // Perform the dequantization step and upscale the Midgame
    mg_eval = 140 * ((int)(outN1[0]) >> SHIFT_L1) / 100;
    eg_eval = 100 * ((int)(outN1[0]) >> SHIFT_L1) / 100;

    // Cap the NNUE evaluation within [-2000, 2000]
    mg_eval = Max(-2000, Min(2000, mg_eval));
    eg_eval = Max(-2000, Min(2000, eg_eval));
    return MakeScore(mg_eval, eg_eval);
}

#endif

/// evaluate.c


EvalTrace TheTrace, EmptyTrace;

#define S(mg, eg) (MakeScore((mg), (eg)))

/* Pawn Evaluation Terms */

constexpr array<array<packed_t, N_RANKS>, 2> PawnCandidatePasser = 
{
   array<packed_t, N_RANKS>{S(0,   0), S(-11, -18), S(-16,  18), S(-18,  29), S(-22,  61), S(21,  59), S(0,   0), S(0,   0)},
   array<packed_t, N_RANKS>{S(0,   0), S(-12,  21), S(-7,  27), S(2,  53), S(22, 116), S(49,  78), S(0,   0), S(0,   0)},
};

constexpr array<packed_t, N_FILES> PawnIsolated = {
    S(-13, -12), S(-1, -16), S(1, -16), S(3, -18),
    S(7, -19), S(3, -15), S(-4, -14), S(-4, -17),
};

constexpr array<array<packed_t, N_FILES>, 2> PawnStacked = 
{
   array<packed_t, N_FILES>{S(10, -29), S(-2, -26), S(0, -23), S(0, -20), S(3, -20), S(5, -26), S(4, -30), S(8, -31)},
   array<packed_t, N_FILES>{S(3, -14), S(0, -15), S(-6,  -9), S(-7, -10), S(-4,  -9), S(-2, -10), S(0, -13), S(0, -17)},
};

constexpr array<array<packed_t, N_RANKS>, 2> PawnBackwards = {
   array<packed_t, N_RANKS>{S(0,   0), S(0,  -7), S(7,  -7), S(6, -18), S(-4, -29), S(0,   0), S(0,   0), S(0,   0)},
   array<packed_t, N_RANKS>{S(0,   0), S(-9, -32), S(-5, -30), S(3, -31), S(29, -41), S(0,   0), S(0,   0), S(0,   0)},
};

constexpr array<packed_t, 32> PawnConnected32 = {
    S(0,   0), S(0,   0), S(0,   0), S(0,   0),
    S(-1, -11), S(12,  -4), S(0,  -2), S(6,   8),
    S(14,   0), S(20,  -6), S(19,   3), S(17,   8),
    S(6,  -1), S(20,   1), S(6,   3), S(14,  10),
    S(8,  14), S(21,  17), S(31,  23), S(25,  18),
    S(45,  40), S(36,  64), S(58,  74), S(64,  88),
    S(108,  35), S(214,  45), S(216,  70), S(233,  61),
    S(0,   0), S(0,   0), S(0,   0), S(0,   0),
};

/* Knight Evaluation Terms */

constexpr array<array<packed_t, 2>, 2> KnightOutpost = {
   array<packed_t, 2>{S(12, -32), S(40,   0)},
   array<packed_t, 2>{S(7, -24), S(21,  -3)},
};

constexpr packed_t KnightBehindPawn = S(3, 28);

constexpr array<packed_t, 4> KnightInSiberia = {
    S(-9,  -6), S(-12, -20), S(-27, -20), S(-47, -19),
};

constexpr array<packed_t, 9> KnightMobility = {
    S(-104,-139), S(-45,-114), S(-22, -37), S(-8,   3),
    S(6,  15), S(11,  34), S(19,  38), S(30,  37),
    S(43,  17),
};

/* Bishop Evaluation Terms */

constexpr packed_t BishopPair = S(22, 88);

constexpr packed_t BishopRammedPawns = S(-8, -17);

constexpr array<array<packed_t, 2>, 2> BishopOutpost = {
   array<packed_t, 2>{S(16, -16), S(50,  -3)},
   array<packed_t, 2>{S(9,  -9), S(-4,  -4)},
};

constexpr packed_t BishopBehindPawn = S(4, 24);

constexpr packed_t BishopLongDiagonal = S(26, 20);

constexpr array<packed_t, 14> BishopMobility = {
    S(-99,-186), S(-46,-124), S(-16, -54), S(-4, -14),
    S(6,   1), S(14,  20), S(17,  35), S(19,  39),
    S(19,  49), S(27,  48), S(26,  48), S(52,  32),
    S(55,  47), S(83,   2),
};

/* Rook Evaluation Terms */

constexpr array<packed_t, 2> RookFile = { S(10,   9), S(34,   8) };

constexpr packed_t RookOnSeventh = S(-1, 42);

constexpr array<packed_t, 15> RookMobility = {
    S(-127,-148), S(-56,-127), S(-25, -85), S(-12, -28),
    S(-10,   2), S(-12,  27), S(-11,  42), S(-4,  46),
    S(4,  52), S(9,  55), S(11,  64), S(19,  68),
    S(19,  73), S(37,  60), S(97,  15),
};

/* Queen Evaluation Terms */

constexpr packed_t QueenRelativePin = S(-22, -13);

constexpr array<packed_t, 28> QueenMobility = {
    S(-111,-273), S(-253,-401), S(-127,-228), S(-46,-236),
    S(-20,-173), S(-9, -86), S(-1, -35), S(2,  -1),
    S(8,   8), S(10,  31), S(15,  37), S(17,  55),
    S(20,  46), S(23,  57), S(22,  58), S(21,  64),
    S(24,  62), S(16,  65), S(13,  63), S(18,  48),
    S(25,  30), S(38,   8), S(34, -12), S(28, -29),
    S(10, -44), S(7, -79), S(-42, -30), S(-23, -50),
};

/* King Evaluation Terms */

constexpr array<packed_t, 12> KingDefenders = {
    S(-37,  -3), S(-17,   2), S(0,   6), S(11,   8),
    S(21,   8), S(32,   0), S(38, -14), S(10,  -5),
    S(12,   6), S(12,   6), S(12,   6), S(12,   6),
};

constexpr array<packed_t, N_FILES> KingPawnFileProximity = {
    S(36,  46), S(22,  31), S(13,  15), S(-8, -22),
    S(-5, -62), S(-3, -75), S(-15, -81), S(-12, -75),
};

constexpr array<array<array<packed_t, N_RANKS>, N_FILES>, 2> KingShelter = 
{
  array<array<packed_t, N_RANKS>, N_FILES>{
        array<packed_t, N_RANKS>{S(-5,  -5), S(17, -31), S(26,  -3), S(24,   8), S(4,   1), S(-12,   4), S(-16, -33), S(-59,  24)},
        array<packed_t, N_RANKS>{S(11,  -6), S(3, -15), S(-5,  -2), S(5,  -4), S(-11,   7), S(-53,  70), S(81,  82), S(-19,   1)},
        array<packed_t, N_RANKS>{S(38,  -3), S(5,  -6), S(-34,   5), S(-17, -15), S(-9,  -5), S(-26,  12), S(11,  73), S(-16,  -1)},
        array<packed_t, N_RANKS>{S(18,  11), S(25, -18), S(0, -14), S(10, -21), S(22, -34), S(-48,   9), S(-140,  49), S(-5,  -5)},
        array<packed_t, N_RANKS>{S(-11,  15), S(1,  -3), S(-44,   6), S(-28,  10), S(-24,  -2), S(-35,  -5), S(40, -24), S(-13,   3)},
        array<packed_t, N_RANKS>{S(51, -14), S(15, -14), S(-24,   5), S(-10, -20), S(10, -34), S(34, -20), S(48, -38), S(-21,   1)},
        array<packed_t, N_RANKS>{S(40, -17), S(2, -24), S(-31,  -1), S(-24,  -8), S(-31,   2), S(-20,  29), S(4,  49), S(-16,   3)},
        array<packed_t, N_RANKS>{S(10, -20), S(4, -24), S(10,   2), S(2,  16), S(-10,  24), S(-10,  44), S(-184,  81), S(-17,  17)}},
  array<array<packed_t, N_RANKS>, N_FILES>{
        array<packed_t, N_RANKS>{S(0,   0), S(-15, -39), S(9, -29), S(-49,  14), S(-36,   6), S(-8,  50), S(-168,  -3), S(-59,  19)},
        array<packed_t, N_RANKS>{S(0,   0), S(17, -18), S(9, -11), S(-11,  -5), S(-1, -24), S(26,  73), S(-186,   4), S(-32,  11)},
        array<packed_t, N_RANKS>{S(0,   0), S(19,  -9), S(1, -11), S(9, -26), S(28,  -5), S(-92,  56), S(-88, -74), S(-8,   1)},
        array<packed_t, N_RANKS>{S(0,   0), S(0,   3), S(-6,  -6), S(-35,  10), S(-46,  13), S(-98,  33), S(-7, -45), S(-35,  -5)},
        array<packed_t, N_RANKS>{S(0,   0), S(12,  -3), S(17, -15), S(17, -15), S(-5, -14), S(-36,   5), S(-101, -52), S(-18,  -1)},
        array<packed_t, N_RANKS>{S(0,   0), S(-8,  -5), S(-22,   1), S(-16,  -6), S(25, -22), S(-27,  10), S(52,  39), S(-14,  -2)},
        array<packed_t, N_RANKS>{S(0,   0), S(32, -22), S(19, -15), S(-9,  -6), S(-29,  13), S(-7,  23), S(-50, -39), S(-27,  18)},
        array<packed_t, N_RANKS>{S(0,   0), S(16, -57), S(17, -32), S(-18,  -7), S(-31,  24), S(-11,  24), S(-225, -49), S(-30,   5)}},
};

constexpr array<array<array<packed_t, N_RANKS>, N_FILES / 2>, 2> KingStorm = {
  array<array<packed_t, N_RANKS>, N_FILES / 2>{
        array<packed_t, N_RANKS>{S(-6,  36), S(144,  -4), S(-13,  26), S(-7,   1), S(-12,  -3), S(-8,  -7), S(-19,   8), S(-28,  -2)},
        array<packed_t, N_RANKS>{S(-17,  60), S(64,  17), S(-9,  21), S(8,  12), S(3,   9), S(6,  -2), S(-5,   2), S(-16,   8)},
        array<packed_t, N_RANKS>{S(2,  48), S(15,  30), S(-17,  20), S(-13,  10), S(-1,   6), S(7,   3), S(8,  -7), S(7,   8)},
        array<packed_t, N_RANKS>{S(-1,  25), S(15,  22), S(-31,  10), S(-22,   1), S(-15,   4), S(13, -10), S(3,  -5), S(-20,   8)}},
  array<array<packed_t, N_RANKS>, N_FILES / 2>{
        array<packed_t, N_RANKS>{S(0,   0), S(-18, -16), S(-18,  -2), S(27, -24), S(10,  -6), S(15, -24), S(-6,   9), S(9,  30)},
        array<packed_t, N_RANKS>{S(0,   0), S(-15, -42), S(-3, -15), S(53, -17), S(15,  -5), S(20, -28), S(-12, -17), S(-34,   5)},
        array<packed_t, N_RANKS>{S(0,   0), S(-34, -62), S(-15, -13), S(9,  -6), S(6,  -2), S(-2, -17), S(-5, -21), S(-3,   3)},
        array<packed_t, N_RANKS>{S(0,   0), S(-1, -26), S(-27, -19), S(-21,   4), S(-10,  -6), S(7, -35), S(66, -29), S(11,  25)}},
};

/* Safety Evaluation Terms */

constexpr packed_t SafetyKnightWeight = S(48, 41);
constexpr packed_t SafetyBishopWeight = S(24, 35);
constexpr packed_t SafetyRookWeight = S(36, 8);
constexpr packed_t SafetyQueenWeight = S(30, 6);

constexpr packed_t SafetyAttackValue = S(45, 34);
constexpr packed_t SafetyWeakSquares = S(42, 41);
constexpr packed_t SafetyNoEnemyQueens = S(-237, -259);
constexpr packed_t SafetySafeQueenCheck = S(93, 83);
constexpr packed_t SafetySafeRookCheck = S(90, 98);
constexpr packed_t SafetySafeBishopCheck = S(59, 59);
constexpr packed_t SafetySafeKnightCheck = S(112, 117);
constexpr packed_t SafetyAdjustment = S(-74, -26);

constexpr array<array<packed_t, N_RANKS>, 2> SafetyShelter = {
   array<packed_t, N_RANKS>{S(-2,   7), S(-1,  13), S(0,   8), S(4,   7), S(6,   2), S(-1,   0), S(2,   0), S(0, -13)},
   array<packed_t, N_RANKS>{S(0,   0), S(-2,  13), S(-2,   9), S(4,   5), S(3,   1), S(-3,   0), S(-2,   0), S(-1,  -9)},
}, 
SafetyStorm = {
   array<packed_t, N_RANKS>{S(-4,  -1), S(-8,   3), S(0,   5), S(1,  -1), S(3,   6), S(-2,  20), S(-2,  18), S(2, -12)},
   array<packed_t, N_RANKS>{S(0,   0), S(1,   0), S(-1,   4), S(0,   0), S(0,   5), S(-1,   1), S(1,   0), S(1,   0)},
};

/* Passed Pawn Evaluation Terms */

constexpr array<array<array<packed_t, N_RANKS>, 2>, 2> PassedPawn = {
  array<array<packed_t, N_RANKS>, 2>{
        array<packed_t, N_RANKS>{S(0,   0), S(-39,  -4), S(-43,  25), S(-62,  28), S(8,  19), S(97,  -4), S(162,  46), S(0,   0)},
        array<packed_t, N_RANKS>{S(0,   0), S(-28,  13), S(-40,  42), S(-56,  44), S(-2,  56), S(114,  54), S(193,  94), S(0,   0)}},
  array<array<packed_t, N_RANKS>, 2>{
        array<packed_t, N_RANKS>{S(0,   0), S(-28,  29), S(-47,  36), S(-60,  54), S(8,  65), S(106,  76), S(258, 124), S(0,   0)},
        array<packed_t, N_RANKS>{S(0,   0), S(-28,  23), S(-40,  35), S(-55,  60), S(8,  89), S(95, 166), S(124, 293), S(0,   0)}},
};

constexpr array<packed_t, N_FILES> PassedFriendlyDistance = {
    S(0,   0), S(-3,   1), S(0,  -4), S(5, -13), S(6, -19), S(-9, -19), S(-9,  -7), S(0,   0),
}, 
PassedEnemyDistance = {
    S(0,   0), S(5,  -1), S(7,   0), S(9,  11), S(0,  25), S(1,  37), S(16,  37), S(0,   0),
};

constexpr packed_t PassedSafePromotionPath = S(-49, 57);

/* Threat Evaluation Terms */

constexpr packed_t ThreatWeakPawn = S(-11, -38);
constexpr packed_t ThreatMinorAttackedByPawn = S(-55, -83);
constexpr packed_t ThreatMinorAttackedByMinor = S(-25, -45);
constexpr packed_t ThreatMinorAttackedByMajor = S(-30, -55);
constexpr packed_t ThreatRookAttackedByLesser = S(-48, -28);
constexpr packed_t ThreatMinorAttackedByKing = S(-43, -21);
constexpr packed_t ThreatRookAttackedByKing = S(-33, -18);
constexpr packed_t ThreatQueenAttackedByOne = S(-50, -7);
constexpr packed_t ThreatOverloadedPieces = S(-7, -16);
constexpr packed_t ThreatByPawnPush = S(15, 32);

/* Space Evaluation Terms */

constexpr packed_t SpaceRestrictPiece = S(-4, -1);
constexpr packed_t SpaceRestrictEmpty = S(-4, -2);
constexpr packed_t SpaceCenterControl = Pack(4, 0, 0, 0);   // Opening only

/* Closedness Evaluation Terms */

constexpr array<packed_t, 9> ClosednessKnightAdjustment = {
    S(-7,  10), S(-7,  29), S(-9,  37), S(-5,  37),
    S(-3,  44), S(-1,  36), S(1,  33), S(-10,  51),
    S(-7,  30),
},
ClosednessRookAdjustment = {
    S(42,  43), S(-6,  80), S(3,  59), S(-5,  47),
    S(-7,  41), S(-3,  23), S(-6,  11), S(-17,  11),
    S(-34, -12),
};

/* Complexity Evaluation Terms */

constexpr packed_t ComplexityTotalPawns = S(0, 8);
constexpr packed_t ComplexityPawnFlanks = S(0, 82);
constexpr packed_t ComplexityPawnEndgame = S(0, 76);
constexpr packed_t ComplexityAdjustment = S(0, -157);

/* General Evaluation Terms */

#undef S

void initEvalInfo(Thread* thread, State* state, EvalInfo* ei)
{
    uint64 white = state->board_.colors_[WHITE];
    uint64 black = state->board_.colors_[BLACK];

    uint64 pawns = state->board_.Pawns();
    uint64 bishops = state->board_.Bishops() | state->board_.Queens();
    uint64 rooks = state->board_.Rooks() | state->board_.Queens();
    uint64 kings = state->board_.Kings();

    // Save some general information about the pawn structure for later
    ei->pawnAttacks[WHITE] = pawnAttackSpan(white & pawns, Filled, WHITE);
    ei->pawnAttacks[BLACK] = pawnAttackSpan(black & pawns, Filled, BLACK);
    ei->pawnAttacksBy2[WHITE] = pawnAttackDouble(white & pawns, Filled, WHITE);
    ei->pawnAttacksBy2[BLACK] = pawnAttackDouble(black & pawns, Filled, BLACK);
    ei->rammedPawns[WHITE] = pawnAdvance(black & pawns, ~(white & pawns), BLACK);
    ei->rammedPawns[BLACK] = pawnAdvance(white & pawns, ~(black & pawns), WHITE);
    ei->blockedPawns[WHITE] = pawnAdvance(white | black, ~(white & pawns), BLACK);
    ei->blockedPawns[BLACK] = pawnAdvance(white | black, ~(black & pawns), WHITE);

    // Compute an area for evaluating our King's safety.
    // The definition of the King Area can be found in masks.c
    ei->kingSquare[WHITE] = lsb(white & kings);
    ei->kingSquare[BLACK] = lsb(black & kings);
    ei->kingAreas[WHITE] = kingAreaMasks(WHITE, ei->kingSquare[WHITE]);
    ei->kingAreas[BLACK] = kingAreaMasks(BLACK, ei->kingSquare[BLACK]);

    // Exclude squares attacked by our opponents, our blocked pawns, and our own King
    ei->mobilityAreas[WHITE] = ~(ei->pawnAttacks[BLACK] | (white & kings) | ei->blockedPawns[WHITE]);
    ei->mobilityAreas[BLACK] = ~(ei->pawnAttacks[WHITE] | (black & kings) | ei->blockedPawns[BLACK]);

    // Init part of the attack tables. By doing this step here, evaluatePawns()
    // can start by setting up the attackedBy2 table, since King attacks are resolved
    ei->attacked[WHITE] = ei->attackedBy[WHITE][KING] = kingAttacks(ei->kingSquare[WHITE]);
    ei->attacked[BLACK] = ei->attackedBy[BLACK][KING] = kingAttacks(ei->kingSquare[BLACK]);

    // For mobility, we allow bishops to attack through each other
    ei->occupiedMinusBishops[WHITE] = (white | black) ^ (white & bishops);
    ei->occupiedMinusBishops[BLACK] = (white | black) ^ (black & bishops);

    // For mobility, we allow rooks to attack through each other
    ei->occupiedMinusRooks[WHITE] = (white | black) ^ (white & rooks);
    ei->occupiedMinusRooks[BLACK] = (white | black) ^ (black & rooks);

    // Init all of the King Safety information
    ei->kingAttacksCount[WHITE] = ei->kingAttacksCount[BLACK] = 0;
    ei->kingAttackersCount[WHITE] = ei->kingAttackersCount[BLACK] = 0;
    ei->kingAttackersWeight[WHITE] = ei->kingAttackersWeight[BLACK] = 0;

    // Try to read a hashed Pawn King Eval. Otherwise, start from scratch
    ei->pkentry = getCachedPawnKingEval(thread, state);
    ei->passedPawns = ei->pkentry == NULL ? 0ull : ei->pkentry->passed;
    ei->pkeval[WHITE] = ei->pkentry == NULL ? 0 : ei->pkentry->eval;
    ei->pkeval[BLACK] = ei->pkentry == NULL ? 0 : 0;
    ei->pksafety[WHITE] = ei->pkentry == NULL ? 0 : ei->pkentry->safetyw;
    ei->pksafety[BLACK] = ei->pkentry == NULL ? 0 : ei->pkentry->safetyb;

    // Roc part
    // ei->area_[WHITE] = 
}

template<int US> packed_t evaluatePawns(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;
    const int Forward = (US == WHITE) ? 8 : -8;

    packed_t eval = 0, pkeval = 0;

    // Store off pawn attacks for king safety and threat computations
    ei->attackedBy2[US] = ei->pawnAttacks[US] & ei->attacked[US];
    ei->attacked[US] |= ei->pawnAttacks[US];
    ei->attackedBy[US][PAWN] = ei->pawnAttacks[US];

    // Update King Safety calculations
    uint64 attacks = ei->pawnAttacks[US] & ei->kingAreas[THEM];
    ei->kingAttacksCount[THEM] += popcount(attacks);

    // Pawn hash holds the rest of the pawn evaluation
    if (ei->pkentry != NULL) return eval;

    uint64 pawns = board.Pawns();
    uint64 myPawns = pawns & board.colors_[US], enemyPawns = pawns & board.colors_[THEM];
    uint64 tempPawns = myPawns;

    // Evaluate each pawn (but not for being passed)
    while (tempPawns) 
    {
        // Pop off the next pawn
        int sq = poplsb(&tempPawns);
        if (TRACE) TheTrace.PawnValue[US]++;
        if (TRACE) TheTrace.PawnPSQT[relativeSquare(US, sq)][US]++;

        uint64 neighbors = myPawns & adjacentFilesMasks(FileOf(sq));
        uint64 backup = myPawns & passedPawnMasks(THEM, sq);
        uint64 stoppers = enemyPawns & passedPawnMasks(US, sq);
        uint64 threats = enemyPawns & pawnAttacks(US, sq);
        uint64 support = myPawns & pawnAttacks(THEM, sq);
        uint64 pushThreats = enemyPawns & pawnAttacks(US, sq + Forward);
        uint64 pushSupport = myPawns & pawnAttacks(THEM, sq + Forward);
        uint64 leftovers = stoppers ^ threats ^ pushThreats;

        // Save passed pawn information for later evaluation
        if (!stoppers) setBit(&ei->passedPawns, sq);

        // Apply a bonus for pawns which will become passers by advancing a
        // square then exchanging our supporters with the remaining stoppers
        else if (!leftovers && popcount(pushSupport) >= popcount(pushThreats)) {
            int flag = popcount(support) >= popcount(threats);
            pkeval += PawnCandidatePasser[flag][OwnRankOf<US>(sq)];
            if (TRACE) TheTrace.PawnCandidatePasser[flag][OwnRankOf<US>(sq)][US]++;
        }

        // Apply a penalty if the pawn is isolated. We consider pawns that
        // are able to capture another pawn to not be isolated, as they may
        // have the potential to deisolate by capturing, or be traded away
        if (!threats && !neighbors) {
            pkeval += PawnIsolated[FileOf(sq)];
            if (TRACE) TheTrace.PawnIsolated[FileOf(sq)][US]++;
        }

        // Apply a penalty if the pawn is stacked. We adjust the bonus for when
        // the pawn appears to be a candidate to unstack. This occurs when the
        // pawn is not passed but may capture or be recaptured by our own pawns,
        // and when the pawn may freely advance on a file and then be traded away
        if (Multiple(File[FileOf(sq)] & myPawns)) 
        {
            int flag = (stoppers && (threats || neighbors)) || (stoppers & ~forwardFileMasks(US, sq));
            pkeval += PawnStacked[flag][FileOf(sq)];
            if (TRACE) TheTrace.PawnStacked[flag][FileOf(sq)][US]++;
        }

        // Apply a penalty if the pawn is backward. We follow the usual definition
        // of backwards, but also specify that the pawn is not both isolated and
        // backwards at the same time. We don't give backward pawns a connected bonus
        if (neighbors && pushThreats && !backup) {
            int flag = !(File[FileOf(sq)] & enemyPawns);
            pkeval += PawnBackwards[flag][OwnRankOf<US>(sq)];
            if (TRACE) TheTrace.PawnBackwards[flag][OwnRankOf<US>(sq)][US]++;
        }

        // Apply a bonus if the pawn is connected and not backwards. We consider a
        // pawn to be connected when there is a pawn lever or the pawn is supported
        else if (pawnConnectedMasks(US, sq) & myPawns) {
            pkeval += PawnConnected32[RelativeSquare32<US>(sq)];
            if (TRACE) TheTrace.PawnConnected32[RelativeSquare32<US>(sq)][US]++;
        }
    }

    ei->pkeval[US] = pkeval; // Save eval for the Pawn Hash

    return eval;
}


/*
template<bool me> INLINE packed_t EvalKnights(EvalInfo* ei, const Board_& board)
{
    ei->attackedBy[me][KNIGHT] = 0ull;

    packed_t eval = 0;
    for (uint64 b, u = board.Knights(me); T(u); u ^= b)
    {
        int sq = lsb(u);
        b = Bit(sq);
        uint64 att = NAtt[sq];
        if (uint64 a = att & EI.area[opp])
            EI.king_att[me] += Single(a) ? KingNAttack1 : KingNAttack;
        state[0].threat |= att & board.Major(opp);
        uint64 control = att & EI.free[me];
        NOTICE(EI.score, pop(control));
        IncV(EI.score, RO->MobKnight[0][pop(control)]);
        NOTICE(EI.score, NO_INFO);
        FakeV(EI.score, (64 * pop(control & RO->LocusN[EI.king[opp]]) - N_LOCUS * pop(control)) * Pack4(1, 1, 1, 1));
        IncV(EI.score, RO->MobKnight[1][pop(control & RO->LocusN[EI.king[opp]])]);
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
}
*/

template<int US> packed_t PrevalKnights(EvalInfo* ei, const Board_& board)
{
    packed_t eval = 0;

    ei->attackedBy[US][KNIGHT] = 0ull;

    // Evaluate each knight
    uint64 tempKnights = board.Knights(US);
    while (tempKnights)
    {
        // Pop off the next knight
        int sq = poplsb(&tempKnights);

        // Compute possible attacks and store off information for king safety
        uint64 attacks = knightAttacks(sq);
        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][KNIGHT] |= attacks;
    }

    return eval;
}

template<int US> packed_t evaluateKnights(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;

    packed_t eval = 0;

    uint64 enemyPawns = board.Pawns(THEM);
    uint64 tempKnights = board.Knights(US);

    // Evaluate each knight
    while (tempKnights)
    {
        // Pop off the next knight
        int sq = poplsb(&tempKnights);
        uint64 attacks = knightAttacks(sq);

        if (TRACE) TheTrace.KnightValue[US]++;
        if (TRACE) TheTrace.KnightPSQT[relativeSquare(US, sq)][US]++;

        // Apply a bonus if the knight is on an outpost square, and cannot be attacked
        // by an enemy pawn. Increase the bonus if one of our pawns supports the knight
        if (HasBit(outpostRanksMasks(US), sq) && !(outpostSquareMasks(US, sq) & enemyPawns)) 
        {
            bool outside = HasBit(File[0] | File[7], sq);
            bool defended = HasBit(ei->pawnAttacks[US], sq);
            eval += KnightOutpost[outside][defended];
            if (TRACE) TheTrace.KnightOutpost[outside][defended][US]++;
        }

        // Apply a bonus if the knight is behind a pawn
        if (HasBit(pawnAdvance(board.Pawns(), 0ull, THEM), sq)) {
            eval += KnightBehindPawn;
            if (TRACE) TheTrace.KnightBehindPawn[US]++;
        }

        // Apply a penalty if the knight is far from both kings
        int kingDistance = Min(distanceBetween(sq, ei->kingSquare[THEM]), distanceBetween(sq, ei->kingSquare[US]));
        if (kingDistance >= 4) {
            eval += KnightInSiberia[kingDistance - 4];
            if (TRACE) TheTrace.KnightInSiberia[kingDistance - 4][US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the knight
        int count = popcount(ei->mobilityAreas[US] & attacks);
        eval += KnightMobility[count];
        if (TRACE) TheTrace.KnightMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyKnightWeight;
            if (TRACE) TheTrace.SafetyKnightWeight[THEM]++;
        }
    }

    return eval;
}

template<int US> packed_t PrevalBishops(EvalInfo* ei, const Board_& board)
{

    packed_t eval = 0;

    ei->attackedBy[US][BISHOP] = 0ull;

    // Evaluate each bishop
    uint64 tempBishops = board.Bishops(US);
    while (tempBishops)
    {
        // Pop off the next Bishop
        int sq = poplsb(&tempBishops);

        // Compute possible attacks and store off information for king safety
        uint64 attacks = bishopAttacks(sq, ei->occupiedMinusBishops[US]);
        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][BISHOP] |= attacks;
    }

    return eval;
}

template<int US> packed_t evaluateBishops(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;

    packed_t eval = 0;

    uint64 enemyPawns = board.Pawns(THEM);
    uint64 tempBishops = board.Bishops(US);

    // Apply a bonus for having a pair of bishops
    if ((tempBishops & LightArea) && (tempBishops & DarkArea)) 
    {
        eval += BishopPair;
        if (TRACE) TheTrace.BishopPair[US]++;
    }

    // Evaluate each bishop
    while (tempBishops) 
    {
        // Pop off the next Bishop
        int sq = poplsb(&tempBishops);
        if (TRACE) TheTrace.BishopValue[US]++;
        if (TRACE) TheTrace.BishopPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        uint64 attacks = bishopAttacks(sq, ei->occupiedMinusBishops[US]);

        // Apply a penalty for the bishop based on number of rammed pawns
        // of our own colour, which reside on the same shade of square as the bishop
        int count = popcount(ei->rammedPawns[US] & squaresOfMatchingColour(sq));
        eval += count * BishopRammedPawns;
        if (TRACE) TheTrace.BishopRammedPawns[US] += count;

        // Apply a bonus if the bishop is on an outpost square, and cannot be attacked
        // by an enemy pawn. Increase the bonus if one of our pawns supports the bishop.
        if (HasBit(outpostRanksMasks(US), sq) && !(outpostSquareMasks(US, sq) & enemyPawns)) 
        {
            bool outside = HasBit(File[0] | File[7], sq);
            bool defended = HasBit(ei->pawnAttacks[US], sq);
            eval += BishopOutpost[outside][defended];
            if (TRACE) TheTrace.BishopOutpost[outside][defended][US]++;
        }

        // Apply a bonus if the bishop is behind a pawn
        if (HasBit(pawnAdvance(board.Pawns(), 0ull, THEM), sq)) {
            eval += BishopBehindPawn;
            if (TRACE) TheTrace.BishopBehindPawn[US]++;
        }

        // Apply a bonus when controlling both central squares on a long diagonal
        if (HasBit(LONG_DIAGONALS & ~CENTER_SQUARES, sq)
            && Multiple(bishopAttacks(sq, board.Pawns()) & CENTER_SQUARES)) {
            eval += BishopLongDiagonal;
            if (TRACE) TheTrace.BishopLongDiagonal[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the bishop
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += BishopMobility[count];
        if (TRACE) TheTrace.BishopMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyBishopWeight;
            if (TRACE) TheTrace.SafetyBishopWeight[THEM]++;
        }
    }

    return eval;
}

template<int US> packed_t PrevalRooks(EvalInfo* ei, const Board_& board)
{
    packed_t eval = 0;

    ei->attackedBy[US][ROOK] = 0ull;

    // Evaluate each rook
    uint64 tempRooks = board.Rooks() & board.colors_[US];
    while (tempRooks)
    {
        // Pop off the next rook
        int sq = poplsb(&tempRooks);

        // Compute possible attacks and store off information for king safety
        uint64 attacks = rookAttacks(sq, ei->occupiedMinusRooks[US]);
        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][ROOK] |= attacks;
    }

    return eval;
}

template<int US> packed_t evaluateRooks(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;

    packed_t eval = 0;

    uint64 myPawns = board.Pawns(US), enemyPawns = board.Pawns(THEM);

    // Evaluate each rook
    uint64 tempRooks = board.Rooks(US);
    while (tempRooks)
    {
        // Pop off the next rook
        int sq = poplsb(&tempRooks);
        if (TRACE) TheTrace.RookValue[US]++;
        if (TRACE) TheTrace.RookPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        uint64 attacks = rookAttacks(sq, ei->occupiedMinusRooks[US]);

        // Rook is on a semi-open file if there are no pawns of the rook's
        // colour on the file. If there are no pawns at all, it is an open file
        if (!(myPawns & File[FileOf(sq)])) {
            bool open = !(enemyPawns & File[FileOf(sq)]);
            eval += RookFile[open];
            if (TRACE) TheTrace.RookFile[open][US]++;
        }

        // Rook gains a bonus for being located on seventh rank relative to its
        // colour so long as the enemy king is on the last two ranks of the state
        if (OwnRankOf<US>(sq) == 6
            && OwnRankOf<US>(ei->kingSquare[THEM]) >= 6) {
            eval += RookOnSeventh;
            if (TRACE) TheTrace.RookOnSeventh[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the rook
        int count = popcount(ei->mobilityAreas[US] & attacks);
        eval += RookMobility[count];
        if (TRACE) TheTrace.RookMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyRookWeight;
            if (TRACE) TheTrace.SafetyRookWeight[THEM]++;
        }
    }

    return eval;
}

template<int US> packed_t PrevalQueens(EvalInfo* ei, const Board_& board)
{
    packed_t eval = 0;

    ei->attackedBy[US][QUEEN] = 0ull;

    // Evaluate each queen
    uint64 tempQueens = board.Queens(US);
    while (tempQueens)
    {
        // Pop off the next queen
        int sq = poplsb(&tempQueens);

        // Compute possible attacks and store off information for king safety
        uint64 attacks = rookAttacks(sq, ei->occupiedMinusRooks[US]) | bishopAttacks(sq, ei->occupiedMinusBishops[US]);

        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][QUEEN] |= attacks;
    }

    return eval;
}

template<int US> packed_t evaluateQueens(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;

    packed_t eval = 0;

    // Evaluate each queen
    uint64 tempQueens = board.Queens(US);
    while (tempQueens)
    {
        // Pop off the next queen
        int sq = poplsb(&tempQueens);
        if (TRACE) TheTrace.QueenValue[US]++;
        if (TRACE) TheTrace.QueenPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        uint64 attacks = rookAttacks(sq, ei->occupiedMinusRooks[US]) | bishopAttacks(sq, ei->occupiedMinusBishops[US]);

        // Apply a penalty if the Queen is at risk for a discovered attack
        if (discoveredAttacks(board, sq, US)) {
            eval += QueenRelativePin;
            if (TRACE) TheTrace.QueenRelativePin[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the queen
        int count = popcount(ei->mobilityAreas[US] & attacks);
        eval += QueenMobility[count];
        if (TRACE) TheTrace.QueenMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyQueenWeight;
            if (TRACE) TheTrace.SafetyQueenWeight[THEM]++;
        }
    }

    return eval;
}

template<int US> void evaluateKingsPawns(EvalInfo* ei, const Board_& board)
{
    // Skip computations if results are cached in the Pawn King Table
    if (ei->pkentry != NULL)
        return;

    const int THEM = !US;

    int dist, blocked;

    uint64 myPawns = board.Pawns(US), enemyPawns = board.Pawns(THEM);

    int kingSq = ei->kingSquare[US];

    // Evaluate based on the number of files between our King and the nearest
    // file-wise pawn. If there is no pawn, kingPawnFileDistance() returns the
    // same distance for both sides causing this evaluation term to be neutral
    dist = kingPawnFileDistance(board.Pawns(), kingSq);
    ei->pkeval[US] += KingPawnFileProximity[dist];
    if (TRACE) TheTrace.KingPawnFileProximity[dist][US]++;

    // Evaluate King Shelter & King Storm threat by looking at the file of our King,
    // as well as the adjacent files. When looking at pawn distances, we will use a
    // distance of 7 to denote a missing pawn, since distance 7 is not possible otherwise.
    for (int file = Max(0, FileOf(kingSq) - 1); file <= Min(N_FILES - 1, FileOf(kingSq) + 1); file++) {

        // Find closest friendly pawn at or above our King on a given file
        uint64 ours = myPawns & File[file] & forwardRanksMasks(US, rankOf(kingSq));
        int ourDist = !ours ? 7 : abs(rankOf(kingSq) - rankOf(backmost(US, ours)));

        // Find closest enemy pawn at or above our King on a given file
        uint64 theirs = enemyPawns & File[file] & forwardRanksMasks(US, rankOf(kingSq));
        int theirDist = !theirs ? 7 : abs(rankOf(kingSq) - rankOf(backmost(US, theirs)));

        // Evaluate King Shelter using pawn distance. Use separate evaluation
        // depending on the file, and if we are looking at the King's file
        ei->pkeval[US] += KingShelter[file == FileOf(kingSq)][file][ourDist];
        if (TRACE) TheTrace.KingShelter[file == FileOf(kingSq)][file][ourDist][US]++;

        // Update the Shelter Safety
        ei->pksafety[US] += SafetyShelter[file == FileOf(kingSq)][ourDist];
        if (TRACE) TheTrace.SafetyShelter[file == FileOf(kingSq)][ourDist][US]++;

        // Evaluate King Storm using enemy pawn distance. Use a separate evaluation
        // depending on the file, and if the opponent's pawn is blocked by our own
        blocked = (ourDist != 7 && (ourDist == theirDist - 1));
        ei->pkeval[US] += KingStorm[blocked][mirrorFile(file)][theirDist];
        if (TRACE) TheTrace.KingStorm[blocked][mirrorFile(file)][theirDist][US]++;

        // Update the Storm Safety
        ei->pksafety[US] += SafetyStorm[blocked][theirDist];
        if (TRACE) TheTrace.SafetyStorm[blocked][theirDist][US]++;
    }

    return;
}

template<int US> packed_t evaluateKings(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;
    packed_t eval = 0;

    uint64 enemyQueens = board.Queens(THEM);
    uint64 defenders = board.Pawns(US) | board.Knights(US) | board.Bishops(US);

    int kingSq = ei->kingSquare[US];
    if (TRACE) TheTrace.KingValue[US]++;
    if (TRACE) TheTrace.KingPSQT[relativeSquare(US, kingSq)][US]++;

    // Bonus for our pawns and minors sitting within our king area
    int count = popcount(defenders & ei->kingAreas[US]);
    eval += KingDefenders[count];
    if (TRACE) TheTrace.KingDefenders[count][US]++;

    // Perform King Safety when we have two attackers, or
    // one attacker with a potential for a Queen attacker
    if (ei->kingAttackersCount[US] > 1 - popcount(enemyQueens)) {

        // Weak squares are attacked by the enemy, defended no more
        // than once and only defended by our Queens or our King
        uint64 weak = ei->attacked[THEM]
                & ~ei->attackedBy2[US]
                & (~ei->attacked[US] | ei->attackedBy[US][QUEEN] | ei->attackedBy[US][KING]);

        // Usually the King Area is 9 squares. Scale are attack counts to account for
        // when the king is in an open area and expects more attacks, or the opposite
        int scaledAttackCounts = (9 * ei->kingAttacksCount[US]) / popcount(ei->kingAreas[US]);

        // Safe target squares are defended or are weak and attacked by two.
        // We exclude squares containing pieces which we cannot capture.
        uint64 safe = ~board.colors_[THEM]
            & (~ei->attacked[US] | (weak & ei->attackedBy2[THEM]));

        // Find square and piece combinations which would check our King
        uint64 occupied = board.colors_[WHITE] | board.colors_[BLACK];
        uint64 knightThreats = knightAttacks(kingSq);
        uint64 bishopThreats = bishopAttacks(kingSq, occupied);
        uint64 rookThreats = rookAttacks(kingSq, occupied);
        uint64 queenThreats = bishopThreats | rookThreats;

        // Identify if there are pieces which can move to the checking squares safely.
        // We consider forking a Queen to be a safe check, even with our own Queen.
        uint64 knightChecks = knightThreats & safe & ei->attackedBy[THEM][KNIGHT];
        uint64 bishopChecks = bishopThreats & safe & ei->attackedBy[THEM][BISHOP];
        uint64 rookChecks = rookThreats & safe & ei->attackedBy[THEM][ROOK];
        uint64 queenChecks = queenThreats & safe & ei->attackedBy[THEM][QUEEN];

        packed_t safety = ei->kingAttackersWeight[US];

        safety += SafetyAttackValue * scaledAttackCounts
            + SafetyWeakSquares * popcount(weak & ei->kingAreas[US])
            + SafetyNoEnemyQueens * !enemyQueens
            + SafetySafeQueenCheck * popcount(queenChecks)
            + SafetySafeRookCheck * popcount(rookChecks)
            + SafetySafeBishopCheck * popcount(bishopChecks)
            + SafetySafeKnightCheck * popcount(knightChecks)
            + ei->pksafety[US]
            + SafetyAdjustment;

        if (TRACE) TheTrace.SafetyAttackValue[US] = scaledAttackCounts;
        if (TRACE) TheTrace.SafetyWeakSquares[US] = popcount(weak & ei->kingAreas[US]);
        if (TRACE) TheTrace.SafetyNoEnemyQueens[US] = !enemyQueens;
        if (TRACE) TheTrace.SafetySafeQueenCheck[US] = popcount(queenChecks);
        if (TRACE) TheTrace.SafetySafeRookCheck[US] = popcount(rookChecks);
        if (TRACE) TheTrace.SafetySafeBishopCheck[US] = popcount(bishopChecks);
        if (TRACE) TheTrace.SafetySafeKnightCheck[US] = popcount(knightChecks);
        if (TRACE) TheTrace.SafetyAdjustment[US] = 1;

        // Convert safety to an MG and EG score
        score_t mg = ScoreMG(safety), eg = ScoreEG(safety);
        eval += MakeScore(-mg * Max<score_t>(0, mg) / 720, -Max<score_t>(0, eg) / 20);
        if (TRACE) TheTrace.safety[US] = safety;
    }

    else if (TRACE) 
    {
        TheTrace.SafetyKnightWeight[US] = 0;
        TheTrace.SafetyBishopWeight[US] = 0;
        TheTrace.SafetyRookWeight[US] = 0;
        TheTrace.SafetyQueenWeight[US] = 0;

        for (int i = 0; i < 8; i++) {
            TheTrace.SafetyShelter[0][i][US] = 0;
            TheTrace.SafetyShelter[1][i][US] = 0;
            TheTrace.SafetyStorm[0][i][US] = 0;
            TheTrace.SafetyStorm[1][i][US] = 0;
        }
    }

    return eval;
}

template<int US> packed_t evaluatePassed(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;

    int sq, rank, dist, flag, canAdvance, safeAdvance;
    packed_t eval = 0;

    uint64 bitboard;
    uint64 myPassers = board.colors_[US] & ei->passedPawns;
    uint64 occupied = board.colors_[WHITE] | board.colors_[BLACK];
    uint64 tempPawns = myPassers;

    // Evaluate each passed pawn
    while (tempPawns) 
    {
        // Pop off the next passed Pawn
        sq = poplsb(&tempPawns);
        rank = OwnRankOf<US>(sq);
        bitboard = pawnAdvance(1ull << sq, 0ull, US);

        // Evaluate based on rank, ability to advance, and safety
        canAdvance = !(bitboard & occupied);
        safeAdvance = !(bitboard & ei->attacked[THEM]);
        eval += PassedPawn[canAdvance][safeAdvance][rank];
        if (TRACE) TheTrace.PassedPawn[canAdvance][safeAdvance][rank][US]++;

        // Short-circuit evaluation for additional passers on a file
        if (Multiple(forwardFileMasks(US, sq) & myPassers)) continue;

        // Evaluate based on distance from our king
        dist = distanceBetween(sq, ei->kingSquare[US]);
        eval += dist * PassedFriendlyDistance[rank];
        if (TRACE) TheTrace.PassedFriendlyDistance[rank][US] += dist;

        // Evaluate based on distance from their king
        dist = distanceBetween(sq, ei->kingSquare[THEM]);
        eval += dist * PassedEnemyDistance[rank];
        if (TRACE) TheTrace.PassedEnemyDistance[rank][US] += dist;

        // Apply a bonus when the path to promoting is uncontested
        bitboard = forwardRanksMasks(US, rankOf(sq)) & File[FileOf(sq)];
        flag = !(bitboard & (board.colors_[THEM] | ei->attacked[THEM]));
        eval += flag * PassedSafePromotionPath;
        if (TRACE) TheTrace.PassedSafePromotionPath[US] += flag;
    }

    return eval;
}

template<int US> packed_t evaluateThreats(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;
    const uint64 Rank3Rel = US == WHITE ? Line[2] : Line[5];

    int count;
    packed_t eval = 0;

    uint64 friendly = board.colors_[US];
    uint64 enemy = board.colors_[THEM];
    uint64 occupied = friendly | enemy;

    uint64 pawns = board.Pawns(US);
    uint64 knights = board.Knights(US);
    uint64 bishops = board.Bishops(US);
    uint64 rooks = board.Rooks(US);
    uint64 queens = board.Queens(US);

    uint64 attacksByPawns = ei->attackedBy[THEM][PAWN];
    uint64 attacksByMinors = ei->attackedBy[THEM][KNIGHT] | ei->attackedBy[THEM][BISHOP];
    uint64 attacksByMajors = ei->attackedBy[THEM][ROOK] | ei->attackedBy[THEM][QUEEN];

    // Squares with more attackers, few defenders, and no pawn support
    uint64 poorlyDefended = (ei->attacked[THEM] & ~ei->attacked[US])
        | (ei->attackedBy2[THEM] & ~ei->attackedBy2[US] & ~ei->attackedBy[US][PAWN]);

    uint64 weakMinors = (knights | bishops) & poorlyDefended;

    // A friendly minor or major is overloaded if attacked and defended by exactly one
    uint64 overloaded = (knights | bishops | rooks | queens)
        & ei->attacked[US] & ~ei->attackedBy2[US]
        & ei->attacked[THEM] & ~ei->attackedBy2[THEM];

    // Look for enemy non-pawn pieces which we may threaten with a pawn advance.
    // Don't consider pieces we already threaten, pawn moves which would be countered
    // by a pawn capture, and squares which are completely unprotected by our pieces.
    uint64 pushThreat = pawnAdvance(pawns, occupied, US);
    pushThreat |= pawnAdvance(pushThreat & ~attacksByPawns & Rank3Rel, occupied, US);
    pushThreat &= ~attacksByPawns & (ei->attacked[US] | ~ei->attacked[THEM]);
    pushThreat = pawnAttackSpan(pushThreat, enemy & ~ei->attackedBy[US][PAWN], US);

    // Penalty for each of our poorly supported pawns
    count = popcount(pawns & ~attacksByPawns & poorlyDefended);
    eval += count * ThreatWeakPawn;
    if (TRACE) TheTrace.ThreatWeakPawn[US] += count;

    // Penalty for pawn threats against our minors
    count = popcount((knights | bishops) & attacksByPawns);
    eval += count * ThreatMinorAttackedByPawn;
    if (TRACE) TheTrace.ThreatMinorAttackedByPawn[US] += count;

    // Penalty for any minor threat against minor pieces
    count = popcount((knights | bishops) & attacksByMinors);
    eval += count * ThreatMinorAttackedByMinor;
    if (TRACE) TheTrace.ThreatMinorAttackedByMinor[US] += count;

    // Penalty for all major threats against poorly supported minors
    count = popcount(weakMinors & attacksByMajors);
    eval += count * ThreatMinorAttackedByMajor;
    if (TRACE) TheTrace.ThreatMinorAttackedByMajor[US] += count;

    // Penalty for pawn and minor threats against our rooks
    count = popcount(rooks & (attacksByPawns | attacksByMinors));
    eval += count * ThreatRookAttackedByLesser;
    if (TRACE) TheTrace.ThreatRookAttackedByLesser[US] += count;

    // Penalty for king threats against our poorly defended minors
    count = popcount(weakMinors & ei->attackedBy[THEM][KING]);
    eval += count * ThreatMinorAttackedByKing;
    if (TRACE) TheTrace.ThreatMinorAttackedByKing[US] += count;

    // Penalty for king threats against our poorly defended rooks
    count = popcount(rooks & poorlyDefended & ei->attackedBy[THEM][KING]);
    eval += count * ThreatRookAttackedByKing;
    if (TRACE) TheTrace.ThreatRookAttackedByKing[US] += count;

    // Penalty for any threat against our queens
    count = popcount(queens & ei->attacked[THEM]);
    eval += count * ThreatQueenAttackedByOne;
    if (TRACE) TheTrace.ThreatQueenAttackedByOne[US] += count;

    // Penalty for any overloaded minors or majors
    count = popcount(overloaded);
    eval += count * ThreatOverloadedPieces;
    if (TRACE) TheTrace.ThreatOverloadedPieces[US] += count;

    // Bonus for giving threats by safe pawn pushes
    count = popcount(pushThreat);
    eval += count * ThreatByPawnPush;
    if (TRACE) TheTrace.ThreatByPawnPush[US] += count;

    return eval;
}

template<int US> packed_t evaluateSpace(EvalInfo* ei, const Board_& board)
{
    const int THEM = !US;

    packed_t eval = 0;

    uint64 friendly = board.colors_[US];
    uint64 enemy = board.colors_[THEM];

    // Squares we attack with more enemy attackers and no friendly pawn attacks
    uint64 uncontrolled = ei->attackedBy2[THEM] & ei->attacked[US]
        & ~ei->attackedBy2[US] & ~ei->attackedBy[US][PAWN];

    // Penalty for restricted piece moves
    int count = popcount(uncontrolled & (friendly | enemy));
    eval += count * SpaceRestrictPiece;
    if (TRACE) TheTrace.SpaceRestrictPiece[US] += count;

    count = popcount(uncontrolled & ~friendly & ~enemy);
    eval += count * SpaceRestrictEmpty;
    if (TRACE) TheTrace.SpaceRestrictEmpty[US] += count;

    // Bonus for uncontested central squares
    // This is mostly relevant in the opening and the early middlegame, while rarely correct
    // in the endgame where one rook or queen could control many uncontested squares.
    // Thus we don't apply this term when below a threshold of minors/majors count.
    count = popcount(~ei->attacked[THEM] & (ei->attacked[US] | friendly) & CENTER_BIG);
    eval += count * SpaceCenterControl;
    if (TRACE) TheTrace.SpaceCenterControl[US] += count;

    return eval;
}

packed_t evaluateClosedness(EvalInfo* ei, const Board_& board)
{
    int closedness, count;
    packed_t eval = 0;

    uint64 white = board.colors_[WHITE];
    uint64 black = board.colors_[BLACK];

    uint64 knights = board.Knights();
    uint64 rooks = board.Rooks();

    // Compute Closedness factor for this position
    closedness = 1 * popcount(board.Pawns())
            + 3 * popcount(ei->rammedPawns[WHITE])
            - 4 * openFileCount(board.Pawns());
    closedness = Max(0, Min(8, closedness / 3));

    // Evaluate Knights based on how Closed the position is
    count = popcount(white & knights) - popcount(black & knights);
    eval += count * ClosednessKnightAdjustment[closedness];
    if (TRACE) TheTrace.ClosednessKnightAdjustment[closedness][WHITE] += count;

    // Evaluate Rooks based on how Closed the position is
    count = popcount(white & rooks) - popcount(black & rooks);
    eval += count * ClosednessRookAdjustment[closedness];
    if (TRACE) TheTrace.ClosednessRookAdjustment[closedness][WHITE] += count;

    return eval;
}

packed_t evaluateComplexity(EvalInfo*, const Board_& board, packed_t eval)
{
    // Adjust endgame evaluation based on features related to how
    // likely the stronger side is to convert the position.
    // More often than not, this is a penalty for drawish positions.

    score_t eg = ScoreEG(eval);
    int sign = (eg > 0) - (eg < 0);

    int pawnsOnBothFlanks = (board.Pawns() & LEFT_FLANK) && (board.Pawns() & RIGHT_FLANK);

    uint64 knights = board.Knights();
    uint64 bishops = board.Bishops();
    uint64 rooks = board.Rooks();
    uint64 queens = board.Queens();

    // Compute the initiative bonus or malus for the attacking side
    packed_t complexity = ComplexityTotalPawns * popcount(board.Pawns())
            + ComplexityPawnFlanks * pawnsOnBothFlanks
            + ComplexityPawnEndgame * !(knights | bishops | rooks | queens)
            + ComplexityAdjustment;

    if (TRACE) TheTrace.ComplexityTotalPawns[WHITE] += popcount(board.Pawns());
    if (TRACE) TheTrace.ComplexityPawnFlanks[WHITE] += pawnsOnBothFlanks;
    if (TRACE) TheTrace.ComplexityPawnEndgame[WHITE] += !(knights | bishops | rooks | queens);
    if (TRACE) TheTrace.ComplexityAdjustment[WHITE] += 1;

    // Avoid changing which side has the advantage
    int v = sign * Max<int>(ScoreEG(complexity), -abs(eg));

    if (TRACE) TheTrace.eval = eval;
    if (TRACE) TheTrace.complexity = complexity;
    return MakeScore(0, v);
}

packed_t evaluatePieces(EvalInfo* ei, const Board_& board)
{
    packed_t eval = evaluatePawns<WHITE>(ei, board) - evaluatePawns<BLACK>(ei, board);

    // This needs to be done after pawn evaluation but before king safety evaluation
    evaluateKingsPawns<WHITE>(ei, board);
    evaluateKingsPawns<BLACK>(ei, board);

    eval += PrevalKnights<WHITE>(ei, board) - PrevalKnights<BLACK>(ei, board);
    eval += PrevalBishops<WHITE>(ei, board) - PrevalBishops<BLACK>(ei, board);
    eval += PrevalRooks<WHITE>(ei, board) - PrevalRooks<BLACK>(ei, board);
    eval += PrevalQueens<WHITE>(ei, board) - PrevalQueens<BLACK>(ei, board);

    eval += evaluateKnights<WHITE>(ei, board) - evaluateKnights<BLACK>(ei, board);
    eval += evaluateBishops<WHITE>(ei, board) - evaluateBishops<BLACK>(ei, board);
    eval += evaluateRooks<WHITE>(ei, board) - evaluateRooks<BLACK>(ei, board);
    eval += evaluateQueens<WHITE>(ei, board) - evaluateQueens<BLACK>(ei, board);
    eval += evaluateKings<WHITE>(ei, board) - evaluateKings<BLACK>(ei, board);
    eval += evaluatePassed<WHITE>(ei, board) - evaluatePassed<BLACK>(ei, board);
    eval += evaluateThreats<WHITE>(ei, board) - evaluateThreats<BLACK>(ei, board);
    eval += evaluateSpace<WHITE>(ei, board) - evaluateSpace<BLACK>(ei, board);

    return eval;
}


int evaluateScaleFactor(State* state, packed_t eval)
{
    // Scale endgames based upon the remaining material. We check
    // for various Opposite Coloured Bishop cases, positions with
    // a lone Queen against multiple minor pieces and/or rooks, and
    // positions with a Lone minor that should not be winnable
    int strongSide = ScoreEG(eval) < 0 ? BLACK : WHITE;
    if (state->matIndex & FlagUnusualMaterial)
    {
        // Scale down as the number of pawns of the strong side reduces
        const uint64 myPawns = state->board_.Pawns(strongSide);
        return Min<int>(SCALE_NORMAL, 96 + popcount(myPawns) * 8);
    }

    return MaterialInfo[state->matIndex].scale[strongSide];
}



constexpr int Tempo = 20;

score_t evaluateBoard(Thread* thread, State* state) 
{
    int factor = SCALE_NORMAL;

    // We can recognize positions we just evaluated
    if (thread->states[thread->height - 1].move == NULL_MOVE)
        return -thread->states[thread->height - 1].eval + 2 * Tempo;

    // Use the NNUE unless we are in an extremely unbalanced position
    packed_t packed;  // not, in itself, an eval
    if (USE_NNUE && abs(ScoreEG(state->psqtmat)) <= 2000) {
        packed = nnue_evaluate(thread, state);
        packed = state->turn == WHITE ? packed : -packed;
    }
    else 
    {
        EvalInfo ei;
        initEvalInfo(thread, state, &ei);
        packed = evaluatePieces(&ei, state->board_);

        packed_t pkeval = ei.pkeval[WHITE] - ei.pkeval[BLACK];
        if (ei.pkentry == NULL) pkeval += computePKNetwork(state->board_);

        packed += pkeval + state->psqtmat;
        packed += evaluateClosedness(&ei, state->board_);
        packed += evaluateComplexity(&ei, state->board_, packed);

        // Store a new Pawn King Entry if we did not have one
        if (!TRACE && ei.pkentry == NULL)
            storeCachedPawnKingEval(thread, state, ei.passedPawns, pkeval, ei.pksafety);

        // Scale evaluation based on remaining material
        factor = evaluateScaleFactor(state, packed);
        if (TRACE) TheTrace.factor = factor;
    }

    // Calculate the game phase based on remaining material (Fruit Method)
    auto mat = state->matIndex & FlagUnusualMaterial ? nullptr : &MaterialInfo[state->matIndex];
    int phase = mat 
            ? mat->phase 
            : 4 * popcount(state->board_.Queens()) + 2 * popcount(state->board_.Rooks()) + 1 * popcount(state->board_.Knights() | state->board_.Bishops());

    // Compute and store an interpolated evaluation from white's POV
    score_t eval;
    if (phase >= OP_PHASE)
        eval = ScoreOP(packed);
    else if (phase >= MG_PHASE)
        eval = (ScoreOP(packed) * (phase - MG_PHASE) + ScoreMG(packed) * (OP_PHASE - phase)) / (OP_PHASE - MG_PHASE);
    else if (phase > EG_PHASE)
        eval = (ScoreMG(packed) * (phase - EG_PHASE) + (ScoreEG(packed) * (MG_PHASE - phase) * factor) / SCALE_NORMAL) / (MG_PHASE - EG_PHASE);
    else
        eval = (ScoreEG(packed) * factor) / SCALE_NORMAL;
    if (mat)
        eval += mat->matQuad;

    // Factor in the Tempo after interpolation and scaling, so that
    // if a null move is made, then we know eval = last_eval + 2 * Tempo
    return Tempo + (state->turn == WHITE ? eval : -eval);
}


/// Mate and Tablebase scores need to be adjusted relative to the Root
/// when going into the Table and when coming out of the Table. Otherwise,
/// we will not know when we have a "faster" vs "slower" Mate or TB Win/Loss

int tt_value_from(int value, int height) 
{
    return value == VALUE_NONE ? VALUE_NONE
        : value >= TBWIN_IN_MAX ? value - height
        : value <= -TBWIN_IN_MAX ? value + height : value;
}

int tt_value_to(int value, int height) 
{
    return value == VALUE_NONE ? VALUE_NONE
        : value >= TBWIN_IN_MAX ? value + height
        : value <= -TBWIN_IN_MAX ? value - height : value;
}


bool tt_probe(uint64 hash, int height, uint16_t* move, int* value, int* eval, int* depth, int* bound)
{
    /// Search for a Transposition matching the provided Zobrist Hash. If one is found,
    /// we update its age in order to indicate that it is still relevant, before copying
    /// over its contents and signaling to the caller that an Entry was found.

    const uint16_t hash16 = hash >> 48;
    TTEntry* slots = Table.buckets[hash & Table.hashMask].slots;

    for (int i = 0; i < TT_BUCKET_NB; i++) {

        if (slots[i].hash16 == hash16) {

            slots[i].generation = Table.generation | (slots[i].generation & TT_MASK_BOUND);

            *move = slots[i].move;
            *value = tt_value_from(slots[i].value, height);
            *eval = slots[i].eval;
            *depth = slots[i].depth;
            *bound = slots[i].generation & TT_MASK_BOUND;
            return TRUE;
        }
    }

    return FALSE;
}

/// transposition.c


struct TTClear { size_t index, count; };

void tt_clear_threaded(TTClear* ttclear)
{
    const uint64 MB = 1ull << 20;

    // Logic for dividing the Table taken from Weiss and CFish
    const uint64 size = (Table.hashMask + 1) * sizeof(TTBucket);
    const uint64 slice = (size + ttclear->count - 1) / ttclear->count;
    const uint64 blocks = (slice + 2 * MB - 1) / (2 * MB);
    const uint64 begin = Min(size, ttclear->index * blocks * 2 * MB);
    const uint64 end = Min(size, begin + blocks * 2 * MB);

    memset(&Table.buckets[0] + begin / sizeof(TTBucket), 0, end - begin);
}

void tt_clear(size_t nthreads)
{
    // Only use 1/4th of the enabled search Threads
    size_t nworkers = Max<size_t>(1, nthreads / 4);
    vector<unique_ptr<thread>> pthreads(nworkers);
    vector<TTClear> ttclears(nworkers);

    // Initalize the data passed via a void* in pthread_create()
    for (size_t i = 0; i < nworkers; i++)
        ttclears[i] = { i, nworkers };

    // Launch each of the helper threads to clear their sections
    for (int i = 1; i < nworkers; i++)
        pthreads[i].reset(new thread(tt_clear_threaded, &ttclears[i]));

    // Reuse this thread for the 0th sections of the Transposition Table
    tt_clear_threaded(&ttclears[0]);

    // Join each of the helper threads after they've cleared their sections
    for (int i = 1; i < nworkers; i++)
        pthreads[i]->join();
}

int tt_init(size_t nthreads, int megabytes)
{
    const uint64 MB = 1ull << 20;
    uint64 keySize = 16ull;

    // Cleanup memory when resizing the table
    if (Table.hashMask)
        vector<TTBucket>().swap(Table.buckets);

    // Default keysize of 16 bits maps to a 2MB TTable
    assert((1ull << 16ull) * sizeof(TTBucket) == 2 * MB);

    // Find the largest keysize that is still within our given megabytes
    while ((1ull << keySize) * sizeof(TTBucket) <= megabytes * MB / 2) keySize++;
    assert((1ull << keySize) * sizeof(TTBucket) <= megabytes * MB);

#if defined(__linux__) && !defined(__ANDROID__)

    // On Linux systems we align on 2MB boundaries and request Huge Pages
    Table.buckets = aligned_alloc(2 * MB, (1ull << keySize) * sizeof(TTBucket));
    madvise(Table.buckets, (1ull << keySize) * sizeof(TTBucket), MADV_HUGEPAGE);
#else

    // Otherwise, we simply allocate as usual and make no requests
    Table.buckets.resize(1ull << keySize);
#endif

    // Save the lookup mask
    Table.hashMask = (1ull << keySize) - 1u;

    // Clear the table and load everything into the cache
    tt_clear(nthreads);

    // Return the number of MB actually allocated for the TTable
    return static_cast<int>(((Table.hashMask + 1) * sizeof(TTBucket)) / MB);
}

int tt_hashfull()
{
    /// Estimate the permill of the table being used, by looking at a thousand
    /// Buckets and seeing how many Entries contain a recent Transposition.

    int used = 0;

    for (int i = 0; i < 1000; i++)
        for (int j = 0; j < TT_BUCKET_NB; j++)
            used += (Table.buckets[i].slots[j].generation & TT_MASK_BOUND) != BOUND_NONE
            && (Table.buckets[i].slots[j].generation & TT_MASK_AGE) == Table.generation;

    return used / TT_BUCKET_NB;
}

void tt_store(uint64 hash, int height, uint16_t move, int value, int eval, int depth, int bound) 
{
    int i;
    const uint16_t hash16 = hash >> 48;
    TTEntry* slots = Table.buckets[hash & Table.hashMask].slots;
    TTEntry* replace = slots; // &slots[0]

    // Find a matching hash, or replace using Min(x1, x2, x3),
    // where xN equals the depth minus 4 times the age difference
    for (i = 0; i < TT_BUCKET_NB && slots[i].hash16 != hash16; i++)
        if (replace->depth - ((259 + Table.generation - replace->generation) & TT_MASK_AGE)
                >= slots[i].depth - ((259 + Table.generation - slots[i].generation) & TT_MASK_AGE))
            replace = &slots[i];

    // Prefer a matching hash, otherwise score a replacement
    replace = (i != TT_BUCKET_NB) ? &slots[i] : replace;

    // Don't overwrite an entry from the same position, unless we have
    // an exact bound or depth that is nearly as good as the old one
    if (bound != BOUND_EXACT
            && hash16 == replace->hash16
            && depth < replace->depth - 2)
        return;

    // Don't overwrite a move if we don't have a new one
    if (move || hash16 != replace->hash16)
        replace->move = (uint16_t)move;

    // Finally, copy the new data into the replaced slot
    replace->depth = (int8_t)depth;
    replace->generation = (uint8_t)bound | Table.generation;
    replace->value = (score_t)tt_value_to(value, height);
    replace->eval = (score_t)eval;
    replace->hash16 = (uint16_t)hash16;
}




/// search.c

int LMRTable[64][64];
int LateMovePruningCounts[2][9];

volatile int ABORT_SIGNAL; // Global ABORT flag for threads
volatile int IS_PONDERING; // Global PONDER flag for threads
volatile int ANALYSISMODE; // Whether to make some changes for Analysis

uint64 nodesSearchedThreadPool(Thread* threads)
{
    // Sum up the node counters across each Thread. Threads have
    // their own node counters to avoid true sharing the cache

    uint64 nodes = 0ull;

    for (int i = 0; i < threads->nthreads; i++)
        nodes += threads->threads[i].nodes;

    return nodes;
}

uint64 tbhitsThreadPool(Thread* threads) 
{
    // Sum up the tbhit counters across each Thread. Threads have
    // their own tbhit counters to avoid true sharing the cache

    uint64 tbhits = 0ull;

    for (int i = 0; i < threads->nthreads; i++)
        tbhits += threads->threads[i].tbhits;

    return tbhits;
}

void uciReport(Thread* threads, PVariation* pv, int alpha, int beta)
{
    // Gather all of the statistics that the UCI protocol would be
    // interested in. Also, bound the value passed by alpha and
    // beta, since Ethereal uses a mix of fail-hard and fail-soft

    int hashfull = tt_hashfull();
    int depth = threads->depth;
    int seldepth = threads->seldepth;
    int multiPV = threads->multiPV + 1;
    double elapsed = elapsed_time(threads->tm);
    int bounded = Max(alpha, Min(pv->score, beta));
    uint64 nodes = nodesSearchedThreadPool(threads);
    uint64 tbhits = tbhitsThreadPool(threads);
    //int nps = (int)(1000 * (nodes / (1 + elapsed)));

    // If the score is MATE or MATED in X, convert to X
    int score = bounded >= MATE_IN_MAX 
            ? (MATE - bounded + 1) / 2
            : bounded <= -MATE_IN_MAX ? -(bounded + MATE) / 2 : bounded;

    // Two possible score types, mate and cp = centipawns
    const char* type = abs(bounded) >= MATE_IN_MAX ? "mate" : "cp";

    // Partial results from a windowed search have bounds
    const char* bound = bounded >= beta 
            ? " lowerbound "
            : bounded <= alpha ? " upperbound " : " ";

    printf("info depth %d seldepth %d multipv %d score %s %d%stime %d "
        "knodes %d tbhits %d hashfull %d pv ",
        depth, seldepth, multiPV, type, score, bound, static_cast<int>(elapsed), static_cast<int>(nodes >> 10), static_cast<int>(tbhits), hashfull);

    // Iterate over the PV and print each move
    for (int i = 0; i < pv->length; i++) {
        char moveStr[6];
        moveToString(pv->line[i], moveStr, threads->state.chess960);
        printf("%s ", moveStr);
    }

    // Send out a newline and flush
    puts(""); fflush(stdout);
}

void uciReportCurrentMove(State* state, uint16_t move, int currmove, int depth)
{
    char moveStr[6];
    moveToString(move, moveStr, state->chess960);
    printf("info depth %d currmove %s currmovenumber %d\n", depth, moveStr, currmove);
    fflush(stdout);
}

struct UCIMove_
{
    uint16_t best, ponder;
    int score;
};

UCIMove_ select_from_threads(Thread* threads) 
{
    /// A thread is better than another if any are true:
    /// [1] The thread has an equal depth and greater score.
    /// [2] The thread has a mate score and is closer to mate.
    /// [3] The thread has a greater depth without replacing a closer mate

    Thread* best_thread = &threads[0];

    for (int i = 1; i < threads->nthreads; i++) 
    {
        const int best_depth = best_thread->completed;
        const int best_score = best_thread->pvs[best_depth].score;

        const int this_depth = threads[i].completed;
        const int this_score = threads[i].pvs[this_depth].score;

        if ((this_depth == best_depth && this_score > best_score)
            || (this_score > MATE_IN_MAX && this_score > best_score))
            best_thread = &threads[i];

        if (this_depth > best_depth
            && (this_score > best_score || best_score < MATE_IN_MAX))
            best_thread = &threads[i];
    }

    // Best and Ponder moves are simply the PV moves
    UCIMove_ retval = {
        best_thread->pvs[best_thread->completed].line[0],
        best_thread->pvs[best_thread->completed].line[1],
        best_thread->pvs[best_thread->completed].score
    };

    // Incomplete searches or low depth ones may result in a short PV
    if (best_thread->pvs[best_thread->completed].length < 2)
        retval.ponder = NONE_MOVE;

    // Report via UCI when our best thread is not the main thread
    if (best_thread != &threads[0]) {
        const int best_depth = best_thread->completed;
        best_thread->multiPV = 0;
        uciReport(best_thread, &best_thread->pvs[best_depth], -MATE, MATE);
    }

    return retval;
}

void update_best_line(Thread* thread, PVariation* pv) 
{
    /// Upon finishing a depth, or reaching a fail-high, we update
    /// this Thread's line of best play for the newly completed depth.
    /// We store seperately the lines that we explore in multipv searches

    if (!thread->multiPV || pv->score > thread->pvs[thread->completed].score) 
    {
        thread->completed = thread->depth;
        memcpy(&thread->pvs[thread->depth], pv, sizeof(PVariation));
    }

    memcpy(&thread->mpvs[thread->multiPV], pv, sizeof(PVariation));
}

void revert_best_line(Thread* thread) 
{
    /// A fail-low during occured during the search, and therefore we need
    /// to remove any fail-highs that we may have originally marked as best
    /// lines, since we now believe the line to much worse than before

    if (!thread->multiPV)
        thread->completed = thread->depth - 1;
}

void report_multipv_lines(Thread* thread) 
{
    /// We've just finished a depth during a MultiPV search. Now we will
    /// once again report the lines, but this time ordering them based on
    /// their scores. It is possible, although generally unusual, for a
    /// move searched later to have a better score than an earlier move.

    for (int i = 0; i < thread->limits->multiPV; i++) {

        for (int j = i + 1; j < thread->limits->multiPV; j++) {

            if (thread->mpvs[j].score > thread->mpvs[i].score) {
                PVariation localpv;
                memcpy(&localpv, &thread->mpvs[i], sizeof(PVariation));
                memcpy(&thread->mpvs[i], &thread->mpvs[j], sizeof(PVariation));
                memcpy(&thread->mpvs[j], &localpv, sizeof(PVariation));
            }
        }
    }

    for (thread->multiPV = 0; thread->multiPV < thread->limits->multiPV; thread->multiPV++)
        uciReport(thread->threads, &thread->mpvs[thread->multiPV], -MATE, MATE);
}


void initSearch() {

    // Init Late Move Reductions Table
    for (int depth = 1; depth < 64; depth++)
        for (int played = 1; played < 64; played++)
            LMRTable[depth][played] = static_cast<int>(0.75 + log(double(depth)) * log(double(played)) / 2.25);

    for (int depth = 1; depth < 9; depth++) {
        LateMovePruningCounts[0][depth] = static_cast<int>(2.5 + 2 * depth * depth / 4.5);
        LateMovePruningCounts[1][depth] = static_cast<int>(4.0 + 4 * depth * depth / 4.5);
    }
}

struct Abort_ : std::exception 
{ 
};

int qsearch(Thread* thread, PVariation* pv, int alpha, int beta)
{
    State* const state = &thread->state;
    NodeState* const ns = &thread->states[thread->height];

    int eval, value, best, oldAlpha = alpha;
    int ttHit, ttValue = 0, ttEval = VALUE_NONE, ttDepth = 0, ttBound = 0;
    uint16_t move, ttMove = NONE_MOVE, bestMove = NONE_MOVE;
    PVariation lpv;

    // Ensure a fresh PV
    pv->length = 0;

    // Updates for UCI reporting
    thread->seldepth = Max(thread->seldepth, thread->height);
    thread->nodes++;

    // Step 1. Abort Check. Exit the search if signaled by main thread or the
    // UCI thread, or if the search time has expired outside pondering mode
    if ((ABORT_SIGNAL && thread->depth > 1) || (tm_stop_early(thread) && !IS_PONDERING))
        throw Abort_();

    // Step 2. Draw Detection. Check for the fifty move rule, repetition, or insufficient
    // material. Add variance to the draw score, to avoid blindness to 3-fold lines
    if (boardIsDrawn(state, thread->height)) 
        return 1 - (thread->nodes & 2);

    // Step 3. Max Draft Cutoff. If we are at the maximum search draft,
    // then end the search here with a static eval of the current state
    if (thread->height >= MAX_PLY)
        return evaluateBoard(thread, state);

    // Step 4. Probe the Transposition Table, adjust the value, and consider cutoffs
    if ((ttHit = tt_probe(state->hash, thread->height, &ttMove, &ttValue, &ttEval, &ttDepth, &ttBound))) {

        // Table is exact or produces a cutoff
        if (ttBound == BOUND_EXACT
            || (ttBound == BOUND_LOWER && ttValue >= beta)
            || (ttBound == BOUND_UPPER && ttValue <= alpha))
            return ttValue;
    }

    // Save a history of the static evaluations
    eval = ns->eval = ttEval != VALUE_NONE
        ? ttEval : evaluateBoard(thread, state);

    // Toss the static evaluation into the TT if we won't overwrite something
    if (!ttHit && !state->kingAttackers)
        tt_store(state->hash, thread->height, NONE_MOVE, VALUE_NONE, eval, 0, BOUND_NONE);

    // Step 5. Eval Pruning. If a static evaluation of the state will
    // exceed beta, then we can stop the search here. Also, if the static
    // eval exceeds alpha, we can call our static eval the new alpha
    best = eval;
    alpha = Max(alpha, eval);
    if (alpha >= beta) return eval;

    // Step 6. Delta Pruning. Even the best possible capture and or promotion
    // combo, with a minor boost for pawn captures, would still fail to cover
    // the distance between alpha and the evaluation. Playing a move is futile.
    if (Max(QSDeltaMargin, moveBestCaseValue(*state)) < alpha - eval)
        return eval;

    // Step 7. Move Generation and Looping. Generate all tactical moves
    // and return those which are winning via SEE, and also strong enough
    // to beat the margin computed in the Delta Pruning step found above
    init_noisy_picker(&ns->mp, thread, NONE_MOVE, Max(1, alpha - eval - QSSeeMargin));
    while ((move = select_next(&ns->mp, thread, 1)) != NONE_MOVE) {

        // Worst case which assumes we lose our piece immediately
        int pessimism = moveEstimatedValue(state->board_, move)
            - SEEPieceValues[TypeOf(state->board_.at_[MoveFrom(move)])];

        // Search the next ply if the move is legal
        if (!apply(thread, state, move)) continue;

        // Short-circuit QS and assume a stand-pat matches the SEE
        if (eval + pessimism > beta && abs(eval + pessimism) < MATE / 2) {
            revert(thread, state, move);
            pv->length = 1;
            pv->line[0] = move;
            return beta;
        }

        value = -qsearch(thread, &lpv, -beta, -alpha);
        revert(thread, state, move);

        // Improved current value
        if (value > best) {

            best = value;
            bestMove = move;

            // Improved current lower bound
            if (value > alpha) {
                alpha = value;

                // Update the Principle Variation
                pv->length = 1 + lpv.length;
                pv->line[0] = move;
                memcpy(pv->line + 1, lpv.line, sizeof(uint16_t) * lpv.length);
            }

            // Search has failed high
            if (alpha >= beta)
                break;
        }
    }

    // Step 8. Store results of search into the Transposition Table.
    ttBound = best >= beta 
            ? BOUND_LOWER
            : best > oldAlpha ? BOUND_EXACT : BOUND_UPPER;
    tt_store(state->hash, thread->height, bestMove, best, eval, 0, ttBound);

    return best;
}

void update_killer_moves(Thread* thread, uint16_t move)
{
    // Avoid saving the same Killer Move twice
    for (auto& k : thread->killers[thread->height])
    {
        if (k == move)
            break;
        std::swap(k, move);
    }
}

void update_history_heuristics(Thread* thread, uint16_t* moves, int length, int depth)
{
    NodeState* const prev = &thread->states[thread->height - 1];
    const int colour = thread->state.turn;

    update_killer_moves(thread, moves[length - 1]);

    if (prev->move != NONE_MOVE && prev->move != NULL_MOVE)
        thread->cmtable[!colour][prev->movedPiece][MoveTo(prev->move)] = moves[length - 1];

    update_quiet_histories(thread, moves, length, depth);
}

void update_capture_histories(Thread* thread, uint16_t best, uint16_t* moves, int length, int depth)
{
    // Update the history for each capture move that was attempted. One of them
    // might have been the move which produced a cutoff, and thus earn a bonus

    for (int i = 0; i < length; i++) {
        score_t* hist = underlying_capture_history(thread, moves[i]);
        update_history(hist, depth, moves[i] == best);
    }
}


// search and singularity are coroutines
int search(Thread* thread, PVariation* pv, int alpha, int beta, int depth, bool cutnode);

int singularity(Thread* thread, uint16_t ttMove, int ttValue, int depth, int PvNode, int alpha, int beta, bool cutnode)
{
    State* const state = &thread->state;
    NodeState* const ns = &thread->states[thread->height - 1];

    PVariation lpv; lpv.length = 0;
    int value, rBeta = Max(ttValue - depth, -MATE);

    // Table move was already applied
    revert(thread, state, ttMove);

    // Search on a null rBeta window, excluding the tt-move
    ns->excluded = ttMove;
    value = search(thread, &lpv, rBeta - 1, rBeta, (depth - 1) / 2, cutnode);
    ns->excluded = NONE_MOVE;

    // We reused the Move Picker, so make sure we cleanup
    ns->mp.stage = STAGE_TABLE + 1;

    // MultiCut. We signal the Move Picker to terminate the search
    if (value >= rBeta && rBeta >= beta)
        ns->mp.stage = STAGE_DONE;

    // Reapply the table move we took off
    else applyLegal(thread, state, ttMove);

    bool double_extend = !PvNode
            && value < rBeta - 15
            && (ns - 1)->dextensions <= 6;

    return double_extend ? 2 // Double extension in some non-pv nodes
            : value < rBeta ? 1 // Singular due to no cutoffs produced
            : ttValue >= beta ? -1 // Potential multi-cut even at current depth
            : ttValue <= alpha ? -1 // Negative extension if ttValue was already failing-low
            : 0;                    // Not singular, and unlikely to produce a cutoff
}


int search(Thread* thread, PVariation* pv, int alpha, int beta, int depth, bool cutnode)
{
    State* const state = &thread->state;
    NodeState* const ns = &thread->states[thread->height];

    const int PvNode = (alpha != beta - 1);
    const int RootNode = (thread->height == 0);

    unsigned tbresult;
    int hist = 0, cmhist = 0, fmhist = 0;
    int movesSeen = 0, quietsPlayed = 0, capturesPlayed = 0, played = 0;
    int ttHit = 0, ttValue = 0, ttEval = VALUE_NONE, ttDepth = 0, tbBound, ttBound = 0;
    int R, newDepth, rAlpha, rBeta, oldAlpha = alpha;
    int inCheck, isQuiet, improving, extension, singular, skipQuiets = 0;
    int eval, value, best = -MATE, syzygyMax = MATE, syzygyMin = -MATE, seeMargin[2];
    uint16_t move, ttMove = NONE_MOVE, bestMove = NONE_MOVE;
    uint16_t quietsTried[MAX_MOVES], capturesTried[MAX_MOVES];
    bool doFullSearch;
    PVariation lpv;

    // Step 1. Quiescence Search. Perform a search using mostly tactical
    // moves to reach a more stable position for use as a static evaluation
    if (depth <= 0 && !state->kingAttackers)
        return qsearch(thread, pv, alpha, beta);

    // Ensure a fresh PV
    pv->length = 0;

    // Ensure positive depth
    depth = Max(0, depth);

    // Updates for UCI reporting
    thread->seldepth = RootNode ? 0 : Max(thread->seldepth, thread->height);
    thread->nodes++;

    // Step 2. Abort Check. Exit the search if signaled by main thread or the
    // UCI thread, or if the search time has expired outside pondering mode
    if ((ABORT_SIGNAL && thread->depth > 1) || (tm_stop_early(thread) && !IS_PONDERING))
        throw Abort_();

    // Step 3. Check for early exit conditions. Don't take early exits in
    // the RootNode, since this would prevent us from having a best move
    if (!RootNode) 
    {
        // Draw Detection. Check for the fifty move rule, repetition, or insufficient
        // material. Add variance to the draw score, to avoid blindness to 3-fold lines
        if (boardIsDrawn(state, thread->height)) 
            return 1 - (thread->nodes & 2);

        // Check to see if we have exceeded the maxiumum search draft
        if (thread->height >= MAX_PLY)
            return state->kingAttackers ? 0 : evaluateBoard(thread, state);

        // Mate Distance Pruning. Check to see if this line is so
        // good, or so bad, that being mated in the ply, or  mating in
        // the next one, would still not create a more extreme line
        rAlpha = Max(alpha, -MATE + thread->height);
        rBeta = Min(beta, MATE - thread->height - 1);
        if (rAlpha >= rBeta) return rAlpha;
    }

    // Don't probe the TT or TB during singluar searches
    if (ns->excluded == NONE_MOVE)
    {
        // Step 4. Probe the Transposition Table, adjust the value, and consider cutoffs
        if (ttHit = tt_probe(state->hash, thread->height, &ttMove, &ttValue, &ttEval, &ttDepth, &ttBound))
        {
            // Only cut with a greater depth search, and do not return
            // when in a PvNode, unless we would otherwise hit a qsearch
            if (ttDepth >= depth
                    && (depth == 0 || !PvNode)
                    && (cutnode || ttValue <= alpha)) 
            {
                // Table is exact or produces a cutoff
                if (ttBound == BOUND_EXACT
                        || (ttBound == BOUND_LOWER && ttValue >= beta)
                        || (ttBound == BOUND_UPPER && ttValue <= alpha))
                    return ttValue;
            }

            // An entry coming from one depth lower than we would accept for a cutoff will
            // still be accepted if it appears that failing low will trigger a research.
            if (!PvNode
                && ttDepth >= depth - 1
                && (ttBound & BOUND_UPPER)
                && (cutnode || ttValue <= alpha)
                && ttValue + TTResearchMargin <= alpha)
                return alpha;
        }

        // Step 5. Probe the Syzygy Tablebases. tablebasesProbeWDL() handles all of
        // the conditions about the state, the existance of tables, the probe depth,
        // as well as to not probe at the Root. The return is defined by the Pyrrhic API
        if ((tbresult = tablebasesProbeWDL(state, depth, thread->height)) != TB_RESULT_FAILED) 
        {
            thread->tbhits++; // Increment tbhits counter for this thread

            // Convert the WDL value to a score. We consider blessed losses
            // and cursed wins to be a draw, and thus set value to zero.
            value = tbresult == TB_LOSS ? -TBWIN + thread->height
                : tbresult == TB_WIN ? TBWIN - thread->height : 0;

            // Identify the bound based on WDL scores. For wins and losses the
            // bound is not exact because we are dependent on the height, but
            // for draws (and blessed / cursed) we know the tbresult to be exact
            tbBound = tbresult == TB_LOSS ? BOUND_UPPER
                : tbresult == TB_WIN ? BOUND_LOWER : BOUND_EXACT;

            // Check to see if the WDL value would cause a cutoff
            if (tbBound == BOUND_EXACT
                || (tbBound == BOUND_LOWER && value >= beta)
                || (tbBound == BOUND_UPPER && value <= alpha)) {

                tt_store(state->hash, thread->height, NONE_MOVE, value, VALUE_NONE, depth, tbBound);
                return value;
            }

            // Never score something worse than the known Syzygy value
            if (PvNode && tbBound == BOUND_LOWER)
                syzygyMin = value, alpha = Max(alpha, value);

            // Never score something better than the known Syzygy value
            if (PvNode && tbBound == BOUND_UPPER)
                syzygyMax = value;
        }
    }
    // Step 6. Initialize flags and values used by pruning and search methods

    // We can grab in check based on the already computed king attackers bitboard
    inCheck = !!state->kingAttackers;

    // Save a history of the static evaluations when not checked
    eval = ns->eval = inCheck 
            ? VALUE_NONE
            : ttEval != VALUE_NONE 
                    ? ttEval 
                    : evaluateBoard(thread, state);

    // Static Exchange Evaluation Pruning Margins
    seeMargin[0] = SEENoisyMargin * depth * depth;
    seeMargin[1] = SEEQuietMargin * depth;

    // Improving if our static eval increased in the last move
    improving = !inCheck && eval > (ns - 2)->eval;

    // Reset Killer moves for our children
    std::fill(thread->killers[thread->height + 1].begin(), thread->killers[thread->height + 1].end(), NONE_MOVE);

    // Track the # of double extensions in this line
    ns->dextensions = RootNode ? 0 : (ns - 1)->dextensions;

    // Beta value for ProbCut Pruning
    rBeta = Min(beta + ProbCutMargin, MATE - MAX_PLY - 1);

    // Toss the static evaluation into the TT if we won't overwrite something
    if (!ttHit && !inCheck && !ns->excluded)
        tt_store(state->hash, thread->height, NONE_MOVE, VALUE_NONE, eval, 0, BOUND_NONE);

    // ------------------------------------------------------------------------
    // All elo estimates as of Ethereal 11.80, @ 12s+0.12 @ 1.275mnps
    // ------------------------------------------------------------------------

    // Step 7 (~32 elo). Beta Pruning / Reverse Futility Pruning / Static
    // Null Move Pruning. If the eval is well above beta, defined by a depth
    // dependent margin, then we assume the eval will hold above beta
    if (!PvNode
        && !inCheck
        && !ns->excluded
        && depth <= BetaPruningDepth
        && eval - BetaMargin * depth > beta)
        return eval;

    // Step 8 (~3 elo). Alpha Pruning for main search loop. The idea is
    // that for low depths if eval is so bad that even a large static
    // bonus doesn't get us beyond alpha, then eval will hold below alpha
    if (!PvNode
        && !inCheck
        && !ns->excluded
        && depth <= AlphaPruningDepth
        && eval + AlphaMargin <= alpha)
        return eval;

    // Step 9 (~93 elo). Null Move Pruning. If our position is so strong
    // that giving our opponent a double move still allows us to maintain
    // beta, then we can prune early with some safety. Do not try NMP when
    // it appears that a TT entry suggests it will fail immediately
    if (!PvNode
        && !inCheck
        && !ns->excluded
        && eval >= beta
        && (ns - 1)->move != NULL_MOVE
        && depth >= NullMovePruningDepth
        && playerHasNonPawnMaterial(state->board_, state->turn)
        && (!ttHit || !(ttBound & BOUND_UPPER) || ttValue >= beta)) {

        // Dynamic R based on Depth, Eval, and Tactical state
        R = 4 + depth / 6 + Min(3, (eval - beta) / 200) + (ns - 1)->tactical;

        apply(thread, state, NULL_MOVE);
        value = -search(thread, &lpv, -beta, -beta + 1, depth - R, !cutnode);
        revert(thread, state, NULL_MOVE);

        // Don't return unproven TB-Wins or Mates
        if (value >= beta)
            return (value > TBWIN_IN_MAX) ? beta : value;
    }

    // Step 10 (~9 elo). Probcut Pruning. If we have a good capture that causes a
    // cutoff with an adjusted beta value at a reduced search depth, we expect that
    // it will cause a similar cutoff at this search depth, with a normal beta value
    if (!PvNode
        && !inCheck
        && !ns->excluded
        && depth >= ProbCutDepth
        && abs(beta) < TBWIN_IN_MAX
        && (!ttHit || ttValue >= rBeta || ttDepth < depth - 3)) {

        // Try tactical moves which maintain rBeta.
        init_noisy_picker(&ns->mp, thread, ttMove, rBeta - eval);
        while ((move = select_next(&ns->mp, thread, 1)) != NONE_MOVE) {

            // Apply move, skip if move is illegal
            if (apply(thread, state, move)) {

                // For high depths, verify the move first with a qsearch
                if (depth >= 2 * ProbCutDepth)
                    value = -qsearch(thread, &lpv, -rBeta, -rBeta + 1);

                // For low depths, or after the above, verify with a reduced search
                if (depth < 2 * ProbCutDepth || value >= rBeta)
                    value = -search(thread, &lpv, -rBeta, -rBeta + 1, depth - 4, !cutnode);

                // Revert the state state
                revert(thread, state, move);

                // Store an entry if we don't have a better one already
                if (value >= rBeta && (!ttHit || ttDepth < depth - 3))
                    tt_store(state->hash, thread->height, move, value, eval, depth - 3, BOUND_LOWER);

                // Probcut failed high verifying the cutoff
                if (value >= rBeta) return value;
            }
        }
    }

    // Step 11. Internal Iterative Reductions. Artifically lower the depth on cutnodes
    // that are high enough up in the search tree that we would expect to have found
    // a Transposition. This is a modernized approach to Internal Iterative Deepening
    if (cutnode && depth >= 7 && ttMove == NONE_MOVE)
        depth -= 1;

    // Step 12. Initialize the Move Picker and being searching through each
    // move one at a time, until we run out or a move generates a cutoff. We
    // reuse an already initialized MovePicker to verify Singular Extension
    if (!ns->excluded) init_picker(&ns->mp, thread, ttMove);
    while ((move = select_next(&ns->mp, thread, skipQuiets)) != NONE_MOVE) 
    {
        const uint64 starting_nodes = thread->nodes;

        // MultiPV and UCI searchmoves may limit our search options
        if (RootNode && moveExaminedByMultiPV(thread, move)) continue;
        if (RootNode && !moveIsInRootMoves(*thread->limits, move)) continue;

        // Track Moves Seen for Late Move Pruning
        movesSeen += 1;
        isQuiet = !moveIsTactical(state->board_, move);

        // All moves have one or more History scores
        hist = isQuiet
                ? get_quiet_history(thread, move, &cmhist, &fmhist)
                : get_capture_history(thread, move);

        // Step 13 (~80 elo). Late Move Pruning / Move Count Pruning. If we
        // have seen many moves in this position already, and we don't expect
        // anything from this move, we can skip all the remaining quiets
        if (best > -TBWIN_IN_MAX
                && depth <= LateMovePruningDepth
                && movesSeen >= LateMovePruningCounts[improving][depth])
            skipQuiets = 1;

        // Step 14 (~175 elo). Quiet Move Pruning. Prune any quiet move that meets one
        // of the criteria below, only after proving a non mated line exists
        if (isQuiet && best > -TBWIN_IN_MAX) 
        {
            // Base LMR reduced depth value that we expect to use later
            int lmrDepth = Max(0, depth - LMRTable[Min(depth, 63)][Min(played, 63)]);
            int fmpMargin = FutilityMarginBase + lmrDepth * FutilityMarginPerDepth;

            // Step 14A (~3 elo). Futility Pruning. If our score is far below alpha,
            // and we don't expect anything from this move, we can skip all other quiets
            if (!inCheck
                    && eval + fmpMargin <= alpha
                    && lmrDepth <= FutilityPruningDepth
                    && hist < FutilityPruningHistoryLimit[improving])
                skipQuiets = 1;

            // Step 14B (~2.5 elo). Futility Pruning. If our score is not only far
            // below alpha but still far below alpha after adding the Futility Margin,
            // we can somewhat safely skip all quiet moves after this one
            if (!inCheck
                    && lmrDepth <= FutilityPruningDepth
                    && eval + fmpMargin + FutilityMarginNoHistory <= alpha)
                skipQuiets = 1;

            // Step 14C (~10 elo). Continuation Pruning. Moves with poor counter
            // or follow-up move history are pruned near the leaf nodes of the search
            if (ns->mp.stage > STAGE_COUNTER_MOVE
                    && lmrDepth <= ContinuationPruningDepth[improving]
                    && Min(cmhist, fmhist) < ContinuationPruningHistoryLimit[improving])
                continue;
        }

        // Step 15 (~42 elo). Static Exchange Evaluation Pruning. Prune moves which fail
        // to beat a depth dependent SEE threshold. The use of the Move Picker's stage
        // is a speedup, which assumes that good noisy moves have a positive SEE
        if (best > -TBWIN_IN_MAX
                && depth <= SEEPruningDepth
                && ns->mp.stage > STAGE_GOOD_NOISY
                && !staticExchangeEvaluation(state, move, seeMargin[isQuiet]))
            continue;

        // Apply move, skip if move is illegal
        if (!apply(thread, state, move))
            continue;

        played += 1;
        if (isQuiet) quietsTried[quietsPlayed++] = move;
        else capturesTried[capturesPlayed++] = move;

        // The UCI spec allows us to output information about the current move
        // that we are going to search. We only do this from the main thread,
        // and we wait a few seconds in order to avoid floiding the output
        if (RootNode && !thread->index && elapsed_time(thread->tm) > CurrmoveTimerMS)
            uciReportCurrentMove(state, move, played + thread->multiPV, thread->depth);

        // Identify moves which are candidate singular moves
        singular = !RootNode
                && depth >= 8
                && move == ttMove
                && ttDepth >= depth - 3
                && (ttBound & BOUND_LOWER);

        // Step 16 (~60 elo). Extensions. Search an additional ply when the move comes from the
        // Transposition Table and appears to beat all other moves by a fair margin. Otherwise,
        // extend for any position where our King is checked.

        extension = singular ? singularity(thread, ttMove, ttValue, depth, PvNode, alpha, beta, cutnode) : inCheck;
        newDepth = depth + (!RootNode ? extension : 0);
        if (extension > 1) ns->dextensions++;

        // Step 17. MultiCut. Sometimes candidate Singular moves are shown to be non-Singular.
        // If this happens, and the rBeta used is greater than beta, then we have multiple moves
        // which appear to beat beta at a reduced depth. singularity() sets the stage to STAGE_DONE

        if (ns->mp.stage == STAGE_DONE)
            return Max(ttValue - depth, -MATE);

        if (depth > 2 && played > 1) 
        {
            // Step 18A (~249 elo). Quiet Late Move Reductions. Reduce the search depth
            // of Quiet moves after we've explored the main line. If a reduced search
            // manages to beat alpha, against our expectations, we perform a research

            if (isQuiet) 
            {
                // Use the LMR Formula as a starting point
                R = LMRTable[Min(depth, 63)][Min(played, 63)];

                // Increase for non PV, non improving
                R += !PvNode + !improving;

                // Increase for King moves that evade checks
                R += inCheck && TypeOf(state->board_.at_[MoveTo(move)]) == KING;

                // Reduce for Killers and Counters
                R -= ns->mp.stage < STAGE_QUIET;

                // Adjust based on history scores
                R -= Max(-2, Min(2, hist / 5000));
            }

            // Step 18B (~3 elo). Noisy Late Move Reductions. The same as Step 18A, but
            // only applied to Tactical moves, based mostly on the Capture History scores

            else 
            {
                // Initialize R based on Capture History
                R = 2 - (hist / 5000);

                // Reduce for moves that give check
                R -= !!state->kingAttackers;
            }

            // Don't extend or drop into QS
            R = Min(depth - 1, Max(R, 1));

            // Perform reduced depth search on a Null Window
            value = -search(thread, &lpv, -alpha - 1, -alpha, newDepth - R, true);

            // Abandon searching here if we could not beat alpha
            doFullSearch = value > alpha && R != 1;
        }

        else doFullSearch = !PvNode || played > 1;

        // Full depth search on a null window
        if (doFullSearch)
            value = -search(thread, &lpv, -alpha - 1, -alpha, newDepth - 1, !cutnode);

        // Full depth search on a full window for some PvNodes
        if (PvNode && (played == 1 || value > alpha))
            value = -search(thread, &lpv, -beta, -alpha, newDepth - 1, FALSE);

        // Revert the state state
        revert(thread, state, move);

        // Reset the extension tracker
        if (extension > 1) ns->dextensions--;

        // Track where nodes were spent in the Main thread at the Root
        if (RootNode && !thread->index)
            thread->tm->nodes[move] += thread->nodes - starting_nodes;

        // Step 19. Update search stats for the best move and its value. Update
        // our lower bound (alpha) if exceeded, and also update the PV in that case
        if (value > best) 
        {
            best = value;
            bestMove = move;

            if (value > alpha) 
            {
                alpha = value;

                // Copy our child's PV and prepend this move to it
                pv->length = 1 + lpv.length;
                pv->line[0] = move;
                memcpy(pv->line + 1, lpv.line, sizeof(uint16_t) * lpv.length);

                // Search failed high
                if (alpha >= beta) break;
            }
        }
    }

    // Step 20 (~760 elo). Update History counters on a fail high for a quiet move.
    // We also update Capture History Heuristics, which augment or replace MVV-LVA.

    if (best >= beta && !moveIsTactical(state->board_, bestMove))
        update_history_heuristics(thread, quietsTried, quietsPlayed, depth);

    if (best >= beta)
        update_capture_histories(thread, bestMove, capturesTried, capturesPlayed, depth);

    // Step 21. Stalemate and Checkmate detection. If no moves were found to
    // be legal then we are either mated or stalemated, For mates, return a
    // score based on how far or close the mate is to the root position
    if (played == 0) return inCheck ? -MATE + thread->height : 0;

    // Step 22. When we found a Syzygy entry, don't report a value greater than
    // the known bounds. For example, a non-zeroing move could be played, not be
    // held in Syzygy, and then be scored better than the true lost value.
    if (PvNode) best = Max(syzygyMin, Min(best, syzygyMax));

    // Step 23. Store results of search into the Transposition Table. We do not overwrite
    // the Root entry from the first line of play we examined. We also don't store into the
    // Transposition Table while attempting to veryify singularities
    if (!ns->excluded && (!RootNode || !thread->multiPV)) {
        ttBound = best >= beta ? BOUND_LOWER
            : best > oldAlpha ? BOUND_EXACT : BOUND_UPPER;
        bestMove = ttBound == BOUND_UPPER ? NONE_MOVE : bestMove;
        tt_store(state->hash, thread->height, bestMove, best, eval, depth, ttBound);
    }

    return best;
}

void aspirationWindow(Thread* thread)
{
    PVariation pv;
    int depth = thread->depth;
    int alpha = -MATE, beta = MATE, delta = WindowSize;
    int report = !thread->index && thread->limits->multiPV == 1;

    // After a few depths use a previous result to form the window
    if (thread->depth >= WindowDepth) {
        alpha = Max(-MATE, thread->pvs[thread->completed].score - delta);
        beta = Min(MATE, thread->pvs[thread->completed].score + delta);
    }

    while (1)
    {
        // Perform a search and consider reporting results
        pv.score = search(thread, &pv, alpha, beta, Max(1, depth), FALSE);
        if ((report && pv.score > alpha && pv.score < beta)
                || (report && elapsed_time(thread->tm) >= WindowTimerMS))
            uciReport(thread->threads, &pv, alpha, beta);

        // Search returned a result within our window
        if (pv.score > alpha && pv.score < beta) {
            thread->bestMoves[thread->multiPV] = pv.line[0];
            update_best_line(thread, &pv);
            return;
        }

        // Search failed low, adjust window and reset depth
        if (pv.score <= alpha) {
            beta = (alpha + beta) / 2;
            alpha = Max(-MATE, alpha - delta);
            depth = thread->depth;
            revert_best_line(thread);
        }

        // Search failed high, adjust window and reduce depth
        else if (pv.score >= beta) {
            beta = Min(MATE, beta + delta);
            depth = depth - (abs(pv.score) <= MATE / 2);
            update_best_line(thread, &pv);
        }

        // Expand the search window
        delta = delta + delta / 2;
    }
}

void iterativeDeepening(Thread* thread)
{
    TimeManager* const tm = thread->tm;
    Limits* const limits = thread->limits;
    const int mainThread = thread->index == 0;

    // Bind when we expect to deal with NUMA
    //if (thread->nthreads > 8)
    //    bindThisThread(thread->index);

    // Perform iterative deepening until exit conditions
    try
    {
        for (thread->depth = 1; thread->depth < MAX_PLY; thread->depth++)
        {
            // If we abort to here, we stop searching

            // Perform a search for the current depth for each requested line of play
            for (thread->multiPV = 0; thread->multiPV < limits->multiPV; thread->multiPV++)
                aspirationWindow(thread);

            // Helper threads need not worry about time and search info updates
            if (!mainThread) continue;

            // We delay reporting during MultiPV searches
            if (limits->multiPV > 1) report_multipv_lines(thread);

            // Update clock based on score and pv changes
            tm_update(thread, limits, tm);

            // Don't want to exit while pondering
            if (IS_PONDERING) continue;

            // Check for termination by any of the possible limits
            if ((limits->limitedBySelf && tm_finished(thread, tm))
                || (limits->limitedByDepth && thread->depth >= limits->depthLimit)
                || (limits->limitedByTime && elapsed_time(tm) >= limits->timeLimit))
                break;
        }
    }
    catch (Abort_)
    {   }
}

/// thread.c

void populateThreadPool(vector<Thread>* threads)
{
    for (size_t i = 0; i < threads->size(); i++)
    {
        auto& thread = (*threads)[i];
        // Offset the Node Stack to allow looking backwards
        thread.states = &(thread.nodeStates[STACK_OFFSET]);

        // NULL out the entire continuation history
        for (int j = 0; j < STACK_SIZE; j++)
            thread.nodeStates[j].continuations = NULL;

        // Threads will know of each other
        thread.index = i;
        thread.threads = &(*threads)[0];
        thread.nthreads = threads->size();

        // Accumulator stack and table require alignment
        thread.nnue = nnue_create_evaluator();
    }
}

void clearThreadPool(vector<Thread>* threads)
{
    for (auto& thread : *threads)
        nnue_delete_accumulators(thread.nnue);

    threads->clear();
}

void resetThreadPool(Thread* threads)
{
    // Reset the per-thread tables, used for move ordering
    // and evaluation caching. This is needed for ucinewgame
    // calls in order to ensure a deterministic behaviour

    for (int i = 0; i < threads->nthreads; i++)
    {
        memset(&threads[i].pktable, 0, sizeof(PKTable));

        memset(&threads[i].killers, 0, sizeof(KillerTable));
        memset(&threads[i].cmtable, 0, sizeof(CounterMoveTable));

        memset(&threads[i].history, 0, sizeof(HistoryTable));
        memset(&threads[i].chistory, 0, sizeof(CaptureHistoryTable));
        memset(&threads[i].continuation, 0, sizeof(ContinuationTable));
    }
}

void newSearchThreadPool(Thread* threads, State* state, Limits* limits, TimeManager* tm)
{
    // Initialize each Thread in the Thread Pool. We need a reference
    // to the UCI seach parameters, access to the timing information,
    // somewhere to store the results of each iteration by the main, and
    // our own copy of the state. Also, we reset the seach statistics

    for (int i = 0; i < threads->nthreads; i++)
    {
        threads[i].limits = limits;
        threads[i].tm = tm;
        threads[i].height = 0;
        threads[i].nodes = 0ull;
        threads[i].tbhits = 0ull;

        memcpy(&threads[i].state, state, sizeof(State));
        threads[i].state.thread = &threads[i];

        // Reset the accumulator stack. The table can remain
        threads[i].nnue->current = &threads[i].nnue->stack[0];
        threads[i].nnue->current->accurate[WHITE] = 0;
        threads[i].nnue->current->accurate[BLACK] = 0;

        memset(threads[i].nodeStates, 0, sizeof(NodeState) * STACK_SIZE);
    }
}

UCIMove_ getBestMove(Thread* threads, State* state, Limits* limits)
{
    vector<unique_ptr<thread>> pthreads(threads->nthreads);
    TimeManager tm = { 0 }; tm_init(limits, &tm);

    // Minor house keeping for starting a search
    tt_update(); // Table has an age component
    ABORT_SIGNAL = 0; // Otherwise Threads will exit
    newSearchThreadPool(threads, state, limits, &tm);

    // Allow Syzygy to refine the move list for optimal results
    if (!limits->limitedByMoves && limits->multiPV == 1)
        tablebasesProbeDTZ(state, limits);

    // Create a new thread for each of the helpers and reuse the current
    // thread for the main thread, which avoids some overhead and saves
    // us from having the current thread eating CPU time while waiting
    for (int i = 1; i < threads->nthreads; i++)
        pthreads[i].reset(new thread(&iterativeDeepening, &threads[i]));
    iterativeDeepening(&threads[0]);

    // When the main thread exits it should signal for the helpers to
    // shutdown. Wait until all helpers have finished before moving on
    ABORT_SIGNAL = 1;
    for (int i = 1; i < threads->nthreads; i++)
        pthreads[i]->join();

    // Pick the best of our completed threads
    return select_from_threads(threads);
}

struct UCIGoStruct {
    Thread* threads;
    State* state;
    Limits  limits;
    uint64 nodesSofar;
    double elapsedSofar;
};

void* start_search_threads(UCIGoStruct* go)
{
    Thread* threads = go->threads;
    State* state = go->state;
    Limits* limits = &go->limits;

    // Execute search, setting best and ponder moves
    auto uciMove = getBestMove(threads, state, limits);

    // UCI spec does not want reports until out of pondering
    while (IS_PONDERING);

    go->elapsedSofar += elapsed_time(threads->tm);
    go->nodesSofar += nodesSearchedThreadPool(threads);
    int nps = (int)(1000 * (go->nodesSofar / (1 + go->elapsedSofar)));
    printf("info nps %d\n", nps);

    // Report best move ( we should always have one )
    char str[6];
    moveToString(uciMove.best, str, state->chess960);
    printf("bestmove %s", str);

    // Report ponder move ( if we have one )
    if (uciMove.ponder != NONE_MOVE) {
        moveToString(uciMove.ponder, str, state->chess960);
        printf(" ponder %s", str);
    }

    // Make sure this all gets reported
    printf("\n"); fflush(stdout);

    return go;
}




/// pgn.h


enum { PGN_LOSS, PGN_DRAW, PGN_WIN, PGN_NO_RESULT, PGN_UNKNOWN_RESULT };

typedef struct PGNData {
    char* startpos;
    bool is_white, is_black;
    int result, plies;
    char buffer[65536];
} PGNData;



/// pgn.c


/// Ethereal's NNUE Data Format

typedef struct HalfKPSample {
    uint64 occupied;   // 8-byte occupancy bitboard ( No Kings )
    score_t  eval;       // 2-byte int for the target evaluation
    uint8_t  result;     // 1-byte int for result. { L=0, D=1, W=2 }
    uint8_t  turn;       // 1-byte int for the side-to-move flag
    uint8_t  wking;      // 1-byte int for the White King Square
    uint8_t  bking;      // 1-byte int for the Black King Square
    uint8_t  packed[15]; // 1-byte int per two non-King pieces
} HalfKPSample;

void pack_bitboard(uint8_t* packed, State* state, uint64 pieces) 
{
#define encode_piece(p) (8 * ColorOf(p) + TypeOf(p))
#define pack_pieces(p1, p2) (((p1) << 4) | (p2))

    uint8_t types[32] = { 0 };
    int N = (1 + popcount(pieces)) / 2;

    for (int i = 0; pieces; i++) {
        int sq = poplsb(&pieces);
        types[i] = encode_piece(state->board_.at_[sq]);
    }

    for (int i = 0; i < N; i++)
        packed[i] = pack_pieces(types[i * 2], types[i * 2 + 1]);

#undef encode_piece
#undef pack_pieces
}

void build_halfkp_sample(State* state, HalfKPSample* sample, unsigned result, score_t eval)
{
    const uint64 white = state->board_.colors_[WHITE];
    const uint64 black = state->board_.colors_[BLACK];
    const uint64 pieces = (white | black);

    sample->occupied = pieces & ~state->board_.Kings();
    sample->eval = state->turn == BLACK ? -eval : eval;
    sample->result = state->turn == BLACK ? 2u - result : result;
    sample->turn = state->turn;
    sample->wking = lsb(state->board_.Kings(WHITE));
    sample->bking = lsb(state->board_.Kings(BLACK));
    pack_bitboard(sample->packed, state, sample->occupied);
}


inline bool san_is_file(char chr) {
    return 'a' <= chr && chr <= 'h';
}

inline bool san_is_rank(char chr) {
    return '1' <= chr && chr <= '8';
}

inline bool san_is_square(const char* SAN) {
    return san_is_file(SAN[0]) && san_is_rank(SAN[1]);
}


inline bool san_has_promotion(const char* SAN) {
    for (const char* ptr = SAN; *ptr != '\0' && *ptr != ' '; ptr++)
        if (*ptr == '=') return true;
    return false;
}

inline bool san_has_capture(const char* SAN) {
    for (const char* ptr = SAN; *ptr != '\0' && *ptr != ' '; ptr++)
        if (*ptr == 'x') return true;
    return false;
}

inline int san_square(const char* str) {
    return 8 * (str[1] - '1') + (str[0] - 'a');
}

inline int san_promotion_type(char chr) 
{
    switch (chr) {
    case 'N': return KNIGHT_PROMO_MOVE;
    case 'B': return BISHOP_PROMO_MOVE;
    case 'R': return ROOK_PROMO_MOVE;
    default: return QUEEN_PROMO_MOVE;
    }
}


uint16_t san_pawn_push(State* state, const char* SAN) 
{
    int to, from, type;

    if (!san_is_square(SAN))
        return NONE_MOVE;

    // Assume a single pawn push
    to = san_square(SAN);
    from = state->turn == WHITE ? to - 8 : to + 8;

    // Promotion is entirely handled by a move flag
    type = san_has_promotion(SAN)
        ? san_promotion_type(SAN[3]) : NORMAL_MOVE;

    // Account for double pawn pushes
    if (state->board_.at_[from] != makePiece(PAWN, state->turn))
        from = state->turn == WHITE ? from - 8 : from + 8;

    // We can assert legality later
    return MoveMake(from, to, type);
}

uint16_t san_pawn_capture(State* state, const char* SAN) 
{
    uint64 pawns;
    int file, tosq, type;

    // Pawn Captures have a file and then an 'x'
    if (!san_is_file(SAN[0]) || !san_has_capture(SAN))
        return NONE_MOVE;

    // Their could be a rank given for the moving piece (???)
    file = SAN[0] - 'a';
    tosq = san_square(SAN + (SAN[1] != 'x') + 2);

    // If we capture "nothing", then we really En Passant
    if (state->board_.at_[tosq] == EMPTY) {
        int rank = state->turn == WHITE ? 4 : 3;
        return MoveMake(8 * rank + file, state->epSquare, ENPASS_MOVE);
    }

    // Promotion is entirely handled by a move flag
    type = !san_has_promotion(SAN) ? NORMAL_MOVE
        : san_promotion_type(SAN[(SAN[1] != 'x') + 5]);

    // Narrow down the position of the capturing Pawn
    pawns = File[file]
            & state->board_.Pawns(state->turn)
            & pawnAttacks(!state->turn, tosq);

    return MoveMake(lsb(pawns), tosq, type);
}

uint16_t san_castle_move(State* state, const char* SAN) 
{
    // Trivially check and build Queen Side Castles
    if (!strncmp(SAN, "O-O-O", 5)) {
        uint64 friendly = state->board_.colors_[state->turn];
        int king = lsb(friendly & state->board_.Kings());
        int rook = lsb(friendly & state->castleRooks);
        return MoveMake(king, rook, CASTLE_MOVE);
    }

    // Trivially check and build King Side Castles
    if (!strncmp(SAN, "O-O", 3)) {
        uint64 friendly = state->board_.colors_[state->turn];
        int king = lsb(friendly & state->board_.Kings());
        int rook = msb(friendly & state->castleRooks);
        return MoveMake(king, rook, CASTLE_MOVE);
    }

    return NONE_MOVE;
}

uint16_t san_piece_move(State* state, const char* SAN) 
{
    int piece, tosq = -1;
    bool has_file, has_rank, has_capt;
    uint64 options, occupied;

    // Decode the moving piece, which should be given
    switch (SAN[0]) {
    case 'K': piece = KING;   break;
    case 'Q': piece = QUEEN;  break;
    case 'R': piece = ROOK;   break;
    case 'B': piece = BISHOP; break;
    case 'N': piece = KNIGHT; break;
    default: return NONE_MOVE;
    }

    // Parse the SAN for various features. Captures are indicted by an 'x' inside
    // the SAN string. Checking of there is a File given requires you to identify
    // both a file, as well as another square, which is implied by the existence
    // of a capture. Likewise for Rank detection. The tosquare follows any 'x'

    has_capt = san_has_capture(SAN);

    has_file = san_is_file(SAN[1])
        && (has_capt || (san_is_square(SAN + 2) || san_is_square(SAN + 3)));

    has_rank = has_capt ? san_is_rank(SAN[1]) || san_is_square(SAN + 1)
        : (san_is_rank(SAN[1]) && san_is_square(SAN + 2))
        || (san_is_square(SAN + 1) && san_is_square(SAN + 3));

    tosq = san_square(SAN + has_file + has_rank + has_capt + 1);

    // From the to-sq, find any of our pieces which can attack. We ignore
    // pins, or otherwise illegal moves until later disambiguation

    occupied = state->board_.colors_[WHITE] | state->board_.colors_[BLACK];

    options = piece == KING ? kingAttacks(tosq)
        : piece == QUEEN ? queenAttacks(tosq, occupied)
        : piece == ROOK ? rookAttacks(tosq, occupied)
        : piece == BISHOP ? bishopAttacks(tosq, occupied)
        : piece == KNIGHT ? knightAttacks(tosq) : 0ull;

    options &= state->board_.colors_[state->turn] & state->board_.pieces_[piece];

    // Narrow down our options using the file disambiguation
    if (has_file)
        options &= File[SAN[1] - 'a'];

    // Narrow down our options using the rank disambiguation
    if (has_rank)
        options &= Line[SAN[1 + has_file] - '1'];

    // If we only have one option, we can delay the legality check
    if (Single(options))
        return MoveMake(lsb(options), tosq, NORMAL_MOVE);

    // If we have multiple options due to pins, we must verify now
    while (options) {
        uint16_t move = MoveMake(poplsb(&options), tosq, NORMAL_MOVE);
        if (moveIsLegal(state, move)) return move;
    }

    // This should never happen, based on the call order of parse_san()
    return NONE_MOVE;
}

uint16_t parse_san(State* state, const char* SAN) 
{
    uint16_t move = NONE_MOVE;

    // Keep trying to parse the move until success or out of attempts
    if (move == NONE_MOVE) move = san_pawn_push(state, SAN);
    if (move == NONE_MOVE) move = san_pawn_capture(state, SAN);
    if (move == NONE_MOVE) move = san_castle_move(state, SAN);
    if (move == NONE_MOVE) move = san_piece_move(state, SAN);

    // This should not be needed, but lets verify to be safe
    return !moveIsLegal(state, move) ? NONE_MOVE : move;
}


int pgn_read_until_move(char* buffer, int index) {
    for (; !isalpha(buffer[index]) && buffer[index] != '\0'; index++);
    return index;
}

int pgn_read_until_space(char* buffer, int index) {
    for (; buffer[index] != ' ' && buffer[index] != '\0'; index++);
    return index;
}


bool pgn_read_headers(FILE* pgn, PGNData* data) 
{
    if (fgets(data->buffer, 65536, pgn) == NULL)
        return false;

    if (strstr(data->buffer, "[White \"Ethereal") == data->buffer)
        data->is_white = true;

    else if (strstr(data->buffer, "[Black \"Ethereal") == data->buffer)
        data->is_black = true;

    else if (strstr(data->buffer, "[Result \"0-1\"]") == data->buffer)
        data->result = PGN_LOSS;

    else if (strstr(data->buffer, "[Result \"1/2-1/2\"]") == data->buffer)
        data->result = PGN_DRAW;

    else if (strstr(data->buffer, "[Result \"1-0\"]") == data->buffer)
        data->result = PGN_WIN;

    else if (strstr(data->buffer, "[Result \"*\"") == data->buffer)
        data->result = PGN_UNKNOWN_RESULT;

    else if (strstr(data->buffer, "[FEN \"") == data->buffer) {
        *strstr(data->buffer, "\"]") = '\0';
        data->startpos = _strdup(data->buffer + strlen("[FEN \""));
    }

    return data->buffer[0] == '[';
}

void pgn_read_moves(FILE* pgn, FILE* bindata, PGNData* data, HalfKPSample* samples, State* state) 
{
    Undo undo;
    double feval;
    uint16_t move;
    int eval, placed = 0, index = 0;

    if (fgets(data->buffer, 65536, pgn) == NULL)
        return;

    while (1) {

        // Read and Apply the next move if there is one
        index = pgn_read_until_move(data->buffer, index);
        if (data->buffer[index] == '\0') break;
        move = parse_san(state, data->buffer + index);

        // Assume that each move has an associated score
        index = pgn_read_until_space(data->buffer, index);

        // Scan for an eval and ignore Mate scores
        if (sscanf(data->buffer + index + 1, "%lf", &feval) == 1)
            eval = static_cast<int>(0.5 + 100.0 * feval);
        else eval = MATE;

        // Use White's POV for all evaluations
        if (state->turn == BLACK) eval = -eval;

        // Use the sample if it is quiet and within [-2000, 2000] cp
        if (abs(eval) <= 2000
            && !state->kingAttackers
            && !moveIsTactical(state->board_, move)
            && (state->turn == WHITE ? data->is_white : data->is_black))
            build_halfkp_sample(state, &samples[placed++], data->result, eval);

        // Skip head to the end of this comment to prepare for the next Move
        index = pgn_read_until_space(data->buffer, index + 1); data->plies++;
        applyMove(state, move, &undo);
    }

    if (data->result != PGN_UNKNOWN_RESULT)
        fwrite(samples, sizeof(HalfKPSample), placed, bindata);
}

/// state.c again

void boardFromFEN(State* state, const char* fen, int chess960)
{
    constexpr uint64 StandardCastles = (1ull << 0) | (1ull << 7) | (1ull << 56) | (1ull << 63);

    int sq = 56;
    char ch;
    char* str = strdup(fen), * strPos = NULL;
    char* token = strtok_r(str, " ", &strPos);
    uint64 rooks, kings, white, black;

    clearBoard(state); // Zero out, set squares to EMPTY

    // Piece placement
    while ((ch = *token++)) {
        if (isdigit(ch))
            sq += ch - '0';
        else if (ch == '/')
            sq -= 16;
        else {
            const bool colour = islower(ch);
            if (const char* piece = strchr(PieceLabel[colour], ch))
                setSquare(state, colour, static_cast<int>(piece - PieceLabel[colour]), sq++);
        }
    }
    state->matIndex = MatIndex<false>(state->board_);

    // Turn of play
    token = strtok_r(NULL, " ", &strPos);
    state->turn = token[0] == 'w' ? WHITE : BLACK;
    if (state->turn == BLACK) state->hash ^= ZobristTurnKey;

    // Castling rights
    token = strtok_r(NULL, " ", &strPos);

    rooks = state->board_.Rooks();
    kings = state->board_.Kings();
    white = state->board_.colors_[WHITE];
    black = state->board_.colors_[BLACK];

    while ((ch = *token++)) {
        if (ch == 'K') setBit(&state->castleRooks, msb(white & rooks & Line[0]));
        if (ch == 'Q') setBit(&state->castleRooks, lsb(white & rooks & Line[0]));
        if (ch == 'k') setBit(&state->castleRooks, msb(black & rooks & Line[7]));
        if (ch == 'q') setBit(&state->castleRooks, lsb(black & rooks & Line[7]));
        if ('A' <= ch && ch <= 'H') setBit(&state->castleRooks, square(0, ch - 'A'));
        if ('a' <= ch && ch <= 'h') setBit(&state->castleRooks, square(7, ch - 'a'));
    }

    for (sq = 0; sq < N_SQUARES; sq++) {
        state->castleMasks[sq] = 15;
        if (HasBit(state->castleRooks, sq))
            state->castleMasks[sq] &= ~Bit(CornerIndex(sq));
        if (HasBit(white & kings, sq))
            state->castleMasks[sq] &= 12;
        if (HasBit(black & kings, sq))
            state->castleMasks[sq] &= 3;
    }

    rooks = state->castleRooks;
    while (rooks) state->hash ^= ZobristCastleKeys[poplsb(&rooks)];

    // En passant square
    state->epSquare = stringToSquare(strtok_r(NULL, " ", &strPos));
    if (state->epSquare != -1)
        state->hash ^= ZobristEnpassKeys[FileOf(state->epSquare)];

    // Half & Full Move Counters
    state->halfMoveCounter = atoi(strtok_r(NULL, " ", &strPos));
    state->fullMoveCounter = atoi(strtok_r(NULL, " ", &strPos));

    // Move count: ignore and use zero, as we count since root
    state->numMoves = 0;

    // Need king attackers for move generation
    state->kingAttackers = attackersToKingSquare(*state);

    // Need squares attacked by the opposing player
    state->threats = allAttackedSquares(state->board_, !state->turn);

    // We save the game mode in order to comply with the UCI rules for printing
    // moves. If chess960 is not enabled, but we have detected an unconventional
    // castle setup, then we set chess960 to be true on our own. Currently, this
    // is simply a hack so that FRC positions may be added to the bench.csv
    state->chess960 = chess960 || (state->castleRooks & ~StandardCastles);

    state->thread = NULL; // By default, a State is not tied to any Thread

    free(str);
}

bool process_next_pgn(FILE* pgn, FILE* bindata, PGNData* data, HalfKPSample* samples, State* state)
{
    // Make sure to cleanup previous PGNs
    if (data->startpos != NULL)
        free(data->startpos);

    // Clear the current PGN to the blank state
    data->startpos = NULL;
    data->is_white = false;
    data->is_black = false;
    data->result = PGN_NO_RESULT;
    data->plies = 0;

    // Read Result & Fen and skip to Moves
    while (pgn_read_headers(pgn, data));

    // Process until we don't get a Result header
    if (data->result == PGN_NO_RESULT)
        return false;

    // Init the state, let Ethereal determine FRC
    boardFromFEN(state, data->startpos, 0);

    // Use all positions if neither matched Ethereal
    if (!data->is_white && !data->is_black)
        data->is_white = data->is_black = true;

    // Read Result & Fen and skip to Moves
    pgn_read_moves(pgn, bindata, data, samples, state);

    // Skip the trailing Newline of each PGN
    if (fgets(data->buffer, 65536, pgn) == NULL)
        return false;

    return true;
}


void process_pgn(const char* fin, const char* fout) 
{
    FILE* pgn = fopen(fin, "r");
    FILE* bindata = fopen(fout, "wb");
    unique_ptr<PGNData> data(new PGNData);
    vector<HalfKPSample> samples(1024);

    State state;
    while (process_next_pgn(pgn, bindata, data.get(), &samples[0], &state));
    fclose(pgn); fclose(bindata); 
}


uint64 perft(State* state, int depth) 
{
    Undo undo[1];
    ptrdiff_t size = 0;
    uint64 found = 0ull;
    uint16_t moves[MAX_MOVES];

    if (depth == 0) return 1ull;

    // Call genAllNoisyMoves() & genAllNoisyMoves()
    size += genAllNoisyMoves(state, moves);
    size += genAllQuietMoves(state, moves + size);

    // Recurse on all valid moves
    for (size -= 1; size >= 0; size--) {
        applyMove(state, moves[size], undo);
        if (moveWasLegal(*state)) found += perft(state, depth - 1);
        revertMove(state, moves[size], undo);
    }

    return found;
}



/// cmdline.c

void runBenchmark(int argc, char** argv)
{
    static const char* Benchmarks[] = {
        #include "bench.csv"
        ""
    };

    State state;
    Limits limits = { 0 };

    double times[256];
    uint64 nodes[256];

    double time;
    uint64 totalNodes = 0ull;

    int depth = argc > 2 ? atoi(argv[2]) : 13;
    int nthreads = argc > 3 ? atoi(argv[3]) : 1;
    int megabytes = argc > 4 ? atoi(argv[4]) : 16;

    if (argc > 5) {
        nnue_init(argv[5]);
        printf("info string set EvalFile to %s\n", argv[5]);
    }

    tt_init(nthreads, megabytes);
    time = get_real_time();
    vector<Thread> threads(nthreads);
    populateThreadPool(&threads);

    // Initialize a "go depth <x>" search
    limits.multiPV = 1;
    limits.limitedByDepth = 1;
    limits.depthLimit = depth;

    vector<UCIMove_> moves;
    for (int i = 0; strcmp(Benchmarks[i], ""); i++)
    {
        // Perform the search on the position
        limits.start = get_real_time();
        boardFromFEN(&state, Benchmarks[i], 0);
        moves.push_back(getBestMove(&threads[0], &state, &limits));

        // Stat collection for later printing
        times[i] = get_real_time() - limits.start;
        nodes[i] = nodesSearchedThreadPool(&threads[0]);

        tt_clear(nthreads); // Reset TT between searches
    }

    printf("\n===============================================================================\n");

    for (int i = 0; strcmp(Benchmarks[i], ""); i++) 
    {
        // Convert moves to typical UCI notation
        char bestStr[6], ponderStr[6];
        moveToString(moves[i].best, bestStr, 0);
        moveToString(moves[i].ponder, ponderStr, 0);

        // Log all collected information for the current position
        printf("[# %2d] %5d cp  Best:%6s  Ponder:%6s %12d nodes %12d nps\n", i + 1, moves[i].score,
            bestStr, ponderStr, (int)nodes[i], (int)(1000.0f * nodes[i] / (times[i] + 1)));
    }

    printf("===============================================================================\n");

    // Report the overall statistics
    time = get_real_time() - time;
    for (int i = 0; strcmp(Benchmarks[i], ""); i++) totalNodes += nodes[i];
    printf("OVERALL: %47d nodes %12d nps\n", (int)totalNodes, (int)(1000.0f * totalNodes / (time + 1)));

    clearThreadPool(&threads);
}

void runEvalBook(int argc, char** argv) 
{
    State state;
    char line[256];
    Limits limits = { 0 };
    double start = get_real_time();

    FILE* book = fopen(argv[2], "r");
    int depth = argc > 3 ? atoi(argv[3]) : 12;
    int nthreads = argc > 4 ? atoi(argv[4]) : 1;
    int megabytes = argc > 5 ? atoi(argv[5]) : 2;

    vector<Thread> threads(nthreads);
    populateThreadPool(&threads);

    limits.multiPV = 1;
    limits.limitedByDepth = 1;
    limits.depthLimit = depth;
    tt_init(nthreads, megabytes);

    while ((fgets(line, 256, book)) != NULL) {
        limits.start = get_real_time();
        boardFromFEN(&state, line, 0);
        auto move = getBestMove(&threads[0], &state, &limits);
        resetThreadPool(&threads[0]);
        tt_clear(nthreads);
        printf("FEN: %s", line);
    }

    printf("Time %dms\n", (int)(get_real_time() - start));
}

int strEquals(const char* str1, const char* str2) {
    return strcmp(str1, str2) == 0;
}

int strStartsWith(const char* str, const char* key) {
    return strstr(str, key) == str;
}

int strContains(const char* str, const char* key) {
    return strstr(str, key) != NULL;
}

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

void handleCommandLine(int argc, char** argv) 
{
    // Output all the wonderful things we can do from the Command Line
    if (argc > 1 && strEquals(argv[1], "--help")) {
        printf("\nbench     [depth=13] [threads=1] [hash=16] [NNUE=None]");
        printf("\n          Run searches on a set of positions to compute a hash\n");
        printf("\nevalbook  [input-file] [depth=12] [threads=1] [hash=2]");
        printf("\n          Evaluate all positions in a FEN file using various options\n");
        printf("\nnndata    [input-file] [output-file]");
        printf("\n          Build an nndata from a stripped pgn file\n");
        exit(EXIT_SUCCESS);
    }

    // Benchmark is being run from the command line
    if (argc > 1 && strEquals(argv[1], "bench")) {
        runBenchmark(argc, argv);
        exit(EXIT_SUCCESS);
    }

    // Evaluate all positions in a datafile to a given depth
    if (argc > 2 && strEquals(argv[1], "evalbook")) {
        runEvalBook(argc, argv);
        exit(EXIT_SUCCESS);
    }

    // Convert a PGN file to an nndata file
    if (argc > 3 && strEquals(argv[1], "nndata")) {
        process_pgn(argv[2], argv[3]);
        exit(EXIT_SUCCESS);
    }

    // Tuner is being run from the command line
#ifdef TUNE
    runTuner();
    exit(EXIT_SUCCESS);
#endif
}

/// uci.c

const char* StartPosition = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

void uciPosition(char* str, State* state, int chess960)
{
    int size;
    uint16_t moves[MAX_MOVES];
    char* ptr, moveStr[6], testStr[6];
    Undo undo[1];

    // Position is defined by a FEN, X-FEN or Shredder-FEN
    if (strContains(str, "fen"))
        boardFromFEN(state, strstr(str, "fen") + strlen("fen "), chess960);

    // Position is simply the usual starting position
    else if (strContains(str, "startpos"))
        boardFromFEN(state, StartPosition, chess960);

    // Position command may include a list of moves
    ptr = strstr(str, "moves");
    if (ptr != NULL)
        ptr += strlen("moves ");

    // Apply each move in the move list
    while (ptr != NULL && *ptr != '\0')
    {
        // UCI sends moves in long algebraic notation
        for (int i = 0; i < 4; i++) moveStr[i] = *ptr++;
        moveStr[4] = *ptr == '\0' || *ptr == ' ' ? '\0' : *ptr++;
        moveStr[5] = '\0';

        // Generate moves for this position
        size = static_cast<int>(genAllLegalMoves(state, moves));

        // Find and apply the given move
        for (int i = 0; i < size; i++) {
            moveToString(moves[i], testStr, state->chess960);
            if (strEquals(moveStr, testStr)) {
                applyMove(state, moves[i], undo);
                break;
            }
        }

        // Reset move history whenever we reset the fifty move rule. This way
        // we can track all positions that are candidates for repetitions, and
        // are still able to use a fixed size for the history array (512)
        if (state->halfMoveCounter == 0)
            state->numMoves = 0;

        // Skip over all white space
        while (*ptr == ' ') ptr++;
    }
}

void uciSetOption(char* str, vector<Thread>* threads, int* multiPV, int* chess960)
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

    if (strStartsWith(str, "setoption name Hash value ")) {
        int megabytes = atoi(str + strlen("setoption name Hash value "));
        printf("info string set Hash to %dMB\n", tt_init(threads->size(), megabytes));
    }

    if (strStartsWith(str, "setoption name Threads value ")) {
        int nthreads = atoi(str + strlen("setoption name Threads value "));
        clearThreadPool(threads);
        threads->resize(nthreads);
        populateThreadPool(threads);
        printf("info string set Threads to %d\n", nthreads);
    }

    if (strStartsWith(str, "setoption name EvalFile value ")) {
        char* ptr = str + strlen("setoption name EvalFile value ");
        if (!strStartsWith(ptr, "<empty>")) nnue_init(ptr);
        printf("info string set EvalFile to %s\n", ptr);
    }

    if (strStartsWith(str, "setoption name MultiPV value ")) {
        *multiPV = atoi(str + strlen("setoption name MultiPV value "));
        printf("info string set MultiPV to %d\n", *multiPV);
    }

    if (strStartsWith(str, "setoption name MoveOverhead value ")) {
        MoveOverhead = atoi(str + strlen("setoption name MoveOverhead value "));
        printf("info string set MoveOverhead to %d\n", MoveOverhead);
    }

    if (strStartsWith(str, "setoption name SyzygyPath value ")) {
        char* ptr = str + strlen("setoption name SyzygyPath value ");
        if (!strStartsWith(ptr, "<empty>")) tb_init(ptr);
        printf("info string set SyzygyPath to %s\n", ptr);
    }

    if (strStartsWith(str, "setoption name SyzygyProbeDepth value ")) {
        TB_PROBE_DEPTH = atoi(str + strlen("setoption name SyzygyProbeDepth value "));
        printf("info string set SyzygyProbeDepth to %u\n", TB_PROBE_DEPTH);
    }

    if (strStartsWith(str, "setoption name UCI_Chess960 value ")) {
        if (strStartsWith(str, "setoption name UCI_Chess960 value true"))
            printf("info string set UCI_Chess960 to true\n"), * chess960 = 1;
        if (strStartsWith(str, "setoption name UCI_Chess960 value false"))
            printf("info string set UCI_Chess960 to false\n"), * chess960 = 0;
    }

    fflush(stdout);
}

thread* uciGo(UCIGoStruct* ucigo, Thread* threads, State* state, int multiPV, char* str)
{
    /// Parse the entire "go" command in order to fill out a Limits struct, found at ucigo->limits.
    /// After we have processed all of this, we can execute a new search thread, held by *pthread,
    /// and detach it.

    double start = get_real_time();
    double wtime = 0, btime = 0;
    double winc = 0, binc = 0, mtg = -1;

    char moveStr[6];
    char* ptr = strtok(str, " ");

    uint16_t moves[MAX_MOVES];
    int size = static_cast<int>(genAllLegalMoves(state, moves)), idx = 0;

    Limits* limits = &ucigo->limits;
    memset(limits, 0, sizeof(Limits));

    IS_PONDERING = FALSE; // Reset PONDERING every time to be safe

    for (ptr = strtok(NULL, " "); ptr != NULL; ptr = strtok(NULL, " "))
    {
        // Parse time control conditions
        if (strEquals(ptr, "wtime")) wtime = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "btime")) btime = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "winc")) winc = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "binc")) binc = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "movestogo")) mtg = atoi(strtok(NULL, " "));

        // Parse special search termination conditions
        if (strEquals(ptr, "depth")) limits->depthLimit = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "movetime")) limits->timeLimit = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "nodes")) limits->nodeLimit = static_cast<uint64>(atof(strtok(NULL, " ")));

        // Parse special search modes
        if (strEquals(ptr, "infinite")) limits->limitedByNone = TRUE;
        if (strEquals(ptr, "searchmoves")) limits->limitedByMoves = TRUE;
        if (strEquals(ptr, "ponder")) IS_PONDERING = TRUE;

        // Parse any specific moves that we are to search
        for (int i = 0; i < size; i++) {
            moveToString(moves[i], moveStr, state->chess960);
            if (strEquals(ptr, moveStr)) limits->searchMoves[idx++] = moves[i];
        }
    }

    // Special exit cases: Time, Depth, and Nodes
    limits->limitedByTime = limits->timeLimit != 0;
    limits->limitedByDepth = limits->depthLimit != 0;
    limits->limitedByNodes = limits->nodeLimit != 0;

    // No special case nor infinite, so we set our own time
    limits->limitedBySelf = !limits->depthLimit && !limits->timeLimit
        && !limits->limitedByNone && !limits->nodeLimit;

    // Pick the time values for the colour we are playing as
    limits->start = start;
    limits->time = (state->turn == WHITE) ? wtime : btime;
    limits->inc = (state->turn == WHITE) ? winc : binc;
    limits->mtg = (state->turn == WHITE) ? mtg : mtg;

    // Cap our MultiPV search based on the suggested or legal moves
    limits->multiPV = Min(multiPV, limits->limitedByMoves ? idx : size);

    // Prepare the uciGoStruct for the new pthread
    ucigo->state = state;
    ucigo->threads = threads;

    // Spawn a new thread to handle the search
    return new thread(&start_search_threads, ucigo);
}

int e_main(int argc, char** argv) 
{
    State state;
    char str[8192] = { 0 };
    unique_ptr<thread> pthreadsgo;
    UCIGoStruct uciGoStruct;

    int chess960 = 0;
    int multiPV = 1;

    // Initialize core components of Ethereal
    initAttacks(); initMasks(); initMaterial();
    initSearch(); initZobrist(); tt_init(1, 16);
    initPKNetwork(); nnue_incbin_init();

    // Create the UCI-state and our threads
    vector<Thread> threads(1);
    populateThreadPool(&threads);
    boardFromFEN(&state, StartPosition, chess960);

    // Handle any command line requests
    handleCommandLine(argc, argv);

    /*
    |------------|-----------------------------------------------------------------------|
    |  Commands  | Response. * denotes that the command blocks until no longer searching |
    |------------|-----------------------------------------------------------------------|
    |        uci |           Outputs the engine name, authors, and all available options |
    |    isready | *           Responds with readyok when no longer searching a position |
    | ucinewgame | *  Resets the TT and any Hueristics to ensure determinism in searches |
    |  setoption | *     Sets a given option and reports that the option was set if done |
    |   position | *  Sets the state position via an optional FEN and optional move list |
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
            printf("id name Ethereal " ETHEREAL_VERSION "\n");
            printf("id author Andrew Grant, Alayan & Laldon\n");
            printf("option name Hash type spin default 16 min 2 max 131072\n");
            printf("option name Threads type spin default 1 min 1 max 2048\n");
            printf("option name EvalFile type string default <empty>\n");
            printf("option name MultiPV type spin default 1 min 1 max 256\n");
            printf("option name MoveOverhead type spin default 300 min 0 max 10000\n");
            printf("option name SyzygyPath type string default <empty>\n");
            printf("option name SyzygyProbeDepth type spin default 0 min 0 max 127\n");
            printf("option name Ponder type check default false\n");
            printf("option name AnalysisMode type check default false\n");
            printf("option name UCI_Chess960 type check default false\n");
            printf("info string licensed to " LICENSE_OWNER "\n");
            printf("uciok\n"), fflush(stdout);
        }

        else if (strEquals(str, "isready"))
            printf("readyok\n"), fflush(stdout);

        else if (strEquals(str, "ucinewgame"))
            resetThreadPool(&threads[0]), tt_clear(threads[0].nthreads);

        else if (strStartsWith(str, "setoption"))
            uciSetOption(str, &threads, &multiPV, &chess960);

        else if (strStartsWith(str, "position"))
            uciPosition(str, &state, chess960);

        else if (strStartsWith(str, "go"))
        {
            pthreadsgo.reset(uciGo(&uciGoStruct, &threads[0], &state, multiPV, str));
            pthreadsgo->detach();   // maybe not needed?
        }

        else if (strEquals(str, "ponderhit"))
            IS_PONDERING = 0;

        else if (strEquals(str, "stop"))
            ABORT_SIGNAL = 1, IS_PONDERING = 0;

        else if (strEquals(str, "quit"))
            break;

        else if (strStartsWith(str, "perft"))
            cout << perft(&state, atoi(str + strlen("perft "))) << endl;

        else if (strStartsWith(str, "print"))
            printBoard(&state), fflush(stdout);
    }

    return 0;
}

#endif

