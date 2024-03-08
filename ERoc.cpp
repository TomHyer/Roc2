
/// Roc and Platform

template<class T_> inline const T_& Max(const T_& lhs, const T_& rhs) { return lhs < rhs ? rhs : lhs; }
template<class T_> inline const T_& Min(const T_& lhs, const T_& rhs) { return lhs < rhs ? lhs : rhs; }
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
#include <array>

using std::array;
#undef assert
#define assert(x)

constexpr int FALSE = 0, TRUE = 1;
enum { MG, EG, N_PHASES };
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

constexpr int MATE_IN_MAX = 32000, MATE = MATE_IN_MAX + MAX_PLY;
constexpr int TBWIN_IN_MAX = 30976, TBWIN = TBWIN_IN_MAX + MAX_PLY;
constexpr int VALUE_NONE = MATE + 1;

constexpr int N_RANKS = 8, N_FILES = 8, N_SQUARES = N_RANKS * N_FILES;

constexpr inline int TypeOf(int piece) { return piece / 4; }
constexpr inline int ColorOf(int piece) { return piece % 4; }

constexpr inline int IsPiece(int piece) { return piece >= 0 && TypeOf(piece) < N_PIECES && ColorOf(piece) < N_COLORS; }

inline int pieceType(int piece)
{
    assert(IsPiece(piece));
    return TypeOf(piece);
}
inline int pieceColour(int piece) 
{
    assert(IsPiece(piece));
    return ColorOf(piece);
}

static inline int makePiece(int type, int colour) {
    assert(0 <= type && type < N_PIECES);
    assert(0 <= colour && colour <= N_COLORS);
    return ColoredPiece(colour, type);
}

// Renamings, currently for move ordering

constexpr int N_KILLER = 2, N_CONTINUATION = 2;
using KillerTable = array<array<uint16_t, 2>, MAX_PLY + 1>;
using CounterMoveTable = array<array<array<uint16_t, N_SQUARES>, N_PIECES>, N_COLORS>;
using HistoryTable = array<array<array<array<array<int16_t, N_SQUARES>, N_SQUARES>, 2>, 2>, N_COLORS>;
using CaptureHistoryTable = array<array<array<array<array<int16_t, N_PIECES - 1>, N_SQUARES>, 2>, 2>, N_PIECES>;
using ContinuationTable = array<array<array<array<array<array<int16_t, N_SQUARES>, N_PIECES>, N_CONTINUATION>, N_SQUARES>, N_PIECES>, 2>;

inline int MakeScore(int mg, int eg) { return (int)((unsigned int)(eg) << 16) + mg; }
inline int ScoreMG(int s) { return (int16_t)((uint16_t)((unsigned)(s))); }
inline int ScoreEG(int s) { return (int16_t)((uint16_t)((unsigned)(s + 0x8000) >> 16)); }

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
template<int N> void Prefetch(const char* p)
{
    //p -= reinterpret_cast<size_t>(p) & 63;
    for (int ii = 0; ii < N; ++ii)
        Prefetch1(p + 64 * ii);
}
#else
#define INLINE static inline __attribute__((always_inline))
#define NOINLINE __attribute__((noinline))
#endif


/// bitboards.h

constexpr uint64_t
    RANK_1 = 0x00000000000000FFull,
    RANK_2 = 0x000000000000FF00ull,
    RANK_3 = 0x0000000000FF0000ull,
    RANK_4 = 0x00000000FF000000ull,
    RANK_5 = 0x000000FF00000000ull,
    RANK_6 = 0x0000FF0000000000ull,
    RANK_7 = 0x00FF000000000000ull,
    RANK_8 = 0xFF00000000000000ull,

    FILE_A = 0x0101010101010101ull,
    FILE_B = 0x0202020202020202ull,
    FILE_C = 0x0404040404040404ull,
    FILE_D = 0x0808080808080808ull,
    FILE_E = 0x1010101010101010ull,
    FILE_F = 0x2020202020202020ull,
    FILE_G = 0x4040404040404040ull,
    FILE_H = 0x8080808080808080ull,

    WHITE_SQUARES = 0x55AA55AA55AA55AAull,
    BLACK_SQUARES = 0xAA55AA55AA55AA55ull,

    LONG_DIAGONALS = 0x8142241818244281ull,
    CENTER_SQUARES = 0x0000001818000000ull,
    CENTER_BIG = 0x00003C3C3C3C0000ull,

    LEFT_FLANK = FILE_A | FILE_B | FILE_C | FILE_D,
    RIGHT_FLANK = FILE_E | FILE_F | FILE_G | FILE_H,

    PROMOTION_RANKS = RANK_1 | RANK_8;

extern const array<uint64_t, 8> Files, Ranks;

int INLINE FileOf(int sq) { return sq % N_FILES; }
constexpr array<int, 8> MIRROR_FILE = { 0, 1, 2, 3, 3, 2, 1, 0 };
INLINE int RankOf(int sq) { return sq / N_FILES; }


/// bitboards.c

const array<uint64_t, 8> Files = { FILE_A, FILE_B, FILE_C, FILE_D, FILE_E, FILE_F, FILE_G, FILE_H };
const array<uint64_t, 8> Ranks = { RANK_1, RANK_2, RANK_3, RANK_4, RANK_5, RANK_6, RANK_7, RANK_8 };

int fileOf(int sq) {
    assert(0 <= sq && sq < N_SQUARES);
    return FileOf(sq);
}

int mirrorFile(int file) {
    assert(0 <= file && file < N_FILES);
    return MIRROR_FILE[file];
}

int rankOf(int sq) {
    assert(0 <= sq && sq < N_SQUARES);
    return RankOf(sq);
}

int relativeRankOf(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return colour == WHITE ? rankOf(sq) : 7 - rankOf(sq);
}

int square(int rank, int file) {
    assert(0 <= rank && rank < N_RANKS);
    assert(0 <= file && file < N_FILES);
    return rank * N_FILES + file;
}

int relativeSquare(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return square(relativeRankOf(colour, sq), fileOf(sq));
}

int relativeSquare32(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return 4 * relativeRankOf(colour, sq) + mirrorFile(fileOf(sq));
}

bool testBit(uint64_t bb, int i) {
    assert(0 <= i && i < N_SQUARES);
    return bb & (1ull << i);
}

void setBit(uint64_t* bb, int i) {
    assert(!testBit(*bb, i));
    *bb ^= 1ull << i;
}

void clearBit(uint64_t* bb, int i) {
    assert(testBit(*bb, i));
    *bb ^= 1ull << i;
}

uint64_t squaresOfMatchingColour(int sq) {
    assert(0 <= sq && sq < N_SQUARES);
    return testBit(WHITE_SQUARES, sq) ? WHITE_SQUARES : BLACK_SQUARES;
}

int popcount(uint64_t bb) {
#ifdef _MSC_VER
    return static_cast<int>(_mm_popcnt_u64(bb));
#else
    return __builtin_popcountll(bb);
#endif
}

int getlsb(uint64_t bb) {
    assert(bb);  // lsb(0) is undefined
#ifdef _MSC_VER
    unsigned long y;
    _BitScanForward64(&y, bb);
    return y;
#else
    return __builtin_ctzll(bb);
#endif
}

int getmsb(uint64_t bb) {
    assert(bb);  // msb(0) is undefined
#ifdef _MSC_VER
    unsigned long y;
    _BitScanReverse64(&y, bb);
    return y;
#else
    return __builtin_clzll(bb) ^ 63;
#endif
}

int frontmost(int colour, uint64_t bb) {
    assert(0 <= colour && colour < N_COLORS);
    return colour == WHITE ? getmsb(bb) : getlsb(bb);
}

int backmost(int colour, uint64_t bb) {
    assert(0 <= colour && colour < N_COLORS);
    return colour == WHITE ? getlsb(bb) : getmsb(bb);
}

int poplsb(uint64_t* bb) {
    int lsb = getlsb(*bb);
    *bb &= *bb - 1;
    return lsb;
}

int popmsb(uint64_t* bb) {
    int msb = getmsb(*bb);
    *bb ^= 1ull << msb;
    return msb;
}

bool several(uint64_t bb) {
    return bb & (bb - 1);
}

bool onlyOne(uint64_t bb) {
    return bb && !several(bb);
}

void printBitboard(uint64_t bb) {

    for (int rank = 7; rank >= 0; rank--) {
        char line[] = ". . . . . . . .";

        for (int file = 0; file < N_FILES; file++)
            if (testBit(bb, square(rank, file)))
                line[2 * file] = 'X';

        printf("%s\n", line);
    }

    printf("\n");
}

/// PSQT from evaluate.c

/* Piece Square Evaluation Terms */

#define S MakeScore

const int PawnPSQT[N_SQUARES] = {
    S(0,   0), S(0,   0), S(0,   0), S(0,   0),
    S(0,   0), S(0,   0), S(0,   0), S(0,   0),
    S(-13,   7), S(-4,   0), S(1,   4), S(6,   1),
    S(3,  10), S(-9,   4), S(-9,   3), S(-16,   7),
    S(-21,   5), S(-17,   6), S(-1,  -6), S(12, -14),
    S(8, -10), S(-4,  -5), S(-15,   7), S(-24,  11),
    S(-14,  16), S(-21,  17), S(9, -10), S(10, -24),
    S(4, -22), S(4, -10), S(-20,  17), S(-17,  18),
    S(-15,  18), S(-18,  11), S(-16,  -8), S(4, -30),
    S(-2, -24), S(-18,  -9), S(-23,  13), S(-17,  21),
    S(-20,  48), S(-9,  44), S(1,  31), S(17,  -9),
    S(36,  -6), S(-9,  31), S(-6,  45), S(-23,  49),
    S(-33, -70), S(-66,  -9), S(-16, -22), S(65, -23),
    S(41, -18), S(39, -14), S(-47,   4), S(-62, -51),
    S(0,   0), S(0,   0), S(0,   0), S(0,   0),
    S(0,   0), S(0,   0), S(0,   0), S(0,   0),
};

const int KnightPSQT[N_SQUARES] = {
    S(-31, -38), S(-6, -24), S(-20, -22), S(-16,  -1),
    S(-11,  -1), S(-22, -19), S(-8, -20), S(-41, -30),
    S(1,  -5), S(-11,   3), S(-6, -19), S(-1,  -2),
    S(0,   0), S(-9, -16), S(-8,  -3), S(-6,   1),
    S(7, -21), S(8,  -5), S(7,   2), S(10,  19),
    S(10,  19), S(4,   2), S(8,  -4), S(3, -19),
    S(16,  21), S(17,  30), S(23,  41), S(27,  50),
    S(24,  53), S(23,  41), S(19,  28), S(13,  26),
    S(13,  30), S(23,  30), S(37,  51), S(30,  70),
    S(26,  67), S(38,  50), S(22,  33), S(14,  28),
    S(-24,  25), S(-5,  37), S(25,  56), S(22,  60),
    S(27,  55), S(29,  55), S(-1,  32), S(-19,  25),
    S(13,  -2), S(-11,  18), S(27,  -2), S(37,  24),
    S(41,  24), S(40,  -7), S(-13,  16), S(2,  -2),
    S(-167,  -5), S(-91,  12), S(-117,  41), S(-38,  17),
    S(-18,  19), S(-105,  48), S(-119,  24), S(-165, -17),
};

const int BishopPSQT[N_SQUARES] = {
    S(5, -21), S(1,   1), S(-1,   5), S(1,   5),
    S(2,   8), S(-6,  -2), S(0,   1), S(4, -25),
    S(26, -17), S(2, -31), S(15,  -2), S(8,   8),
    S(8,   8), S(13,  -3), S(9, -31), S(26, -29),
    S(9,   3), S(22,   9), S(-5,  -3), S(18,  19),
    S(17,  20), S(-5,  -6), S(20,   4), S(15,   8),
    S(0,  12), S(10,  17), S(17,  32), S(20,  32),
    S(24,  34), S(12,  30), S(15,  17), S(0,  14),
    S(-20,  34), S(13,  31), S(1,  38), S(21,  45),
    S(12,  46), S(6,  38), S(13,  33), S(-14,  37),
    S(-13,  31), S(-11,  45), S(-7,  23), S(2,  40),
    S(8,  38), S(-21,  34), S(-5,  46), S(-9,  35),
    S(-59,  38), S(-49,  22), S(-13,  30), S(-35,  36),
    S(-33,  36), S(-13,  33), S(-68,  21), S(-55,  35),
    S(-66,  18), S(-65,  36), S(-123,  48), S(-107,  56),
    S(-112,  53), S(-97,  43), S(-33,  22), S(-74,  15),
};

const int RookPSQT[N_SQUARES] = {
    S(-26,  -1), S(-21,   3), S(-14,   4), S(-6,  -4),
    S(-5,  -4), S(-10,   3), S(-13,  -2), S(-22, -14),
    S(-70,   5), S(-25, -10), S(-18,  -7), S(-11, -11),
    S(-9, -13), S(-15, -15), S(-15, -17), S(-77,   3),
    S(-39,   3), S(-16,  14), S(-25,   9), S(-14,   2),
    S(-12,   3), S(-25,   8), S(-4,   9), S(-39,   1),
    S(-32,  24), S(-21,  36), S(-21,  36), S(-5,  26),
    S(-8,  27), S(-19,  34), S(-13,  33), S(-30,  24),
    S(-22,  46), S(4,  38), S(16,  38), S(35,  30),
    S(33,  32), S(10,  36), S(17,  31), S(-14,  43),
    S(-33,  60), S(17,  41), S(0,  54), S(33,  36),
    S(29,  35), S(3,  52), S(33,  32), S(-26,  56),
    S(-18,  41), S(-24,  47), S(-1,  38), S(15,  38),
    S(14,  37), S(-2,  36), S(-24,  49), S(-12,  38),
    S(33,  55), S(24,  63), S(-1,  73), S(9,  66),
    S(10,  67), S(0,  69), S(34,  59), S(37,  56),
};

const int QueenPSQT[N_SQUARES] = {
    S(20, -34), S(4, -26), S(9, -34), S(17, -16),
    S(18, -18), S(14, -46), S(9, -28), S(22, -44),
    S(6, -15), S(15, -22), S(22, -42), S(13,   2),
    S(17,   0), S(22, -49), S(18, -29), S(3, -18),
    S(6,  -1), S(21,   7), S(5,  35), S(0,  34),
    S(2,  34), S(5,  37), S(24,   9), S(13, -15),
    S(9,  17), S(12,  46), S(-6,  59), S(-19, 109),
    S(-17, 106), S(-4,  57), S(18,  48), S(8,  33),
    S(-10,  42), S(-8,  79), S(-19,  66), S(-32, 121),
    S(-32, 127), S(-23,  80), S(-8,  95), S(-10,  68),
    S(-28,  56), S(-23,  50), S(-33,  66), S(-18,  70),
    S(-17,  71), S(-19,  63), S(-18,  65), S(-28,  76),
    S(-16,  61), S(-72, 108), S(-19,  65), S(-52, 114),
    S(-54, 120), S(-14,  59), S(-69, 116), S(-11,  73),
    S(8,  43), S(19,  47), S(0,  79), S(3,  78),
    S(-3,  89), S(13,  65), S(18,  79), S(21,  56),
};

const int KingPSQT[N_SQUARES] = {
    S(87, -77), S(67, -49), S(4,  -7), S(-9, -26),
    S(-10, -27), S(-8,  -1), S(57, -50), S(79, -82),
    S(35,   3), S(-27,  -3), S(-41,  16), S(-89,  29),
    S(-64,  26), S(-64,  28), S(-25,  -3), S(30,  -4),
    S(-44, -19), S(-16, -19), S(28,   7), S(0,  35),
    S(18,  32), S(31,   9), S(-13, -18), S(-36, -13),
    S(-48, -44), S(98, -39), S(71,  12), S(-22,  45),
    S(12,  41), S(79,  10), S(115, -34), S(-59, -38),
    S(-6, -10), S(95, -39), S(39,  14), S(-49,  18),
    S(-27,  19), S(35,  14), S(81, -34), S(-50, -13),
    S(24, -39), S(123, -22), S(105,  -1), S(-22, -21),
    S(-39, -20), S(74, -15), S(100, -23), S(-17, -49),
    S(0, -98), S(28, -21), S(7, -18), S(-3, -41),
    S(-57, -39), S(12, -26), S(22, -24), S(-15,-119),
    S(-16,-153), S(49, -94), S(-21, -73), S(-19, -32),
    S(-51, -55), S(-42, -62), S(53, -93), S(-58,-133),
};


/* Material Value Evaluation Terms */

const int PawnValue = S(82, 144);
const int KnightValue = S(426, 475);
const int BishopValue = S(441, 510);
const int RookValue = S(627, 803);
const int QueenValue = S(1292, 1623);
const int KingValue = S(0, 0);

#undef S


int PSQT[32][N_SQUARES];
void initPSQT()
{
    // Init a normalized 64-length PSQT for the evaluation which
    // combines the Piece Values with the original PSQT Values

    for (int sq = 0; sq < N_SQUARES; sq++) {

        const int sq1 = relativeSquare(WHITE, sq);
        const int sq2 = relativeSquare(BLACK, sq);

        PSQT[WHITE_PAWN][sq] = +PawnValue + PawnPSQT[sq1];
        PSQT[WHITE_KNIGHT][sq] = +KnightValue + KnightPSQT[sq1];
        PSQT[WHITE_BISHOP][sq] = +BishopValue + BishopPSQT[sq1];
        PSQT[WHITE_ROOK][sq] = +RookValue + RookPSQT[sq1];
        PSQT[WHITE_QUEEN][sq] = +QueenValue + QueenPSQT[sq1];
        PSQT[WHITE_KING][sq] = +KingValue + KingPSQT[sq1];

        PSQT[BLACK_PAWN][sq] = -PawnValue - PawnPSQT[sq2];
        PSQT[BLACK_KNIGHT][sq] = -KnightValue - KnightPSQT[sq2];
        PSQT[BLACK_BISHOP][sq] = -BishopValue - BishopPSQT[sq2];
        PSQT[BLACK_ROOK][sq] = -RookValue - RookPSQT[sq2];
        PSQT[BLACK_QUEEN][sq] = -QueenValue - QueenPSQT[sq2];
        PSQT[BLACK_KING][sq] = -KingValue - KingPSQT[sq2];
    }
}


/// zobrist.c

array<array<uint64_t, N_SQUARES>, 32> ZobristKeys;
array<uint64_t, N_FILES> ZobristEnpassKeys;
array<uint64_t, N_SQUARES> ZobristCastleKeys;
uint64_t ZobristTurnKey;

uint64_t rand64() 
{
    // http://vigna.di.unimi.it/ftp/papers/xorshift.pdf

    static uint64_t seed = 1070372ull;

    seed ^= seed >> 12;
    seed ^= seed << 25;
    seed ^= seed >> 27;

    return seed * 2685821657736338717ull;
}

void initZobrist() {

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

const char* PieceLabel[N_COLORS] = { "PNBRQK", "pnbrqk" };

int castleKingTo(int king, int rook) {
    return square(rankOf(king), (rook > king) ? 6 : 2);
}

int castleRookTo(int king, int rook) {
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
        *str++ = fileOf(sq) + 'a';
        *str++ = rankOf(sq) + '1';
    }

    *str++ = '\0';
}

void moveToString(uint16_t move, char* str, int chess960) {

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

struct Thread;

static const int HistoryDivisor = 16384;

void update_history_heuristics(Thread* thread, uint16_t* moves, int length, int depth);
void update_killer_moves(Thread* thread, uint16_t move);
void get_refutation_moves(Thread* thread, uint16_t* killer1, uint16_t* killer2, uint16_t* counter);

int  get_capture_history(Thread* thread, uint16_t move);
void get_capture_histories(Thread* thread, uint16_t* moves, int* scores, int start, int length);
void update_capture_histories(Thread* thread, uint16_t best, uint16_t* moves, int length, int depth);

int  get_quiet_history(Thread* thread, uint16_t move, int* cmhist, int* fmhist);
void get_quiet_histories(Thread* thread, uint16_t* moves, int* scores, int start, int length);
void update_quiet_histories(Thread* thread, uint16_t* moves, int length, int depth);

/// movepicker.h


enum { NORMAL_PICKER, NOISY_PICKER };

enum {
    STAGE_TABLE,
    STAGE_GENERATE_NOISY, STAGE_GOOD_NOISY,
    STAGE_KILLER_1, STAGE_KILLER_2, STAGE_COUNTER_MOVE,
    STAGE_GENERATE_QUIET, STAGE_QUIET,
    STAGE_BAD_NOISY,
    STAGE_DONE,
};

struct MovePicker {
    int split, noisy_size, quiet_size;
    int stage, type, threshold;
    int values[MAX_MOVES];
    uint16_t moves[MAX_MOVES];
    uint16_t tt_move, killer1, killer2, counter;
};

void     init_picker(MovePicker* mp, Thread* thread, uint16_t tt_move);
void     init_noisy_picker(MovePicker* mp, Thread* thread, uint16_t tt_move, int threshold);
uint16_t select_next(MovePicker* mp, Thread* thread, int skip_quiets);


/// timeman.h

/// limits from uci.h
struct Limits {
    double start, time, inc, mtg, timeLimit;
    int limitedByNone, limitedByTime, limitedBySelf;
    int limitedByDepth, limitedByMoves, limitedByNodes;
    int multiPV, depthLimit; uint64_t nodeLimit;
    uint16_t searchMoves[MAX_MOVES], excludedMoves[MAX_MOVES];
};



struct TimeManager {
    int pv_stability;
    double start_time, ideal_usage, max_usage;
    uint64_t nodes[0x10000];
};

double get_real_time();
double elapsed_time(const TimeManager* tm);
void tm_init(const Limits* limits, TimeManager* tm);
void tm_update(const Thread* thread, const Limits* limits, TimeManager* tm);
bool tm_finished(const Thread* thread, const TimeManager* tm);
bool tm_stop_early(const Thread* thread);


/// search.h

struct Board;

struct PVariation {
    int length, score;
    uint16_t line[MAX_PLY];
};

void initSearch();
void* start_search_threads(void* arguments);
void getBestMove(Thread* threads, Board* board, Limits* limits, uint16_t* best, uint16_t* ponder, int* score);
void* iterativeDeepening(void* vthread);
void aspirationWindow(Thread* thread);
int search(Thread* thread, PVariation* pv, int alpha, int beta, int depth, bool cutnode);
int qsearch(Thread* thread, PVariation* pv, int alpha, int beta);
int staticExchangeEvaluation(Board* board, uint16_t move, int threshold);
int singularity(Thread* thread, uint16_t ttMove, int ttValue, int depth, int PvNode, int alpha, int beta, bool cutnode);

static const int WindowDepth = 5;
static const int WindowSize = 10;
static const int WindowTimerMS = 2500;

static const int CurrmoveTimerMS = 2500;

static const int TTResearchMargin = 128;

static const int BetaPruningDepth = 8;
static const int BetaMargin = 75;

static const int AlphaPruningDepth = 5;
static const int AlphaMargin = 3000;

static const int NullMovePruningDepth = 2;

static const int ProbCutDepth = 5;
static const int ProbCutMargin = 100;

static const int FutilityPruningDepth = 8;
static const int FutilityMarginBase = 92;
static const int FutilityMarginPerDepth = 59;
static const int FutilityMarginNoHistory = 158;
static const int FutilityPruningHistoryLimit[] = { 12000, 6000 };

static const int ContinuationPruningDepth[] = { 3, 2 };
static const int ContinuationPruningHistoryLimit[] = { -1000, -2500 };

static const int LateMovePruningDepth = 8;

static const int SEEPruningDepth = 9;
static const int SEEQuietMargin = -64;
static const int SEENoisyMargin = -19;
static const int SEEPieceValues[] = {
     100,  450,  450,  675,
    1300,    0,    0,    0,
};

static const int QSSeeMargin = 110;
static const int QSDeltaMargin = 150;


/// board.h

struct Thread;

struct Board {
    uint8_t squares[N_SQUARES];
    uint64_t pieces[8], colours[3];
    uint64_t hash, pkhash, kingAttackers, threats;
    uint64_t castleRooks, castleMasks[N_SQUARES];
    int turn, epSquare, halfMoveCounter, fullMoveCounter;
    int psqtmat, numMoves, chess960;
    uint64_t history[8192];
    Thread* thread;
};

struct Undo {
    uint64_t hash, pkhash, kingAttackers, threats, castleRooks;
    int epSquare, halfMoveCounter, psqtmat, capturePiece;
};

void boardFromFEN(Board* board, const char* fen, int chess960);
void boardToFEN(Board* board, char* fen);
void printBoard(Board* board);
int boardHasNonPawnMaterial(Board* board, int turn);
int boardIsDrawn(Board* board, int height);
int boardDrawnByFiftyMoveRule(Board* board);
int boardDrawnByRepetition(Board* board, int height);
int boardDrawnByInsufficientMaterial(Board* board);

uint64_t perft(Board* board, int depth);


/// attacks.h

struct Magic {
    uint64_t magic;
    uint64_t mask;
    uint64_t shift;
    uint64_t* offset;
};

void initAttacks();

uint64_t pawnAttacks(int colour, int sq);
uint64_t knightAttacks(int sq);
uint64_t bishopAttacks(int sq, uint64_t occupied);
uint64_t rookAttacks(int sq, uint64_t occupied);
uint64_t queenAttacks(int sq, uint64_t occupied);
uint64_t kingAttacks(int sq);

uint64_t pawnLeftAttacks(uint64_t pawns, uint64_t targets, int colour);
uint64_t pawnRightAttacks(uint64_t pawns, uint64_t targets, int colour);
uint64_t pawnAttackSpan(uint64_t pawns, uint64_t targets, int colour);
uint64_t pawnAttackDouble(uint64_t pawns, uint64_t targets, int colour);
uint64_t pawnAdvance(uint64_t pawns, uint64_t occupied, int colour);
uint64_t pawnEnpassCaptures(uint64_t pawns, int epsq, int colour);

int squareIsAttacked(Board* board, int colour, int sq);
uint64_t attackersToSquare(Board* board, int colour, int sq);
uint64_t allAttackedSquares(Board* board, int colour);
uint64_t allAttackersToSquare(Board* board, uint64_t occupied, int sq);
uint64_t attackersToKingSquare(Board* board);

uint64_t discoveredAttacks(Board* board, int sq, int US);

static const uint64_t RookMagics[N_SQUARES] = {
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

static const uint64_t BishopMagics[N_SQUARES] = {
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

// Pyrrhic

extern int TB_LARGEST;   // Set by Pyrrhic in tb_init()
#include "pyrrhic/tbprobe.cpp"
using namespace std;    // only after pyrrhic



// these are from move.h

int apply(Thread* thread, Board* board, uint16_t move);
void applyLegal(Thread* thread, Board* board, uint16_t move);
void applyMove(Board* board, uint16_t move, Undo* undo);
void applyNormalMove(Board* board, uint16_t move, Undo* undo);
void applyCastleMove(Board* board, uint16_t move, Undo* undo);
void applyEnpassMove(Board* board, uint16_t move, Undo* undo);
void applyPromotionMove(Board* board, uint16_t move, Undo* undo);
void applyNullMove(Board* board, Undo* undo);

void revert(Thread* thread, Board* board, uint16_t move);
void revertMove(Board* board, uint16_t move, Undo* undo);
void revertNullMove(Board* board, Undo* undo);

int legalMoveCount(Board* board);
int moveExaminedByMultiPV(Thread* thread, uint16_t move);
int moveIsInRootMoves(Thread* thread, uint16_t move);
int moveIsTactical(Board* board, uint16_t move);
int moveEstimatedValue(Board* board, uint16_t move);
int moveBestCaseValue(Board* board);
int moveIsLegal(Board* board, uint16_t move);
int moveIsPseudoLegal(Board* board, uint16_t move);
int moveWasLegal(Board* board);


/// masks.h

void initMasks();

int distanceBetween(int sq1, int sq2);
int kingPawnFileDistance(uint64_t pawns, int ksq);
int openFileCount(uint64_t pawns);
uint64_t bitsBetweenMasks(int sq1, int sq2);
uint64_t kingAreaMasks(int colour, int sq);
uint64_t forwardRanksMasks(int colour, int rank);
uint64_t forwardFileMasks(int colour, int sq);
uint64_t adjacentFilesMasks(int file);
uint64_t passedPawnMasks(int colour, int sq);
uint64_t pawnConnectedMasks(int colour, int sq);
uint64_t outpostSquareMasks(int colour, int sq);
uint64_t outpostRanksMasks(int colour);


/// masks.c

int DistanceBetween[N_SQUARES][N_SQUARES];
int KingPawnFileDistance[N_FILES][1 << N_FILES];
uint64_t BitsBetweenMasks[N_SQUARES][N_SQUARES];
uint64_t KingAreaMasks[N_COLORS][N_SQUARES];
uint64_t ForwardRanksMasks[N_COLORS][N_RANKS];
uint64_t ForwardFileMasks[N_COLORS][N_SQUARES];
uint64_t AdjacentFilesMasks[N_FILES];
uint64_t PassedPawnMasks[N_COLORS][N_SQUARES];
uint64_t PawnConnectedMasks[N_COLORS][N_SQUARES];
uint64_t OutpostSquareMasks[N_COLORS][N_SQUARES];
uint64_t OutpostRanksMasks[N_COLORS];

void initMasks() {

    // Init a table for the distance between two given squares
    for (int sq1 = 0; sq1 < N_SQUARES; sq1++)
        for (int sq2 = 0; sq2 < N_SQUARES; sq2++)
            DistanceBetween[sq1][sq2] = Max(abs(fileOf(sq1) - fileOf(sq2)), abs(rankOf(sq1) - rankOf(sq2)));

    // Init a table to compute the distance between Pawns and Kings file-wise
    for (uint64_t mask = 0ull; mask <= 0xFF; mask++) {
        for (int file = 0; file < N_FILES; file++) {

            int ldist, rdist, dist;
            uint64_t left, right;

            // Look at only one side at a time by shifting off the other pawns
            left = (0xFFull & (mask << (N_FILES - file - 1))) >> (N_FILES - file - 1);
            right = (mask >> file) << file;

            // Find closest Pawn on each side. If no pawn, use "max" distance
            ldist = left ? file - getmsb(left) : N_FILES - 1;
            rdist = right ? getlsb(right) - file : N_FILES - 1;

            // Take the min distance, unless there are no pawns, then use 0
            dist = (left | right) ? Min(ldist, rdist) : 0;
            KingPawnFileDistance[file][mask] = dist;
        }
    }

    // Init a table of bitmasks for the squares between two given ones (aligned on diagonal)
    for (int sq1 = 0; sq1 < N_SQUARES; sq1++)
        for (int sq2 = 0; sq2 < N_SQUARES; sq2++)
            if (testBit(bishopAttacks(sq1, 0ull), sq2))
                BitsBetweenMasks[sq1][sq2] = bishopAttacks(sq1, 1ull << sq2)
                & bishopAttacks(sq2, 1ull << sq1);

    // Init a table of bitmasks for the squares between two given ones (aligned on a straight)
    for (int sq1 = 0; sq1 < N_SQUARES; sq1++)
        for (int sq2 = 0; sq2 < N_SQUARES; sq2++)
            if (testBit(rookAttacks(sq1, 0ull), sq2))
                BitsBetweenMasks[sq1][sq2] = rookAttacks(sq1, 1ull << sq2)
                & rookAttacks(sq2, 1ull << sq1);

    // Init a table for the King Areas. Use the King's square, the King's target
    // squares, and the squares within the pawn shield. When on the A/H files, extend
    // the King Area to include an additional file, namely the C and F file respectively
    for (int sq = 0; sq < N_SQUARES; sq++) {

        KingAreaMasks[WHITE][sq] = kingAttacks(sq) | (1ull << sq) | (kingAttacks(sq) << 8);
        KingAreaMasks[BLACK][sq] = kingAttacks(sq) | (1ull << sq) | (kingAttacks(sq) >> 8);

        KingAreaMasks[WHITE][sq] |= fileOf(sq) != 0 ? 0ull : KingAreaMasks[WHITE][sq] << 1;
        KingAreaMasks[BLACK][sq] |= fileOf(sq) != 0 ? 0ull : KingAreaMasks[BLACK][sq] << 1;

        KingAreaMasks[WHITE][sq] |= fileOf(sq) != 7 ? 0ull : KingAreaMasks[WHITE][sq] >> 1;
        KingAreaMasks[BLACK][sq] |= fileOf(sq) != 7 ? 0ull : KingAreaMasks[BLACK][sq] >> 1;
    }

    // Init a table of bitmasks for the ranks at or above a given rank, by colour
    for (int rank = 0; rank < N_RANKS; rank++) {
        for (int i = rank; i < N_RANKS; i++)
            ForwardRanksMasks[WHITE][rank] |= Ranks[i];
        ForwardRanksMasks[BLACK][rank] = ~ForwardRanksMasks[WHITE][rank] | Ranks[rank];
    }

    // Init a table of bitmasks for the squares on a file above a given square, by colour
    for (int sq = 0; sq < N_SQUARES; sq++) {
        ForwardFileMasks[WHITE][sq] = Files[fileOf(sq)] & ForwardRanksMasks[WHITE][rankOf(sq)];
        ForwardFileMasks[BLACK][sq] = Files[fileOf(sq)] & ForwardRanksMasks[BLACK][rankOf(sq)];
    }

    // Init a table of bitmasks containing the files next to a given file
    for (int file = 0; file < N_FILES; file++) {
        AdjacentFilesMasks[file] = Files[Max(0, file - 1)];
        AdjacentFilesMasks[file] |= Files[Min(N_FILES - 1, file + 1)];
        AdjacentFilesMasks[file] &= ~Files[file];
    }

    // Init a table of bitmasks to check if a given pawn has any opposition
    for (int colour = WHITE; colour <= BLACK; colour++)
        for (int sq = 0; sq < N_SQUARES; sq++)
            PassedPawnMasks[colour][sq] = ~forwardRanksMasks(!colour, rankOf(sq))
            & (adjacentFilesMasks(fileOf(sq)) | Files[fileOf(sq)]);

    // Init a table of bitmasks to check if a square is an outpost relative
    // to opposing pawns, such that no enemy pawn may attack the square with ease
    for (int colour = WHITE; colour <= BLACK; colour++)
        for (int sq = 0; sq < N_SQUARES; sq++)
            OutpostSquareMasks[colour][sq] = PassedPawnMasks[colour][sq] & ~Files[fileOf(sq)];

    // Init a pair of bitmasks to check if a square may be an outpost, by colour
    OutpostRanksMasks[WHITE] = RANK_4 | RANK_5 | RANK_6;
    OutpostRanksMasks[BLACK] = RANK_3 | RANK_4 | RANK_5;

    // Init a table of bitmasks to check for supports for a given pawn
    for (int sq = 8; sq < 56; sq++) {
        PawnConnectedMasks[WHITE][sq] = pawnAttacks(BLACK, sq) | pawnAttacks(BLACK, sq + 8);
        PawnConnectedMasks[BLACK][sq] = pawnAttacks(WHITE, sq) | pawnAttacks(WHITE, sq - 8);
    }
}

int distanceBetween(int s1, int s2) {
    assert(0 <= s1 && s1 < N_SQUARES);
    assert(0 <= s2 && s2 < N_SQUARES);
    return DistanceBetween[s1][s2];
}

int kingPawnFileDistance(uint64_t pawns, int ksq) {
    pawns |= pawns >> 8; pawns |= pawns >> 16; pawns |= pawns >> 32;
    assert(0 <= fileOf(ksq) && fileOf(ksq) < N_FILES);
    assert((pawns & 0xFF) < (1ull << N_FILES));
    return KingPawnFileDistance[fileOf(ksq)][pawns & 0xFF];
}

int openFileCount(uint64_t pawns) {
    pawns |= pawns >> 8; pawns |= pawns >> 16; pawns |= pawns >> 32;
    return popcount(~pawns & 0xFF);
}

uint64_t bitsBetweenMasks(int s1, int s2) {
    assert(0 <= s1 && s1 < N_SQUARES);
    assert(0 <= s2 && s2 < N_SQUARES);
    return BitsBetweenMasks[s1][s2];
}

uint64_t kingAreaMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return KingAreaMasks[colour][sq];
}

uint64_t forwardRanksMasks(int colour, int rank) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= rank && rank < N_RANKS);
    return ForwardRanksMasks[colour][rank];
}

uint64_t forwardFileMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return ForwardFileMasks[colour][sq];
}

uint64_t adjacentFilesMasks(int file) {
    assert(0 <= file && file < N_FILES);
    return AdjacentFilesMasks[file];
}

uint64_t passedPawnMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return PassedPawnMasks[colour][sq];
}

uint64_t pawnConnectedMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return PawnConnectedMasks[colour][sq];
}

uint64_t outpostSquareMasks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return OutpostSquareMasks[colour][sq];
}

uint64_t outpostRanksMasks(int colour) {
    assert(0 <= colour && colour < N_COLORS);
    return OutpostRanksMasks[colour];
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

void initPKNetwork();
int computePKNetwork(Board* board);


/// network.c


PKNetwork PKNN;

static array<string, 224> PKWeights = {
#include "weights/pknet_224x32x2.net"
    ""
};

static int computePKNetworkIndex(int colour, int piece, int sq) {
    return (64 + 48) * colour
        + (48 * (piece == KING))
        + sq - 8 * (piece == PAWN);
}


void initPKNetwork() {

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

int computePKNetwork(Board* board) {

    uint64_t pawns = board->pieces[PAWN];
    uint64_t kings = board->pieces[KING];
    uint64_t black = board->colours[BLACK];

    float layer1Neurons[PKNETWORK_LAYER1];
    float outputNeurons[PKNETWORK_OUTPUTS];

    // Layer 1: Compute the values in the hidden Neurons of Layer 1
    // by looping over the Kings and Pawns bitboards, and applying
    // the weight which corresponds to each piece. We break the Kings
    // into two nearly duplicate steps, in order to more efficiently
    // set and update the Layer 1 Neurons initially

    { // Do one King first so we can set the Neurons
        int sq = poplsb(&kings);
        int idx = computePKNetworkIndex(testBit(black, sq), KING, sq);
        for (int i = 0; i < PKNETWORK_LAYER1; i++)
            layer1Neurons[i] = PKNN.inputBiases[i] + PKNN.inputWeights[idx][i];
    }

    { // Do the remaining King as we would do normally
        int sq = poplsb(&kings);
        int idx = computePKNetworkIndex(testBit(black, sq), KING, sq);
        for (int i = 0; i < PKNETWORK_LAYER1; i++)
            layer1Neurons[i] += PKNN.inputWeights[idx][i];
    }

    while (pawns) {
        int sq = poplsb(&pawns);
        int idx = computePKNetworkIndex(testBit(black, sq), PAWN, sq);
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
    uint64_t occupancy[N_COLORS][N_COLORS][N_PIECES - 1];
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
    uint64_t hashMask;
    uint8_t generation;
};

void tt_update();
void tt_prefetch(uint64_t hash);

int tt_init(size_t nthreads, int megabytes);
int tt_hashfull();
bool tt_probe(uint64_t hash, int height, uint16_t* move, int* value, int* eval, int* depth, int* bound);
void tt_store(uint64_t hash, int height, uint16_t move, int value, int eval, int depth, int bound);

struct TTClear { size_t index, count; };
void tt_clear(size_t nthreads);
void* tt_clear_threaded(void* cargo);

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

struct PKEntry { uint64_t pkhash, passed; int eval, safetyw, safetyb; };
typedef PKEntry PKTable[PK_CACHE_SIZE];

PKEntry* getCachedPawnKingEval(Thread* thread, const Board* board);
void storeCachedPawnKingEval(Thread* thread, const Board* board, uint64_t passed, int eval, int safety[2]);


/// thread.h

struct NNUEEvaluator;

enum {
    STACK_OFFSET = 4,
    STACK_SIZE = MAX_PLY + STACK_OFFSET
};

struct NodeState {

    int eval;          // Static evaluation of the Node
    int movedPiece;    // Moving piece, otherwise UB
    int dextensions;   // Number of Double Extensions
    bool tactical;     // Cached moveIsTactical()
    uint16_t move;     // Move applied at the Node
    uint16_t excluded; // Excluded move during Singular Extensions
    MovePicker mp;     // Move Picker at each ply

    // Fast reference for future use for History lookups
    array<array<array<int16_t, N_SQUARES>, N_PIECES>, N_CONTINUATION>* continuations;
};

struct Thread
{
    Board board;
    Limits* limits;
    TimeManager* tm;
    PVariation pvs[MAX_PLY];
    PVariation mpvs[MAX_MOVES];

    int multiPV;
    uint16_t bestMoves[MAX_MOVES];

    uint64_t nodes, tbhits;
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
    jmp_buf jbuffer;
};


void populateThreadPool(vector<Thread>* threads);
void clearThreadPool(vector<Thread>* threads);

void resetThreadPool(Thread* threads);
void newSearchThreadPool(Thread* threads, Board* board, Limits* limits, TimeManager* tm);

uint64_t nodesSearchedThreadPool(Thread* threads);
uint64_t tbhitsThreadPool(Thread* threads);





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

INLINE void nnue_pop(Board* board) {
    if (USE_NNUE && board->thread != NULL)
        --board->thread->nnue->current;
}

INLINE void nnue_push(Board* board) {
    if (USE_NNUE && board->thread != NULL) {
        NNUEAccumulator* accum = ++board->thread->nnue->current;
        accum->accurate[WHITE] = accum->accurate[BLACK] = FALSE;
        accum->changes = 0;
    }
}

INLINE void nnue_move_piece(Board* board, int piece, int from, int to) {
    if (USE_NNUE && board->thread != NULL) {
        NNUEAccumulator* accum = board->thread->nnue->current;
        accum->deltas[accum->changes++] = NNUEDelta{ piece, from, to };
    }
}

INLINE void nnue_add_piece(Board* board, int piece, int sq) {
    nnue_move_piece(board, piece, N_SQUARES, sq);
}

INLINE void nnue_remove_piece(Board* board, int piece, int sq) {
    if (piece != EMPTY)
        nnue_move_piece(board, piece, sq, N_SQUARES);
}

int nnue_can_update(NNUEAccumulator* accum, Board* board, int colour);
void nnue_update_accumulator(NNUEAccumulator* accum, Board* board, int colour, int relksq);
void nnue_refresh_accumulator(NNUEEvaluator* nnue, NNUEAccumulator* accum, Board* board, int colour, int relksq);


/// nnue.accumulator.c


static int sq64_to_sq32(int sq) {
    static const int Mirror[] = { 3, 2, 1, 0, 0, 1, 2, 3 };
    return ((sq >> 1) & ~0x3) + Mirror[sq & 0x7];
}

static int nnue_index(int piece, int relksq, int colour, int sq) {

    const int ptype = pieceType(piece);
    const int pcolour = pieceColour(piece);
    const int relpsq = relativeSquare(colour, sq);

    const int mksq = testBit(LEFT_FLANK, relksq) ? (relksq ^ 0x7) : relksq;
    const int mpsq = testBit(LEFT_FLANK, relksq) ? (relpsq ^ 0x7) : relpsq;

    return 640 * sq64_to_sq32(mksq) + (64 * (5 * (colour == pcolour) + ptype)) + mpsq;
}

int nnue_can_update(NNUEAccumulator* accum, Board* board, int colour) {

    // Search back through the tree to find an accurate accum
    while (accum != board->thread->nnue->stack) {

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

void nnue_update_accumulator(NNUEAccumulator* accum, Board* board, int colour, int relksq) {

    int add = 0, remove = 0;
    int add_list[3], remove_list[3];
    vepi16* inputs, * outputs, * weights, registers[NUM_REGS];

    // Recurse and update all out of our date parents
    if (!(accum - 1)->accurate[colour])
        nnue_update_accumulator((accum - 1), board, colour, relksq);

    // Determine the features that have changed, by looping through them
    for (NNUEDelta* x = &accum->deltas[0]; x < &accum->deltas[0] + accum->changes; x++) {

        // HalfKP does not concern with KxK relations
        if (pieceType(x->piece) == KING)
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

void nnue_refresh_accumulator(NNUEEvaluator* nnue, NNUEAccumulator* accum, Board* board, int colour, int relsq) {

    vepi16* outputs, * weights, registers[NUM_REGS];
    const int ksq = getlsb(board->pieces[KING] & board->colours[colour]);
    NNUEAccumulatorTableEntry* entry = &nnue->table[ksq];

    int set_indexes[32], set_count = 0;
    int unset_indexes[32], unset_count = 0;

    for (int c = WHITE; c <= BLACK; c++) {

        for (int pt = PAWN; pt <= QUEEN; pt++) {

            uint64_t pieces = board->pieces[pt] & board->colours[c];
            uint64_t to_set = pieces & ~entry->occupancy[colour][c][pt];
            uint64_t to_unset = entry->occupancy[colour][c][pt] & ~pieces;

            while (to_set)
                set_indexes[set_count++] = nnue_index(makePiece(pt, c), relsq, colour, poplsb(&to_set));

            while (to_unset)
                unset_indexes[unset_count++] = nnue_index(makePiece(pt, c), relsq, colour, poplsb(&to_unset));

            entry->occupancy[colour][c][pt] = pieces;
        }
    }

    for (int offset = 0; offset < KPSIZE; offset += NUM_REGS * vepi16_cnt) {

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



/// movegen.h

ptrdiff_t genAllLegalMoves(Board* board, uint16_t* moves);
ptrdiff_t genAllNoisyMoves(Board* board, uint16_t* moves);
ptrdiff_t genAllQuietMoves(Board* board, uint16_t* moves);




/// move.c


static void updateCastleZobrist(Board* board, uint64_t oldRooks, uint64_t newRooks) {
    uint64_t diff = oldRooks ^ newRooks;
    while (diff)
        board->hash ^= ZobristCastleKeys[poplsb(&diff)];
}

void applyMove(Board* board, uint16_t move, Undo* undo) {

    static void (*table[4])(Board*, uint16_t, Undo*) = {
        applyNormalMove, applyCastleMove,
        applyEnpassMove, applyPromotionMove
    };

    // Save information which is hard to recompute
    undo->hash = board->hash;
    undo->pkhash = board->pkhash;
    undo->kingAttackers = board->kingAttackers;
    undo->threats = board->threats;
    undo->castleRooks = board->castleRooks;
    undo->epSquare = board->epSquare;
    undo->halfMoveCounter = board->halfMoveCounter;
    undo->psqtmat = board->psqtmat;

    // Store hash history for repetition checking
    board->history[board->numMoves++] = board->hash;
    board->fullMoveCounter++;

    // Update the hash for before changing the enpass square
    if (board->epSquare != -1)
        board->hash ^= ZobristEnpassKeys[fileOf(board->epSquare)];

    // Run the correct move application function
    table[MoveType(move) >> 12](board, move, undo);

    // No function updated epsquare so we reset
    if (board->epSquare == undo->epSquare)
        board->epSquare = -1;

    // No function updates this so we do it here
    board->turn = !board->turn;

    // Need king attackers for move generation
    board->kingAttackers = attackersToKingSquare(board);

    // Need squares attacked by the opposing player
    board->threats = allAttackedSquares(board, !board->turn);
}

void applyNormalMove(Board* board, uint16_t move, Undo* undo) {

    const int from = MoveFrom(move);
    const int to = MoveTo(move);

    const int fromPiece = board->squares[from];
    const int toPiece = board->squares[to];

    const int fromType = pieceType(fromPiece);
    const int toType = pieceType(toPiece);
    const int toColour = pieceColour(toPiece);

    if (fromType == PAWN || toPiece != EMPTY)
        board->halfMoveCounter = 0;
    else
        board->halfMoveCounter += 1;

    board->pieces[fromType] ^= (1ull << from) ^ (1ull << to);
    board->colours[board->turn] ^= (1ull << from) ^ (1ull << to);

    board->pieces[toType] ^= (1ull << to);
    board->colours[toColour] ^= (1ull << to);

    board->squares[from] = EMPTY;
    board->squares[to] = fromPiece;
    undo->capturePiece = toPiece;

    board->castleRooks &= board->castleMasks[from];
    board->castleRooks &= board->castleMasks[to];
    updateCastleZobrist(board, undo->castleRooks, board->castleRooks);

    board->psqtmat += PSQT[fromPiece][to]
        - PSQT[fromPiece][from]
        - PSQT[toPiece][to];

    board->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[toPiece][to]
        ^ ZobristTurnKey;

    if (fromType == PAWN || fromType == KING)
        board->pkhash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to];

    if (toType == PAWN)
        board->pkhash ^= ZobristKeys[toPiece][to];

    if (fromType == PAWN && (to ^ from) == 16) {

        uint64_t enemyPawns = board->pieces[PAWN]
            & board->colours[!board->turn]
            & adjacentFilesMasks(fileOf(from))
            & (board->turn == WHITE ? RANK_4 : RANK_5);
        if (enemyPawns) {
            board->epSquare = board->turn == WHITE ? from + 8 : from - 8;
            board->hash ^= ZobristEnpassKeys[fileOf(from)];
        }
    }

    nnue_push(board);
    nnue_move_piece(board, fromPiece, from, to);
    nnue_remove_piece(board, toPiece, to);
}

void applyCastleMove(Board* board, uint16_t move, Undo* undo) {

    const int from = MoveFrom(move);
    const int rFrom = MoveTo(move);

    const int to = castleKingTo(from, rFrom);
    const int rTo = castleRookTo(from, rFrom);

    const int fromPiece = makePiece(KING, board->turn);
    const int rFromPiece = makePiece(ROOK, board->turn);

    board->halfMoveCounter += 1;

    board->pieces[KING] ^= (1ull << from) ^ (1ull << to);
    board->colours[board->turn] ^= (1ull << from) ^ (1ull << to);

    board->pieces[ROOK] ^= (1ull << rFrom) ^ (1ull << rTo);
    board->colours[board->turn] ^= (1ull << rFrom) ^ (1ull << rTo);

    board->squares[from] = EMPTY;
    board->squares[rFrom] = EMPTY;

    board->squares[to] = fromPiece;
    board->squares[rTo] = rFromPiece;

    board->castleRooks &= board->castleMasks[from];
    updateCastleZobrist(board, undo->castleRooks, board->castleRooks);

    board->psqtmat += PSQT[fromPiece][to]
        - PSQT[fromPiece][from]
        + PSQT[rFromPiece][rTo]
        - PSQT[rFromPiece][rFrom];

    board->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[rFromPiece][rFrom]
        ^ ZobristKeys[rFromPiece][rTo]
        ^ ZobristTurnKey;

    board->pkhash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to];

    assert(pieceType(fromPiece) == KING);

    undo->capturePiece = EMPTY;

    nnue_push(board);
    if (from != to) nnue_move_piece(board, fromPiece, from, to);
    if (rFrom != rTo) nnue_move_piece(board, rFromPiece, rFrom, rTo);
}

void applyEnpassMove(Board* board, uint16_t move, Undo* undo) {

    const int from = MoveFrom(move);
    const int to = MoveTo(move);
    const int ep = to - 8 + (board->turn << 4);

    const int fromPiece = makePiece(PAWN, board->turn);
    const int enpassPiece = makePiece(PAWN, !board->turn);

    board->halfMoveCounter = 0;

    board->pieces[PAWN] ^= (1ull << from) ^ (1ull << to);
    board->colours[board->turn] ^= (1ull << from) ^ (1ull << to);

    board->pieces[PAWN] ^= (1ull << ep);
    board->colours[!board->turn] ^= (1ull << ep);

    board->squares[from] = EMPTY;
    board->squares[to] = fromPiece;
    board->squares[ep] = EMPTY;
    undo->capturePiece = enpassPiece;

    board->psqtmat += PSQT[fromPiece][to]
        - PSQT[fromPiece][from]
        - PSQT[enpassPiece][ep];

    board->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[enpassPiece][ep]
        ^ ZobristTurnKey;

    board->pkhash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[fromPiece][to]
        ^ ZobristKeys[enpassPiece][ep];

    assert(pieceType(fromPiece) == PAWN);
    assert(pieceType(enpassPiece) == PAWN);

    nnue_push(board);
    nnue_move_piece(board, fromPiece, from, to);
    nnue_remove_piece(board, enpassPiece, ep);
}

void applyPromotionMove(Board* board, uint16_t move, Undo* undo) {

    const int from = MoveFrom(move);
    const int to = MoveTo(move);

    const int fromPiece = board->squares[from];
    const int toPiece = board->squares[to];
    const int promoPiece = makePiece(MovePromoPiece(move), board->turn);

    const int toType = pieceType(toPiece);
    const int toColour = pieceColour(toPiece);
    const int promotype = MovePromoPiece(move);

    board->halfMoveCounter = 0;

    board->pieces[PAWN] ^= (1ull << from);
    board->pieces[promotype] ^= (1ull << to);
    board->colours[board->turn] ^= (1ull << from) ^ (1ull << to);

    board->pieces[toType] ^= (1ull << to);
    board->colours[toColour] ^= (1ull << to);

    board->squares[from] = EMPTY;
    board->squares[to] = promoPiece;
    undo->capturePiece = toPiece;

    board->castleRooks &= board->castleMasks[to];
    updateCastleZobrist(board, undo->castleRooks, board->castleRooks);

    board->psqtmat += PSQT[promoPiece][to]
        - PSQT[fromPiece][from]
        - PSQT[toPiece][to];

    board->hash ^= ZobristKeys[fromPiece][from]
        ^ ZobristKeys[promoPiece][to]
        ^ ZobristKeys[toPiece][to]
        ^ ZobristTurnKey;

    board->pkhash ^= ZobristKeys[fromPiece][from];

    assert(pieceType(fromPiece) == PAWN);
    assert(pieceType(toPiece) != PAWN);
    assert(pieceType(toPiece) != KING);

    nnue_push(board);
    nnue_remove_piece(board, fromPiece, from);
    nnue_remove_piece(board, toPiece, to);
    nnue_add_piece(board, promoPiece, to);
}

void applyNullMove(Board* board, Undo* undo) {

    // Save information which is hard to recompute
    undo->hash = board->hash;
    undo->threats = board->threats;
    undo->epSquare = board->epSquare;
    undo->halfMoveCounter = board->halfMoveCounter++;

    // NULL moves simply swap the turn only
    board->turn = !board->turn;
    board->history[board->numMoves++] = board->hash;
    board->fullMoveCounter++;

    // Update the hash for turn and changes to enpass square
    board->hash ^= ZobristTurnKey;
    if (board->epSquare != -1) {
        board->hash ^= ZobristEnpassKeys[fileOf(board->epSquare)];
        board->epSquare = -1;
    }

    board->threats = allAttackedSquares(board, !board->turn);
}


void revert(Thread* thread, Board* board, uint16_t move) {

    if (move == NULL_MOVE)
        revertNullMove(board, &thread->undoStack[--thread->height]);
    else
        revertMove(board, move, &thread->undoStack[--thread->height]);
}

void revertMove(Board* board, uint16_t move, Undo* undo) {

    const int to = MoveTo(move);
    const int from = MoveFrom(move);

    // Revert information which is hard to recompute
    board->hash = undo->hash;
    board->pkhash = undo->pkhash;
    board->kingAttackers = undo->kingAttackers;
    board->threats = undo->threats;
    board->castleRooks = undo->castleRooks;
    board->epSquare = undo->epSquare;
    board->halfMoveCounter = undo->halfMoveCounter;
    board->psqtmat = undo->psqtmat;

    // Swap turns and update the history index
    board->turn = !board->turn;
    board->numMoves--;
    board->fullMoveCounter--;

    // Update Accumulator pointer
    nnue_pop(board);

    if (MoveType(move) == NORMAL_MOVE) {

        const int fromType = pieceType(board->squares[to]);
        const int toType = pieceType(undo->capturePiece);
        const int toColour = pieceColour(undo->capturePiece);

        board->pieces[fromType] ^= (1ull << from) ^ (1ull << to);
        board->colours[board->turn] ^= (1ull << from) ^ (1ull << to);

        board->pieces[toType] ^= (1ull << to);
        board->colours[toColour] ^= (1ull << to);

        board->squares[from] = board->squares[to];
        board->squares[to] = undo->capturePiece;
    }

    else if (MoveType(move) == CASTLE_MOVE) {

        const int rFrom = to;
        const int rTo = castleRookTo(from, rFrom);
        const int _to = castleKingTo(from, rFrom);

        board->pieces[KING] ^= (1ull << from) ^ (1ull << _to);
        board->colours[board->turn] ^= (1ull << from) ^ (1ull << _to);

        board->pieces[ROOK] ^= (1ull << rFrom) ^ (1ull << rTo);
        board->colours[board->turn] ^= (1ull << rFrom) ^ (1ull << rTo);

        board->squares[_to] = EMPTY;
        board->squares[rTo] = EMPTY;

        board->squares[from] = makePiece(KING, board->turn);
        board->squares[rFrom] = makePiece(ROOK, board->turn);
    }

    else if (MoveType(move) == PROMOTION_MOVE) {

        const int toType = pieceType(undo->capturePiece);
        const int toColour = pieceColour(undo->capturePiece);
        const int promotype = MovePromoPiece(move);

        board->pieces[PAWN] ^= (1ull << from);
        board->pieces[promotype] ^= (1ull << to);
        board->colours[board->turn] ^= (1ull << from) ^ (1ull << to);

        board->pieces[toType] ^= (1ull << to);
        board->colours[toColour] ^= (1ull << to);

        board->squares[from] = makePiece(PAWN, board->turn);
        board->squares[to] = undo->capturePiece;
    }

    else { // (MoveType(move) == ENPASS_MOVE)

        assert(MoveType(move) == ENPASS_MOVE);

        const int ep = to - 8 + (board->turn << 4);

        board->pieces[PAWN] ^= (1ull << from) ^ (1ull << to);
        board->colours[board->turn] ^= (1ull << from) ^ (1ull << to);

        board->pieces[PAWN] ^= (1ull << ep);
        board->colours[!board->turn] ^= (1ull << ep);

        board->squares[from] = board->squares[to];
        board->squares[to] = EMPTY;
        board->squares[ep] = undo->capturePiece;
    }
}

void revertNullMove(Board* board, Undo* undo) {

    // Revert information which is hard to recompute
    board->hash = undo->hash;
    board->threats = undo->threats;
    board->epSquare = undo->epSquare;
    board->halfMoveCounter = undo->halfMoveCounter;

    // NULL moves simply swap the turn only
    board->turn = !board->turn;
    board->numMoves--;
    board->fullMoveCounter--;
}


int legalMoveCount(Board* board) {

    // Count of the legal number of moves for a given position

    uint16_t moves[MAX_MOVES];
    return static_cast<int>(genAllLegalMoves(board, moves));
}

int moveExaminedByMultiPV(Thread* thread, uint16_t move) {

    // Check to see if this move was already selected as the
    // best move in a previous iteration of this search depth

    for (int i = 0; i < thread->multiPV; i++)
        if (thread->bestMoves[i] == move)
            return 1;

    return 0;
}

int moveIsInRootMoves(Thread* thread, uint16_t move) {

    // We do two things: 1) Check to make sure we are not using a move which
    // has been flagged as excluded thanks to Syzygy probing. 2) Check to see
    // if we are doing a "go searchmoves <>"  command, in which case we have
    // to limit our search to the provided moves.

    for (int i = 0; i < MAX_MOVES; i++)
        if (move == thread->limits->excludedMoves[i])
            return 0;

    if (!thread->limits->limitedByMoves)
        return 1;

    for (int i = 0; i < MAX_MOVES; i++)
        if (move == thread->limits->searchMoves[i])
            return 1;

    return 0;
}

int moveIsTactical(Board* board, uint16_t move) {

    // We can use a simple bit trick since we assert that only
    // the enpass and promotion moves will ever have the 13th bit,
    // (ie 2 << 12) set. We use (2 << 12) in order to match move.h
    assert(ENPASS_MOVE & PROMOTION_MOVE & (2 << 12));
    assert(!((NORMAL_MOVE | CASTLE_MOVE) & (2 << 12)));

    // Check for captures, promotions, or enpassant. Castle moves may appear to be
    // tactical, since the King may move to its own square, or the rooks square
    return (board->squares[MoveTo(move)] != EMPTY && MoveType(move) != CASTLE_MOVE)
        || (move & ENPASS_MOVE & PROMOTION_MOVE);
}

int moveEstimatedValue(Board* board, uint16_t move) {

    // Start with the value of the piece on the target square
    int value = SEEPieceValues[pieceType(board->squares[MoveTo(move)])];

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

int moveBestCaseValue(Board* board) {

    // Assume the opponent has at least a pawn
    int value = SEEPieceValues[PAWN];

    // Check for a higher value target
    for (int piece = QUEEN; piece > PAWN; piece--)
        if (board->pieces[piece] & board->colours[!board->turn])
        {
            value = SEEPieceValues[piece]; break;
        }

    // Check for a potential pawn promotion
    if (board->pieces[PAWN]
        & board->colours[board->turn]
        & (board->turn == WHITE ? RANK_7 : RANK_2))
        value += SEEPieceValues[QUEEN] - SEEPieceValues[PAWN];

    return value;
}

int moveIsLegal(Board* board, uint16_t move) {

    int legal; Undo undo;

    if (!moveIsPseudoLegal(board, move))
        return 0;

    applyMove(board, move, &undo);
    legal = moveWasLegal(board);
    revertMove(board, move, &undo);

    return legal;
}

int moveIsPseudoLegal(Board* board, uint16_t move) {

    int from = MoveFrom(move);
    int type = MoveType(move);
    int ftype = pieceType(board->squares[from]);
    int rook, king, rookTo, kingTo;

    uint64_t friendly = board->colours[board->turn];
    uint64_t enemy = board->colours[!board->turn];
    uint64_t castles = friendly & board->castleRooks;
    uint64_t occupied = friendly | enemy;
    uint64_t attacks, forward, mask;

    // Quick check against obvious illegal moves, such as our special move values,
    // moving a piece that is not ours, normal move and enpass moves that have bits
    // set which would otherwise indicate that the move is a castle or a promotion
    if ((move == NONE_MOVE || move == NULL_MOVE)
        || (pieceColour(board->squares[from]) != board->turn)
        || (MovePromoType(move) != PROMOTE_TO_KNIGHT && type == NORMAL_MOVE)
        || (MovePromoType(move) != PROMOTE_TO_KNIGHT && type == ENPASS_MOVE))
        return 0;

    // Knight, Bishop, Rook, and Queen moves are legal so long as the
    // move type is NORMAL and the destination is an attacked square

    if (ftype == KNIGHT)
        return type == NORMAL_MOVE
        && testBit(knightAttacks(from) & ~friendly, MoveTo(move));

    if (ftype == BISHOP)
        return type == NORMAL_MOVE
        && testBit(bishopAttacks(from, occupied) & ~friendly, MoveTo(move));

    if (ftype == ROOK)
        return type == NORMAL_MOVE
        && testBit(rookAttacks(from, occupied) & ~friendly, MoveTo(move));

    if (ftype == QUEEN)
        return type == NORMAL_MOVE
        && testBit(queenAttacks(from, occupied) & ~friendly, MoveTo(move));

    if (ftype == PAWN) {

        // Throw out castle moves with our pawn
        if (type == CASTLE_MOVE)
            return 0;

        // Look at the squares which our pawn threatens
        attacks = pawnAttacks(board->turn, from);

        // Enpass moves are legal if our to square is the enpass
        // square and we could attack a piece on the enpass square
        if (type == ENPASS_MOVE)
            return MoveTo(move) == board->epSquare && testBit(attacks, MoveTo(move));

        // Compute simple pawn advances
        forward = pawnAdvance(1ull << from, occupied, board->turn);

        // Promotion moves are legal if we can move to one of the promotion
        // ranks, defined by PROMOTION_RANKS, independent of moving colour
        if (type == PROMOTION_MOVE)
            return testBit(PROMOTION_RANKS & ((attacks & enemy) | forward), MoveTo(move));

        // Add the double advance to forward
        forward |= pawnAdvance(forward & (!board->turn ? RANK_3 : RANK_6), occupied, board->turn);

        // Normal moves are legal if we can move there
        return testBit(~PROMOTION_RANKS & ((attacks & enemy) | forward), MoveTo(move));
    }

    // The colour check should (assuming board->squares only contains
    // pieces and EMPTY flags) ensure that ftype is an actual piece,
    // which at this point the only piece left to check is the King
    assert(ftype == KING);

    // Normal moves are legal if the to square is a valid target
    if (type == NORMAL_MOVE)
        return testBit(kingAttacks(from) & ~friendly, MoveTo(move));

    // Kings cannot enpass or promote
    if (type != CASTLE_MOVE)
        return 0;

    // Verifying a castle move can be difficult, so instead we will just
    // attempt to generate the (two) possible castle moves for the given
    // player. If one matches, we can then verify the pseudo legality
    // using the same code as from movegen.c

    while (castles && !board->kingAttackers) {

        // Figure out which pieces are moving to which squares
        rook = poplsb(&castles), king = from;
        rookTo = castleRookTo(king, rook);
        kingTo = castleKingTo(king, rook);

        // Make sure the move actually matches what we have
        if (move != MoveMake(king, rook, CASTLE_MOVE)) continue;

        // Castle is illegal if we would go over a piece
        mask = bitsBetweenMasks(king, kingTo) | (1ull << kingTo);
        mask |= bitsBetweenMasks(rook, rookTo) | (1ull << rookTo);
        mask &= ~((1ull << king) | (1ull << rook));
        if (occupied & mask) return 0;

        // Castle is illegal if we move through a checking threat
        mask = bitsBetweenMasks(king, kingTo);
        while (mask)
            if (squareIsAttacked(board, board->turn, poplsb(&mask)))
                return 0;

        return 1; // All requirments are met
    }

    return 0;
}

int moveWasLegal(Board* board) {

    // Grab the last player's King's square and verify safety
    int sq = getlsb(board->colours[!board->turn] & board->pieces[KING]);
    assert(board->squares[sq] == makePiece(KING, !board->turn));
    return !squareIsAttacked(board, !board->turn, sq);
}




/// more move.c

int apply(Thread* thread, Board* board, uint16_t move)
{
    NodeState* const ns = &thread->states[thread->height];

    // NULL moves are only tried when legal
    if (move == NULL_MOVE) {

        ns->movedPiece = EMPTY;
        ns->tactical = false;
        ns->continuations = NULL;
        ns->move = NULL_MOVE;

        // Prefetch the next tt-entry as soon as we have the Key
        applyNullMove(board, &thread->undoStack[thread->height]);
        tt_prefetch(board->hash);
    }

    else {

        ns->movedPiece = pieceType(board->squares[MoveFrom(move)]);
        ns->tactical = moveIsTactical(board, move);
        ns->continuations = &thread->continuation[ns->tactical][ns->movedPiece][MoveTo(move)];
        ns->move = move;

        // Prefetch the next tt-entry as soon as we have the Key
        applyMove(board, move, &thread->undoStack[thread->height]);
        tt_prefetch(board->hash);

        // Reject the move if it was illegal
        if (!moveWasLegal(board))
            return revertMove(board, move, &thread->undoStack[thread->height]), 0;
    }

    // Advance the Stack before updating
    thread->height++;

    return 1;
}

void applyLegal(Thread* thread, Board* board, uint16_t move)
{
    NodeState* const ns = &thread->states[thread->height];

    ns->movedPiece = pieceType(board->squares[MoveFrom(move)]);
    ns->tactical = moveIsTactical(board, move);
    ns->continuations = &thread->continuation[ns->tactical][ns->movedPiece][MoveTo(move)];
    ns->move = move;

    // Assumed that this move is legal
    applyMove(board, move, &thread->undoStack[thread->height]);
    assert(moveWasLegal(board));

    // Advance the Stack before updating
    thread->height++;
}




/// history.c

static int stat_bonus(int depth) {

    // Approximately verbatim stat bonus formula from Stockfish
    return depth > 13 ? 32 : 16 * depth * depth + 128 * Max(depth - 1, 0);
}

static void update_history(int16_t* current, int depth, bool good) {

    // HistoryDivisor is essentially the max value of history
    const int delta = good ? stat_bonus(depth) : -stat_bonus(depth);
    *current += delta - *current * abs(delta) / HistoryDivisor;
}


static int history_captured_piece(Thread* thread, uint16_t move) {

    // Handle Enpassant; Consider promotions as Pawn Captures
    return MoveType(move) != NORMAL_MOVE
        ? PAWN
        : pieceType(thread->board.squares[MoveTo(move)]);
}

static int16_t* underlying_capture_history(Thread* thread, uint16_t move) {

    const int captured = history_captured_piece(thread, move);
    const int piece = pieceType(thread->board.squares[MoveFrom(move)]);

    // Determine if piece evades and/or enters a threat
    const bool threat_from = testBit(thread->board.threats, MoveFrom(move));
    const bool threat_to = testBit(thread->board.threats, MoveTo(move));

    assert(PAWN <= captured && captured <= QUEEN);
    assert(PAWN <= piece && piece <= KING);

    return &thread->chistory[piece][threat_from][threat_to][MoveTo(move)][captured];
}

static void underlying_quiet_history(Thread* thread, uint16_t move, int16_t* histories[3]) {

    static int16_t NULL_HISTORY; // Always zero to handle missing CM/FM history

    NodeState* const ns = &thread->states[thread->height];
    const uint64_t threats = thread->board.threats;

    // Extract information from this move
    const int to = MoveTo(move);
    const int from = MoveFrom(move);
    const int piece = pieceType(thread->board.squares[from]);

    // Determine if piece evades and/or enters a threat
    const bool threat_from = testBit(threats, from);
    const bool threat_to = testBit(threats, to);

    // Set Counter Move History if it exists
    histories[0] = (ns - 1)->continuations == NULL
        ? &NULL_HISTORY : &(*(ns - 1)->continuations)[0][piece][to];

    // Set Followup Move History if it exists
    histories[1] = (ns - 2)->continuations == NULL
        ? &NULL_HISTORY : &(*(ns - 2)->continuations)[1][piece][to];

    // Set Butterfly History, which will always exist
    histories[2] = &thread->history[thread->board.turn][threat_from][threat_to][from][to];
}


void update_history_heuristics(Thread* thread, uint16_t* moves, int length, int depth) {

    NodeState* const prev = &thread->states[thread->height - 1];
    const int colour = thread->board.turn;

    update_killer_moves(thread, moves[length - 1]);

    if (prev->move != NONE_MOVE && prev->move != NULL_MOVE)
        thread->cmtable[!colour][prev->movedPiece][MoveTo(prev->move)] = moves[length - 1];

    update_quiet_histories(thread, moves, length, depth);
}

void update_killer_moves(Thread* thread, uint16_t move) {

    // Avoid saving the same Killer Move twice
    if (thread->killers[thread->height][0] != move) {
        thread->killers[thread->height][1] = thread->killers[thread->height][0];
        thread->killers[thread->height][0] = move;
    }
}

void get_refutation_moves(Thread* thread, uint16_t* killer1, uint16_t* killer2, uint16_t* counter) {

    // At each ply, we should have two potential Killer moves that have produced cutoffs
    // at the same ply in sibling nodes. Additionally, we may have a counter move, which
    // refutes the previously moved piece's destination square, somewhere in the search tree

    NodeState* const prev = &thread->states[thread->height - 1];

    *counter = (prev->move == NONE_MOVE || prev->move == NULL_MOVE) ? NONE_MOVE
        : thread->cmtable[!thread->board.turn][prev->movedPiece][MoveTo(prev->move)];

    *killer1 = thread->killers[thread->height][0];
    *killer2 = thread->killers[thread->height][1];
}


int get_capture_history(Thread* thread, uint16_t move) {

    // Inflate Queen Promotions beyond the range of reductions
    return  64000 * (MovePromoPiece(move) == QUEEN)
        + *underlying_capture_history(thread, move);
}

void get_capture_histories(Thread* thread, uint16_t* moves, int* scores, int start, int length) {

    // Grab histories for all of the capture moves. Since this is used for sorting,
    // we include an MVV-LVA factor to improve sorting. Additionally, we add 64k to
    // the history score to ensure it is >= 0 to differentiate good from bad later on

    static const int MVVAugment[] = { 0, 2400, 2400, 4800, 9600 };

    for (int i = start; i < start + length; i++)
        scores[i] = 64000 + get_capture_history(thread, moves[i])
        + MVVAugment[history_captured_piece(thread, moves[i])];
}

void update_capture_histories(Thread* thread, uint16_t best, uint16_t* moves, int length, int depth) {

    // Update the history for each capture move that was attempted. One of them
    // might have been the move which produced a cutoff, and thus earn a bonus

    for (int i = 0; i < length; i++) {
        int16_t* hist = underlying_capture_history(thread, moves[i]);
        update_history(hist, depth, moves[i] == best);
    }
}


int get_quiet_history(Thread* thread, uint16_t move, int* cmhist, int* fmhist) {

    int16_t* histories[3];
    underlying_quiet_history(thread, move, histories);

    *cmhist = *histories[0]; *fmhist = *histories[1];
    return *histories[0] + *histories[1] + *histories[2];
}

void get_quiet_histories(Thread* thread, uint16_t* moves, int* scores, int start, int length) {

    int null_hist; // cmhist & fmhist are set, although ignored

    for (int i = start; i < start + length; i++)
        scores[i] = get_quiet_history(thread, moves[i], &null_hist, &null_hist);
}

void update_quiet_histories(Thread* thread, uint16_t* moves, int length, int depth) {

    NodeState* const ns = &thread->states[thread->height];

    // We found a low-depth cutoff too easily
    if (!depth || (length == 1 && depth <= 3))
        return;

    for (int i = 0; i < length; i++) {

        int16_t* histories[3];
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


/// movepicker.c


static uint16_t pop_move(int* size, uint16_t* moves, int* values, int index) {
    uint16_t popped = moves[index];
    moves[index] = moves[--*size];
    values[index] = values[*size];
    return popped;
}

static int best_index(MovePicker* mp, int start, int end) {

    int best = start;

    for (int i = start + 1; i < end; i++)
        if (mp->values[i] > mp->values[best])
            best = i;

    return best;
}


void init_picker(MovePicker* mp, Thread* thread, uint16_t tt_move) {

    // Start with the tt-move
    mp->stage = STAGE_TABLE;
    mp->tt_move = tt_move;

    // Lookup our refutations (killers and counter moves)
    get_refutation_moves(thread, &mp->killer1, &mp->killer2, &mp->counter);

    // General housekeeping
    mp->threshold = 0;
    mp->type = NORMAL_PICKER;

    // Skip over the TT-move if it is illegal
    mp->stage += !moveIsPseudoLegal(&thread->board, tt_move);
}

void init_noisy_picker(MovePicker* mp, Thread* thread, uint16_t tt_move, int threshold) {

    // Start with the tt-move potentially
    mp->stage = STAGE_TABLE;
    mp->tt_move = tt_move;

    // Skip all of the refutation moves
    mp->killer1 = mp->killer2 = mp->counter = NONE_MOVE;

    // General housekeeping
    mp->threshold = threshold;
    mp->type = NOISY_PICKER;

    // Skip over the TT-move unless its a threshold-winning capture
    mp->stage += !moveIsTactical(&thread->board, tt_move)
        || !moveIsPseudoLegal(&thread->board, tt_move)
        || !staticExchangeEvaluation(&thread->board, tt_move, threshold);
}

uint16_t select_next(MovePicker* mp, Thread* thread, int skip_quiets) {

    int best;
    uint16_t best_move;
    Board* board = &thread->board;

    switch (mp->stage) {

    case STAGE_TABLE:

        // Play table move ( Already shown to be legal )
        mp->stage = STAGE_GENERATE_NOISY;
        return mp->tt_move;

    case STAGE_GENERATE_NOISY:

        // Generate and evaluate noisy moves. mp->split sets a break point
        // to seperate the noisy from the quiet moves, so that we can skip
        // some of the noisy moves during STAGE_GOOD_NOISY and return later
        mp->noisy_size = mp->split = static_cast<int>(genAllNoisyMoves(board, mp->moves));
        get_capture_histories(thread, mp->moves, mp->values, 0, mp->noisy_size);
        mp->stage = STAGE_GOOD_NOISY;

        /* fallthrough */

    case STAGE_GOOD_NOISY:

        // Check to see if there are still more noisy moves
        while (mp->noisy_size) {

            // Grab the next best move index
            best = best_index(mp, 0, mp->noisy_size);

            // Values below zero are flagged as failing an SEE (bad noisy)
            if (mp->values[best] < 0)
                break;

            // Skip moves which fail to beat our SEE margin. We flag those moves
            // as failed with the value (-1), and then repeat the selection process
            if (!staticExchangeEvaluation(board, mp->moves[best], mp->threshold)) {
                mp->values[best] = -1;
                continue;
            }

            // Reduce effective move list size
            best_move = pop_move(&mp->noisy_size, mp->moves, mp->values, best);

            // Don't play the table move twice
            if (best_move == mp->tt_move)
                continue;

            // Don't play the refutation moves twice
            if (best_move == mp->killer1) mp->killer1 = NONE_MOVE;
            if (best_move == mp->killer2) mp->killer2 = NONE_MOVE;
            if (best_move == mp->counter) mp->counter = NONE_MOVE;

            return best_move;
        }

        // Jump to bad noisy moves when skipping quiets
        if (skip_quiets) {
            mp->stage = STAGE_BAD_NOISY;
            return select_next(mp, thread, skip_quiets);
        }

        mp->stage = STAGE_KILLER_1;

        /* fallthrough */

    case STAGE_KILLER_1:

        // Play killer move if not yet played, and pseudo legal
        mp->stage = STAGE_KILLER_2;
        if (!skip_quiets
            && mp->killer1 != mp->tt_move
            && moveIsPseudoLegal(board, mp->killer1))
            return mp->killer1;

        /* fallthrough */

    case STAGE_KILLER_2:

        // Play killer move if not yet played, and pseudo legal
        mp->stage = STAGE_COUNTER_MOVE;
        if (!skip_quiets
            && mp->killer2 != mp->tt_move
            && moveIsPseudoLegal(board, mp->killer2))
            return mp->killer2;

        /* fallthrough */

    case STAGE_COUNTER_MOVE:

        // Play counter move if not yet played, and pseudo legal
        mp->stage = STAGE_GENERATE_QUIET;
        if (!skip_quiets
            && mp->counter != mp->tt_move
            && mp->counter != mp->killer1
            && mp->counter != mp->killer2
            && moveIsPseudoLegal(board, mp->counter))
            return mp->counter;

        /* fallthrough */

    case STAGE_GENERATE_QUIET:

        // Generate and evaluate all quiet moves when not skipping them
        if (!skip_quiets) {
            mp->quiet_size = static_cast<int>(genAllQuietMoves(board, mp->moves + mp->split));
            get_quiet_histories(thread, mp->moves, mp->values, mp->split, mp->quiet_size);
        }

        mp->stage = STAGE_QUIET;

        /* fallthrough */

    case STAGE_QUIET:

        // Check to see if there are still more quiet moves
        while (!skip_quiets && mp->quiet_size) {

            // Select next best quiet and reduce the effective move list size
            best = best_index(mp, mp->split, mp->split + mp->quiet_size) - mp->split;
            best_move = pop_move(&mp->quiet_size, mp->moves + mp->split, mp->values + mp->split, best);

            // Don't play a move more than once
            if (best_move == mp->tt_move || best_move == mp->killer1
                || best_move == mp->killer2 || best_move == mp->counter)
                continue;

            return best_move;
        }

        // Out of quiet moves, only bad quiets remain
        mp->stage = STAGE_BAD_NOISY;

        /* fallthrough */

    case STAGE_BAD_NOISY:

        // Check to see if there are still more noisy moves
        while (mp->noisy_size && mp->type != NOISY_PICKER) {

            // Reduce effective move list size
            best_move = pop_move(&mp->noisy_size, mp->moves, mp->values, 0);

            // Don't play a move more than once
            if (best_move == mp->tt_move || best_move == mp->killer1
                || best_move == mp->killer2 || best_move == mp->counter)
                continue;

            return best_move;
        }

        mp->stage = STAGE_DONE;

        /* fallthrough */

    case STAGE_DONE:
        return NONE_MOVE;

    default:
        return NONE_MOVE;
    }
}




/// board.c



static void clearBoard(Board* board) 
{
    // Wipe the entire board structure, and also set all of
    // the pieces on the board to be EMPTY. Ideally, before
    // this board is used again we will call boardFromFEN()

    memset(board, 0, sizeof(Board));
    memset(&board->squares, EMPTY, sizeof(board->squares));
}

static void setSquare(Board* board, int colour, int piece, int sq) {

    // Generate a piece on the given square. This serves as an aid
    // to setting up the board from a FEN. We make sure update any
    // related hash values, as well as the PSQT + material values

    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= piece && piece < N_PIECES);
    assert(0 <= sq && sq < N_SQUARES);

    board->squares[sq] = makePiece(piece, colour);
    setBit(&board->colours[colour], sq);
    setBit(&board->pieces[piece], sq);

    board->psqtmat += PSQT[board->squares[sq]][sq];
    board->hash ^= ZobristKeys[board->squares[sq]][sq];
    if (piece == PAWN || piece == KING)
        board->pkhash ^= ZobristKeys[board->squares[sq]][sq];
}

static int stringToSquare(char* str) {

    // Helper for reading the enpass square from a FEN. If no square
    // is provided, Ethereal will use -1 to represent this internally

    return str[0] == '-' ? -1 : square(str[1] - '1', str[0] - 'a');
}

void boardToFEN(Board* board, char* fen) 
{
    int sq;
    char str[3];
    uint64_t castles;

    // Piece placement
    for (int r = N_RANKS - 1; r >= 0; r--) {
        int cnt = 0;

        for (int f = 0; f < N_FILES; f++) {
            const int s = square(r, f);
            const int p = board->squares[s];

            if (p != EMPTY) {
                if (cnt)
                    *fen++ = cnt + '0';

                *fen++ = PieceLabel[pieceColour(p)][pieceType(p)];
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
    *fen++ = board->turn == WHITE ? 'w' : 'b';
    *fen++ = ' ';

    // Castle rights for White
    castles = board->colours[WHITE] & board->castleRooks;
    while (castles) {
        sq = popmsb(&castles);
        if (board->chess960) *fen++ = 'A' + fileOf(sq);
        else if (testBit(FILE_H, sq)) *fen++ = 'K';
        else if (testBit(FILE_A, sq)) *fen++ = 'Q';
    }

    // Castle rights for Black
    castles = board->colours[BLACK] & board->castleRooks;
    while (castles) {
        sq = popmsb(&castles);
        if (board->chess960) *fen++ = 'a' + fileOf(sq);
        else if (testBit(FILE_H, sq)) *fen++ = 'k';
        else if (testBit(FILE_A, sq)) *fen++ = 'q';
    }

    // Check for empty Castle rights
    if (!board->castleRooks)
        *fen++ = '-';

    // En passant square, Half Move Counter, and Full Move Counter
    squareToString(board->epSquare, str);
    printf(fen, " %s %d %d", str, board->halfMoveCounter, board->fullMoveCounter);
}

void printBoard(Board* board) {

    char fen[256];

    // Print each row of the board, starting from the top
    for (int sq = square(N_RANKS - 1, 0); sq >= 0; sq -= N_FILES) {

        printf("\n     |----|----|----|----|----|----|----|----|\n");
        printf("   %d ", 1 + sq / 8);

        // Print each square in a row, starting from the left
        for (int i = 0; i < 8; i++) {

            int colour = pieceColour(board->squares[sq + i]);
            int type = pieceType(board->squares[sq + i]);

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
    boardToFEN(board, fen);
    printf("\n%s\n\n", fen);
}

int boardHasNonPawnMaterial(Board* board, int turn) {
    uint64_t friendly = board->colours[turn];
    uint64_t kings = board->pieces[KING];
    uint64_t pawns = board->pieces[PAWN];
    return (friendly & (kings | pawns)) != friendly;
}

int boardIsDrawn(Board* board, int height) {

    // Drawn if any of the three possible cases
    return boardDrawnByFiftyMoveRule(board)
        || boardDrawnByRepetition(board, height)
        || boardDrawnByInsufficientMaterial(board);
}

int boardDrawnByFiftyMoveRule(Board* board) {

    // Fifty move rule triggered. BUG: We do not account for the case
    // when the fifty move rule occurs as checkmate is delivered, which
    // should not be considered a drawn position, but a checkmated one.
    return board->halfMoveCounter > 99;
}

int boardDrawnByRepetition(Board* board, int height) {

    int reps = 0;

    // Look through hash histories for our moves
    for (int i = board->numMoves - 2; i >= 0; i -= 2) {

        // No draw can occur before a zeroing move
        if (i < board->numMoves - board->halfMoveCounter)
            break;

        // Check for matching hash with a two fold after the root,
        // or a three fold which occurs in part before the root move
        if (board->history[i] == board->hash
            && (i > board->numMoves - height || ++reps == 2))
            return 1;
    }

    return 0;
}

int boardDrawnByInsufficientMaterial(Board* board) {

    // Check for KvK, KvN, KvB, and KvNN.

    return !(board->pieces[PAWN] | board->pieces[ROOK] | board->pieces[QUEEN])
        && (!several(board->colours[WHITE]) || !several(board->colours[BLACK]))
        && (!several(board->pieces[KNIGHT] | board->pieces[BISHOP])
            || (!board->pieces[BISHOP] && popcount(board->pieces[KNIGHT]) <= 2));
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


void tm_init(const Limits* limits, TimeManager* tm) {

    tm->pv_stability = 0; // Clear our stability time usage heuristic
    tm->start_time = limits->start; // Save off the start time of the search
    memset(tm->nodes, 0, sizeof(uint16_t) * 0x10000); // Clear Node counters

    // Allocate time if Ethereal is handling the clock
    if (limits->limitedBySelf) {

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
    const uint64_t best_nodes = tm->nodes[thread->pvs[thread->completed - 0].line[0]];
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

struct UCIGoStruct {
    Thread* threads;
    Board* board;
    Limits  limits;
};

thread* uciGo(UCIGoStruct* ucigo, Thread* threads, Board* board, int multiPV, char* str);
void uciSetOption(char* str, vector<Thread>* threads, int* multiPV, int* chess960);
void uciPosition(char* str, Board* board, int chess960);

void uciReport(Thread* threads, PVariation* pv, int alpha, int beta);
void uciReportCurrentMove(Board* board, uint16_t move, int currmove, int depth);

int strEquals(const char* str1, const char* str2);
int strStartsWith(const char* str, const char* key);
int strContains(const char* str, const char* key);
int getInput(char* str);

/// syzygy.h

void tablebasesProbeDTZ(Board* board, Limits* limits);
unsigned tablebasesProbeWDL(Board* board, int depth, int height);


/// syzygy.c

unsigned TB_PROBE_DEPTH; // Set by UCI options

static uint16_t convertPyrrhicMove(Board* board, unsigned result) {

    // Extract Pyrhic's move representation
    unsigned to = TB_GET_TO(result);
    unsigned from = TB_GET_FROM(result);
    unsigned ep = TB_GET_EP(result);
    unsigned promo = TB_GET_PROMOTES(result);

    // Convert the move notation. Care that Pyrrhic's promotion flags are inverted
    if (ep == 0u && promo == 0u) return MoveMake(from, to, NORMAL_MOVE);
    else if (ep != 0u)           return MoveMake(from, board->epSquare, ENPASS_MOVE);
    else /* if (promo != 0u) */  return MoveMake(from, to, PROMOTION_MOVE | ((4 - promo) << 14));
}

static void removeBadWDL(Board* board, Limits* limits, unsigned result, unsigned* results) {

    // Remove for any moves that fail to maintain the ideal WDL outcome
    for (int i = 0; i < MAX_MOVES && results[i] != TB_RESULT_FAILED; i++)
        if (TB_GET_WDL(results[i]) != TB_GET_WDL(result))
            limits->excludedMoves[i] = convertPyrrhicMove(board, results[i]);
}


void tablebasesProbeDTZ(Board* board, Limits* limits) 
{
    unsigned results[MAX_MOVES];
    uint64_t white = board->colours[WHITE];
    uint64_t black = board->colours[BLACK];

    // We cannot probe when there are castling rights, or when
    // we have more pieces than our largest Tablebase has pieces
    if (board->castleRooks
        || popcount(white | black) > TB_LARGEST)
        return;

    // Tap into Pyrrhic's API. Pyrrhic takes the board representation and the
    // fifty move rule counter, followed by the enpass square (0 if none set),
    // and the turn Pyrrhic defines WHITE as 1, and BLACK as 0, which is the
    // opposite of how Ethereal defines them

    unsigned result = tb_probe_root(
        board->colours[WHITE], board->colours[BLACK],
        board->pieces[KING], board->pieces[QUEEN],
        board->pieces[ROOK], board->pieces[BISHOP],
        board->pieces[KNIGHT], board->pieces[PAWN],
        board->halfMoveCounter, board->epSquare == -1 ? 0 : board->epSquare,
        board->turn == WHITE ? 1 : 0, results
    );

    // Probe failed, or we are already in a finished position.
    if (result == TB_RESULT_FAILED
        || result == TB_RESULT_CHECKMATE
        || result == TB_RESULT_STALEMATE)
        return;

    // Remove any moves that fail to maintain optimal WDL
    removeBadWDL(board, limits, result, results);
}

unsigned tablebasesProbeWDL(Board* board, int depth, int height) {

    uint64_t white = board->colours[WHITE];
    uint64_t black = board->colours[BLACK];

    // Never take a Syzygy Probe in a Root node, in a node with Castling rights,
    // in a node which was not just zero'ed by a Pawn Move or Capture, or in a
    // node which has more pieces than our largest found Tablebase can handle

    if (height == 0
        || board->castleRooks
        || board->halfMoveCounter
        || popcount(white | black) > TB_LARGEST)
        return TB_RESULT_FAILED;


    // We also will avoid probing beneath the provided TB_PROBE_DEPTH, except
    // for when our board has even fewer pieces than the largest Tablebase is
    // able to handle. Namely, when we have a 7man Tablebase, we will always
    // probe the 6man Tablebase if possible, irregardless of TB_PROBE_DEPTH

    if (depth < (int)TB_PROBE_DEPTH
        && popcount(white | black) == TB_LARGEST)
        return TB_RESULT_FAILED;


    // Tap into Pyrrhic's API. Pyrrhic takes the board representation, followed
    // by the enpass square (0 if none set), and the turn. Pyrrhic defines WHITE
    // as 1, and BLACK as 0, which is the opposite of how Ethereal defines them

    return tb_probe_wdl(
        board->colours[WHITE], board->colours[BLACK],
        board->pieces[KING], board->pieces[QUEEN],
        board->pieces[ROOK], board->pieces[BISHOP],
        board->pieces[KNIGHT], board->pieces[PAWN],
        board->epSquare == -1 ? 0 : board->epSquare,
        board->turn == WHITE ? 1 : 0
    );
}


/// evaluate.h


#ifdef TUNE
#define TRACE (1)
#else
#define TRACE (0)
#endif

enum {
    SCALE_DRAW = 0,
    SCALE_OCB_BISHOPS_ONLY = 64,
    SCALE_OCB_ONE_KNIGHT = 106,
    SCALE_OCB_ONE_ROOK = 96,
    SCALE_LONE_QUEEN = 88,
    SCALE_NORMAL = 128,
    SCALE_LARGE_PAWN_ADV = 144,
};

struct EvalTrace {
    int PawnValue[N_COLORS];
    int KnightValue[N_COLORS];
    int BishopValue[N_COLORS];
    int RookValue[N_COLORS];
    int QueenValue[N_COLORS];
    int KingValue[N_COLORS];
    int PawnPSQT[N_SQUARES][N_COLORS];
    int KnightPSQT[N_SQUARES][N_COLORS];
    int BishopPSQT[N_SQUARES][N_COLORS];
    int RookPSQT[N_SQUARES][N_COLORS];
    int QueenPSQT[N_SQUARES][N_COLORS];
    int KingPSQT[N_SQUARES][N_COLORS];
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
    int eval, complexity, factor, safety[N_COLORS];
};

struct EvalInfo {
    uint64_t pawnAttacks[N_COLORS];
    uint64_t pawnAttacksBy2[N_COLORS];
    uint64_t rammedPawns[N_COLORS];
    uint64_t blockedPawns[N_COLORS];
    uint64_t kingAreas[N_COLORS];
    uint64_t mobilityAreas[N_COLORS];
    uint64_t attacked[N_COLORS];
    uint64_t attackedBy2[N_COLORS];
    uint64_t attackedBy[N_COLORS][N_PIECES];
    uint64_t occupiedMinusBishops[N_COLORS];
    uint64_t occupiedMinusRooks[N_COLORS];
    uint64_t passedPawns;
    int kingSquare[N_COLORS];
    int kingAttacksCount[N_COLORS];
    int kingAttackersCount[N_COLORS];
    int kingAttackersWeight[N_COLORS];
    int pkeval[N_COLORS];
    int pksafety[N_COLORS];
    PKEntry* pkentry;
};

int evaluateBoard(Thread* thread, Board* board);
int evaluatePieces(EvalInfo* ei, Board* board);
int evaluatePawns(EvalInfo* ei, Board* board, int colour);
int evaluateKnights(EvalInfo* ei, Board* board, int colour);
int evaluateBishops(EvalInfo* ei, Board* board, int colour);
int evaluateRooks(EvalInfo* ei, Board* board, int colour);
int evaluateQueens(EvalInfo* ei, Board* board, int colour);
int evaluateKingsPawns(EvalInfo* ei, Board* board, int colour);
int evaluateKings(EvalInfo* ei, Board* board, int colour);
int evaluatePassed(EvalInfo* ei, Board* board, int colour);
int evaluateThreats(EvalInfo* ei, Board* board, int colour);
int evaluateSpace(EvalInfo* ei, Board* board, int colour);
int evaluateClosedness(EvalInfo* ei, Board* board);
int evaluateComplexity(EvalInfo* ei, Board* board, int eval);
int evaluateScaleFactor(Board* board, int eval);
void initPSQTInfo(Thread* thread, Board* board, EvalInfo* ei);

#define MakeScore(mg, eg) ((int)((unsigned int)(eg) << 16) + (mg))
#define ScoreMG(s) ((int16_t)((uint16_t)((unsigned)((s)))))
#define ScoreEG(s) ((int16_t)((uint16_t)((unsigned)((s) + 0x8000) >> 16)))

extern const int Tempo;

/// nnue/nnue.h

#if USE_NNUE

void nnue_init(const char* fname);
void nnue_incbin_init();
int nnue_evaluate(Thread* thread, Board* board);

#else

INLINE void nnue_init(const char* fname) {
    (void)fname; printf("info string Error: NNUE is disabled for this binary\n");
}

INLINE void nnue_incbin_init() {
    (void)0;
};

INLINE int nnue_evaluate(Thread* thread, Board* board) {
    (void)thread; (void)board; return 0;
}

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

static void scale_weights() 
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

static void shuffle_input_layer() 
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

static void abort_nnue(const char* reason) {
    printf("info string %s\n", reason);
    fflush(stdout); exit(EXIT_FAILURE);
}


INLINE void maddubs_x4(vepi32* acc, const vepi8* inp, const vepi8* wgt, int i, int j, int k) 
{
    static const int InChunks = L1SIZE / vepi8_cnt;

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

int nnue_evaluate(Thread* thread, Board* board) {

    int mg_eval, eg_eval;
    const uint64_t white = board->colours[WHITE];
    const uint64_t black = board->colours[BLACK];
    const uint64_t kings = board->pieces[KING];

    if (!NNUE_LOADED)
        abort_nnue("NNUE File was not provided");

    // For optimizations, auto-flag KvK as drawn
    if (kings == (white | black)) return 0;

    // Optimized computation of various input indices
    int wrelksq = relativeSquare(WHITE, getlsb(white & kings));
    int brelksq = relativeSquare(BLACK, getlsb(black & kings));

    NNUEAccumulator* accum = thread->nnue->current;

    ALIGN64 uint8_t out8[L1SIZE];
    ALIGN64 float   outN1[L1SIZE];
    ALIGN64 float   outN2[L1SIZE];

    if (!accum->accurate[WHITE]) {

        // Possible to recurse and incrementally update each
        if (nnue_can_update(accum, board, WHITE))
            nnue_update_accumulator(accum, board, WHITE, wrelksq);

        // History is missing, we must refresh completely
        else
            nnue_refresh_accumulator(thread->nnue, accum, board, WHITE, wrelksq);
    }

    if (!accum->accurate[BLACK]) {

        // Possible to recurse and incrementally update each
        if (nnue_can_update(accum, board, BLACK))
            nnue_update_accumulator(accum, board, BLACK, brelksq);

        // History is missing, we must refresh completely
        else
            nnue_refresh_accumulator(thread->nnue, accum, board, BLACK, brelksq);
    }

    // Feed-forward the entire evaluation function
    halfkp_relu(accum, out8, board->turn);
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


EvalTrace T, EmptyTrace;

#define S(mg, eg) (MakeScore((mg), (eg)))

/* Pawn Evaluation Terms */

const int PawnCandidatePasser[2][N_RANKS] = {
   {S(0,   0), S(-11, -18), S(-16,  18), S(-18,  29),
    S(-22,  61), S(21,  59), S(0,   0), S(0,   0)},
   {S(0,   0), S(-12,  21), S(-7,  27), S(2,  53),
    S(22, 116), S(49,  78), S(0,   0), S(0,   0)},
};

const int PawnIsolated[N_FILES] = {
    S(-13, -12), S(-1, -16), S(1, -16), S(3, -18),
    S(7, -19), S(3, -15), S(-4, -14), S(-4, -17),
};

const int PawnStacked[2][N_FILES] = {
   {S(10, -29), S(-2, -26), S(0, -23), S(0, -20),
    S(3, -20), S(5, -26), S(4, -30), S(8, -31)},
   {S(3, -14), S(0, -15), S(-6,  -9), S(-7, -10),
    S(-4,  -9), S(-2, -10), S(0, -13), S(0, -17)},
};

const int PawnBackwards[2][N_RANKS] = {
   {S(0,   0), S(0,  -7), S(7,  -7), S(6, -18),
    S(-4, -29), S(0,   0), S(0,   0), S(0,   0)},
   {S(0,   0), S(-9, -32), S(-5, -30), S(3, -31),
    S(29, -41), S(0,   0), S(0,   0), S(0,   0)},
};

const int PawnConnected32[32] = {
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

const int KnightOutpost[2][2] = {
   {S(12, -32), S(40,   0)},
   {S(7, -24), S(21,  -3)},
};

const int KnightBehindPawn = S(3, 28);

const int KnightInSiberia[4] = {
    S(-9,  -6), S(-12, -20), S(-27, -20), S(-47, -19),
};

const int KnightMobility[9] = {
    S(-104,-139), S(-45,-114), S(-22, -37), S(-8,   3),
    S(6,  15), S(11,  34), S(19,  38), S(30,  37),
    S(43,  17),
};

/* Bishop Evaluation Terms */

const int BishopPair = S(22, 88);

const int BishopRammedPawns = S(-8, -17);

const int BishopOutpost[2][2] = {
   {S(16, -16), S(50,  -3)},
   {S(9,  -9), S(-4,  -4)},
};

const int BishopBehindPawn = S(4, 24);

const int BishopLongDiagonal = S(26, 20);

const int BishopMobility[14] = {
    S(-99,-186), S(-46,-124), S(-16, -54), S(-4, -14),
    S(6,   1), S(14,  20), S(17,  35), S(19,  39),
    S(19,  49), S(27,  48), S(26,  48), S(52,  32),
    S(55,  47), S(83,   2),
};

/* Rook Evaluation Terms */

const int RookFile[2] = { S(10,   9), S(34,   8) };

const int RookOnSeventh = S(-1, 42);

const int RookMobility[15] = {
    S(-127,-148), S(-56,-127), S(-25, -85), S(-12, -28),
    S(-10,   2), S(-12,  27), S(-11,  42), S(-4,  46),
    S(4,  52), S(9,  55), S(11,  64), S(19,  68),
    S(19,  73), S(37,  60), S(97,  15),
};

/* Queen Evaluation Terms */

const int QueenRelativePin = S(-22, -13);

const int QueenMobility[28] = {
    S(-111,-273), S(-253,-401), S(-127,-228), S(-46,-236),
    S(-20,-173), S(-9, -86), S(-1, -35), S(2,  -1),
    S(8,   8), S(10,  31), S(15,  37), S(17,  55),
    S(20,  46), S(23,  57), S(22,  58), S(21,  64),
    S(24,  62), S(16,  65), S(13,  63), S(18,  48),
    S(25,  30), S(38,   8), S(34, -12), S(28, -29),
    S(10, -44), S(7, -79), S(-42, -30), S(-23, -50),
};

/* King Evaluation Terms */

const int KingDefenders[12] = {
    S(-37,  -3), S(-17,   2), S(0,   6), S(11,   8),
    S(21,   8), S(32,   0), S(38, -14), S(10,  -5),
    S(12,   6), S(12,   6), S(12,   6), S(12,   6),
};

const int KingPawnFileProximity[N_FILES] = {
    S(36,  46), S(22,  31), S(13,  15), S(-8, -22),
    S(-5, -62), S(-3, -75), S(-15, -81), S(-12, -75),
};

const int KingShelter[2][N_FILES][N_RANKS] = {
  {{S(-5,  -5), S(17, -31), S(26,  -3), S(24,   8),
    S(4,   1), S(-12,   4), S(-16, -33), S(-59,  24)},
   {S(11,  -6), S(3, -15), S(-5,  -2), S(5,  -4),
    S(-11,   7), S(-53,  70), S(81,  82), S(-19,   1)},
   {S(38,  -3), S(5,  -6), S(-34,   5), S(-17, -15),
    S(-9,  -5), S(-26,  12), S(11,  73), S(-16,  -1)},
   {S(18,  11), S(25, -18), S(0, -14), S(10, -21),
    S(22, -34), S(-48,   9), S(-140,  49), S(-5,  -5)},
   {S(-11,  15), S(1,  -3), S(-44,   6), S(-28,  10),
    S(-24,  -2), S(-35,  -5), S(40, -24), S(-13,   3)},
   {S(51, -14), S(15, -14), S(-24,   5), S(-10, -20),
    S(10, -34), S(34, -20), S(48, -38), S(-21,   1)},
   {S(40, -17), S(2, -24), S(-31,  -1), S(-24,  -8),
    S(-31,   2), S(-20,  29), S(4,  49), S(-16,   3)},
   {S(10, -20), S(4, -24), S(10,   2), S(2,  16),
    S(-10,  24), S(-10,  44), S(-184,  81), S(-17,  17)}},
  {{S(0,   0), S(-15, -39), S(9, -29), S(-49,  14),
    S(-36,   6), S(-8,  50), S(-168,  -3), S(-59,  19)},
   {S(0,   0), S(17, -18), S(9, -11), S(-11,  -5),
    S(-1, -24), S(26,  73), S(-186,   4), S(-32,  11)},
   {S(0,   0), S(19,  -9), S(1, -11), S(9, -26),
    S(28,  -5), S(-92,  56), S(-88, -74), S(-8,   1)},
   {S(0,   0), S(0,   3), S(-6,  -6), S(-35,  10),
    S(-46,  13), S(-98,  33), S(-7, -45), S(-35,  -5)},
   {S(0,   0), S(12,  -3), S(17, -15), S(17, -15),
    S(-5, -14), S(-36,   5), S(-101, -52), S(-18,  -1)},
   {S(0,   0), S(-8,  -5), S(-22,   1), S(-16,  -6),
    S(25, -22), S(-27,  10), S(52,  39), S(-14,  -2)},
   {S(0,   0), S(32, -22), S(19, -15), S(-9,  -6),
    S(-29,  13), S(-7,  23), S(-50, -39), S(-27,  18)},
   {S(0,   0), S(16, -57), S(17, -32), S(-18,  -7),
    S(-31,  24), S(-11,  24), S(-225, -49), S(-30,   5)}},
};

const int KingStorm[2][N_FILES / 2][N_RANKS] = {
  {{S(-6,  36), S(144,  -4), S(-13,  26), S(-7,   1),
    S(-12,  -3), S(-8,  -7), S(-19,   8), S(-28,  -2)},
   {S(-17,  60), S(64,  17), S(-9,  21), S(8,  12),
    S(3,   9), S(6,  -2), S(-5,   2), S(-16,   8)},
   {S(2,  48), S(15,  30), S(-17,  20), S(-13,  10),
    S(-1,   6), S(7,   3), S(8,  -7), S(7,   8)},
   {S(-1,  25), S(15,  22), S(-31,  10), S(-22,   1),
    S(-15,   4), S(13, -10), S(3,  -5), S(-20,   8)}},
  {{S(0,   0), S(-18, -16), S(-18,  -2), S(27, -24),
    S(10,  -6), S(15, -24), S(-6,   9), S(9,  30)},
   {S(0,   0), S(-15, -42), S(-3, -15), S(53, -17),
    S(15,  -5), S(20, -28), S(-12, -17), S(-34,   5)},
   {S(0,   0), S(-34, -62), S(-15, -13), S(9,  -6),
    S(6,  -2), S(-2, -17), S(-5, -21), S(-3,   3)},
   {S(0,   0), S(-1, -26), S(-27, -19), S(-21,   4),
    S(-10,  -6), S(7, -35), S(66, -29), S(11,  25)}},
};

/* Safety Evaluation Terms */

const int SafetyKnightWeight = S(48, 41);
const int SafetyBishopWeight = S(24, 35);
const int SafetyRookWeight = S(36, 8);
const int SafetyQueenWeight = S(30, 6);

const int SafetyAttackValue = S(45, 34);
const int SafetyWeakSquares = S(42, 41);
const int SafetyNoEnemyQueens = S(-237, -259);
const int SafetySafeQueenCheck = S(93, 83);
const int SafetySafeRookCheck = S(90, 98);
const int SafetySafeBishopCheck = S(59, 59);
const int SafetySafeKnightCheck = S(112, 117);
const int SafetyAdjustment = S(-74, -26);

const int SafetyShelter[2][N_RANKS] = {
   {S(-2,   7), S(-1,  13), S(0,   8), S(4,   7),
    S(6,   2), S(-1,   0), S(2,   0), S(0, -13)},
   {S(0,   0), S(-2,  13), S(-2,   9), S(4,   5),
    S(3,   1), S(-3,   0), S(-2,   0), S(-1,  -9)},
};

const int SafetyStorm[2][N_RANKS] = {
   {S(-4,  -1), S(-8,   3), S(0,   5), S(1,  -1),
    S(3,   6), S(-2,  20), S(-2,  18), S(2, -12)},
   {S(0,   0), S(1,   0), S(-1,   4), S(0,   0),
    S(0,   5), S(-1,   1), S(1,   0), S(1,   0)},
};

/* Passed Pawn Evaluation Terms */

const int PassedPawn[2][2][N_RANKS] = {
  {{S(0,   0), S(-39,  -4), S(-43,  25), S(-62,  28),
    S(8,  19), S(97,  -4), S(162,  46), S(0,   0)},
   {S(0,   0), S(-28,  13), S(-40,  42), S(-56,  44),
    S(-2,  56), S(114,  54), S(193,  94), S(0,   0)}},
  {{S(0,   0), S(-28,  29), S(-47,  36), S(-60,  54),
    S(8,  65), S(106,  76), S(258, 124), S(0,   0)},
   {S(0,   0), S(-28,  23), S(-40,  35), S(-55,  60),
    S(8,  89), S(95, 166), S(124, 293), S(0,   0)}},
};

const int PassedFriendlyDistance[N_FILES] = {
    S(0,   0), S(-3,   1), S(0,  -4), S(5, -13),
    S(6, -19), S(-9, -19), S(-9,  -7), S(0,   0),
};

const int PassedEnemyDistance[N_FILES] = {
    S(0,   0), S(5,  -1), S(7,   0), S(9,  11),
    S(0,  25), S(1,  37), S(16,  37), S(0,   0),
};

const int PassedSafePromotionPath = S(-49, 57);

/* Threat Evaluation Terms */

const int ThreatWeakPawn = S(-11, -38);
const int ThreatMinorAttackedByPawn = S(-55, -83);
const int ThreatMinorAttackedByMinor = S(-25, -45);
const int ThreatMinorAttackedByMajor = S(-30, -55);
const int ThreatRookAttackedByLesser = S(-48, -28);
const int ThreatMinorAttackedByKing = S(-43, -21);
const int ThreatRookAttackedByKing = S(-33, -18);
const int ThreatQueenAttackedByOne = S(-50, -7);
const int ThreatOverloadedPieces = S(-7, -16);
const int ThreatByPawnPush = S(15, 32);

/* Space Evaluation Terms */

const int SpaceRestrictPiece = S(-4, -1);
const int SpaceRestrictEmpty = S(-4, -2);
const int SpaceCenterControl = S(3, 0);

/* Closedness Evaluation Terms */

const int ClosednessKnightAdjustment[9] = {
    S(-7,  10), S(-7,  29), S(-9,  37), S(-5,  37),
    S(-3,  44), S(-1,  36), S(1,  33), S(-10,  51),
    S(-7,  30),
};

const int ClosednessRookAdjustment[9] = {
    S(42,  43), S(-6,  80), S(3,  59), S(-5,  47),
    S(-7,  41), S(-3,  23), S(-6,  11), S(-17,  11),
    S(-34, -12),
};

/* Complexity Evaluation Terms */

const int ComplexityTotalPawns = S(0, 8);
const int ComplexityPawnFlanks = S(0, 82);
const int ComplexityPawnEndgame = S(0, 76);
const int ComplexityAdjustment = S(0, -157);

/* General Evaluation Terms */

const int Tempo = 20;

#undef S

int evaluateBoard(Thread* thread, Board* board) {

    int phase, eval, pkeval, factor = SCALE_NORMAL;

    // We can recognize positions we just evaluated
    if (thread->states[thread->height - 1].move == NULL_MOVE)
        return -thread->states[thread->height - 1].eval + 2 * Tempo;

    // Use the NNUE unless we are in an extremely unbalanced position
    if (USE_NNUE && abs(ScoreEG(board->psqtmat)) <= 2000) {
        eval = nnue_evaluate(thread, board);
        eval = board->turn == WHITE ? eval : -eval;
    }

    else 
    {
        EvalInfo ei;
        initPSQTInfo(thread, board, &ei);
        eval = evaluatePieces(&ei, board);

        pkeval = ei.pkeval[WHITE] - ei.pkeval[BLACK];
        if (ei.pkentry == NULL) pkeval += computePKNetwork(board);

        eval += pkeval + board->psqtmat;
        eval += evaluateClosedness(&ei, board);
        eval += evaluateComplexity(&ei, board, eval);

        // Store a new Pawn King Entry if we did not have one
        if (!TRACE && ei.pkentry == NULL)
            storeCachedPawnKingEval(thread, board, ei.passedPawns, pkeval, ei.pksafety);

        // Scale evaluation based on remaining material
        factor = evaluateScaleFactor(board, eval);
        if (TRACE) T.factor = factor;
    }

    // Calculate the game phase based on remaining material (Fruit Method)
    phase = 4 * popcount(board->pieces[QUEEN])
        + 2 * popcount(board->pieces[ROOK])
        + 1 * popcount(board->pieces[KNIGHT] | board->pieces[BISHOP]);

    // Compute and store an interpolated evaluation from white's POV
    eval = (ScoreMG(eval) * phase
        + ScoreEG(eval) * (24 - phase) * factor / SCALE_NORMAL) / 24;

    // Factor in the Tempo after interpolation and scaling, so that
    // if a null move is made, then we know eval = last_eval + 2 * Tempo
    return Tempo + (board->turn == WHITE ? eval : -eval);
}

int evaluatePieces(EvalInfo* ei, Board* board) {

    int eval;

    eval = evaluatePawns(ei, board, WHITE) - evaluatePawns(ei, board, BLACK);

    // This needs to be done after pawn evaluation but before king safety evaluation
    evaluateKingsPawns(ei, board, WHITE);
    evaluateKingsPawns(ei, board, BLACK);

    eval += evaluateKnights(ei, board, WHITE) - evaluateKnights(ei, board, BLACK);
    eval += evaluateBishops(ei, board, WHITE) - evaluateBishops(ei, board, BLACK);
    eval += evaluateRooks(ei, board, WHITE) - evaluateRooks(ei, board, BLACK);
    eval += evaluateQueens(ei, board, WHITE) - evaluateQueens(ei, board, BLACK);
    eval += evaluateKings(ei, board, WHITE) - evaluateKings(ei, board, BLACK);
    eval += evaluatePassed(ei, board, WHITE) - evaluatePassed(ei, board, BLACK);
    eval += evaluateThreats(ei, board, WHITE) - evaluateThreats(ei, board, BLACK);
    eval += evaluateSpace(ei, board, WHITE) - evaluateSpace(ei, board, BLACK);

    return eval;
}

int evaluatePawns(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;
    const int Forward = (colour == WHITE) ? 8 : -8;

    int sq, flag, eval = 0, pkeval = 0;
    uint64_t pawns, myPawns, tempPawns, enemyPawns, attacks;

    // Store off pawn attacks for king safety and threat computations
    ei->attackedBy2[US] = ei->pawnAttacks[US] & ei->attacked[US];
    ei->attacked[US] |= ei->pawnAttacks[US];
    ei->attackedBy[US][PAWN] = ei->pawnAttacks[US];

    // Update King Safety calculations
    attacks = ei->pawnAttacks[US] & ei->kingAreas[THEM];
    ei->kingAttacksCount[THEM] += popcount(attacks);

    // Pawn hash holds the rest of the pawn evaluation
    if (ei->pkentry != NULL) return eval;

    pawns = board->pieces[PAWN];
    myPawns = tempPawns = pawns & board->colours[US];
    enemyPawns = pawns & board->colours[THEM];

    // Evaluate each pawn (but not for being passed)
    while (tempPawns) {

        // Pop off the next pawn
        sq = poplsb(&tempPawns);
        if (TRACE) T.PawnValue[US]++;
        if (TRACE) T.PawnPSQT[relativeSquare(US, sq)][US]++;

        uint64_t neighbors = myPawns & adjacentFilesMasks(fileOf(sq));
        uint64_t backup = myPawns & passedPawnMasks(THEM, sq);
        uint64_t stoppers = enemyPawns & passedPawnMasks(US, sq);
        uint64_t threats = enemyPawns & pawnAttacks(US, sq);
        uint64_t support = myPawns & pawnAttacks(THEM, sq);
        uint64_t pushThreats = enemyPawns & pawnAttacks(US, sq + Forward);
        uint64_t pushSupport = myPawns & pawnAttacks(THEM, sq + Forward);
        uint64_t leftovers = stoppers ^ threats ^ pushThreats;

        // Save passed pawn information for later evaluation
        if (!stoppers) setBit(&ei->passedPawns, sq);

        // Apply a bonus for pawns which will become passers by advancing a
        // square then exchanging our supporters with the remaining stoppers
        else if (!leftovers && popcount(pushSupport) >= popcount(pushThreats)) {
            flag = popcount(support) >= popcount(threats);
            pkeval += PawnCandidatePasser[flag][relativeRankOf(US, sq)];
            if (TRACE) T.PawnCandidatePasser[flag][relativeRankOf(US, sq)][US]++;
        }

        // Apply a penalty if the pawn is isolated. We consider pawns that
        // are able to capture another pawn to not be isolated, as they may
        // have the potential to deisolate by capturing, or be traded away
        if (!threats && !neighbors) {
            pkeval += PawnIsolated[fileOf(sq)];
            if (TRACE) T.PawnIsolated[fileOf(sq)][US]++;
        }

        // Apply a penalty if the pawn is stacked. We adjust the bonus for when
        // the pawn appears to be a candidate to unstack. This occurs when the
        // pawn is not passed but may capture or be recaptured by our own pawns,
        // and when the pawn may freely advance on a file and then be traded away
        if (several(Files[fileOf(sq)] & myPawns)) {
            flag = (stoppers && (threats || neighbors))
                || (stoppers & ~forwardFileMasks(US, sq));
            pkeval += PawnStacked[flag][fileOf(sq)];
            if (TRACE) T.PawnStacked[flag][fileOf(sq)][US]++;
        }

        // Apply a penalty if the pawn is backward. We follow the usual definition
        // of backwards, but also specify that the pawn is not both isolated and
        // backwards at the same time. We don't give backward pawns a connected bonus
        if (neighbors && pushThreats && !backup) {
            flag = !(Files[fileOf(sq)] & enemyPawns);
            pkeval += PawnBackwards[flag][relativeRankOf(US, sq)];
            if (TRACE) T.PawnBackwards[flag][relativeRankOf(US, sq)][US]++;
        }

        // Apply a bonus if the pawn is connected and not backwards. We consider a
        // pawn to be connected when there is a pawn lever or the pawn is supported
        else if (pawnConnectedMasks(US, sq) & myPawns) {
            pkeval += PawnConnected32[relativeSquare32(US, sq)];
            if (TRACE) T.PawnConnected32[relativeSquare32(US, sq)][US]++;
        }
    }

    ei->pkeval[US] = pkeval; // Save eval for the Pawn Hash

    return eval;
}

int evaluateKnights(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, outside, kingDistance, defended, count, eval = 0;
    uint64_t attacks;

    uint64_t enemyPawns = board->pieces[PAWN] & board->colours[THEM];
    uint64_t tempKnights = board->pieces[KNIGHT] & board->colours[US];

    ei->attackedBy[US][KNIGHT] = 0ull;

    // Evaluate each knight
    while (tempKnights) {

        // Pop off the next knight
        sq = poplsb(&tempKnights);
        if (TRACE) T.KnightValue[US]++;
        if (TRACE) T.KnightPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        attacks = knightAttacks(sq);
        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][KNIGHT] |= attacks;

        // Apply a bonus if the knight is on an outpost square, and cannot be attacked
        // by an enemy pawn. Increase the bonus if one of our pawns supports the knight
        if (testBit(outpostRanksMasks(US), sq)
            && !(outpostSquareMasks(US, sq) & enemyPawns)) {
            outside = testBit(FILE_A | FILE_H, sq);
            defended = testBit(ei->pawnAttacks[US], sq);
            eval += KnightOutpost[outside][defended];
            if (TRACE) T.KnightOutpost[outside][defended][US]++;
        }

        // Apply a bonus if the knight is behind a pawn
        if (testBit(pawnAdvance(board->pieces[PAWN], 0ull, THEM), sq)) {
            eval += KnightBehindPawn;
            if (TRACE) T.KnightBehindPawn[US]++;
        }

        // Apply a penalty if the knight is far from both kings
        kingDistance = Min(distanceBetween(sq, ei->kingSquare[THEM]), distanceBetween(sq, ei->kingSquare[US]));
        if (kingDistance >= 4) {
            eval += KnightInSiberia[kingDistance - 4];
            if (TRACE) T.KnightInSiberia[kingDistance - 4][US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the knight
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += KnightMobility[count];
        if (TRACE) T.KnightMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyKnightWeight;
            if (TRACE) T.SafetyKnightWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateBishops(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, outside, defended, count, eval = 0;
    uint64_t attacks;

    uint64_t enemyPawns = board->pieces[PAWN] & board->colours[THEM];
    uint64_t tempBishops = board->pieces[BISHOP] & board->colours[US];

    ei->attackedBy[US][BISHOP] = 0ull;

    // Apply a bonus for having a pair of bishops
    if ((tempBishops & WHITE_SQUARES) && (tempBishops & BLACK_SQUARES)) {
        eval += BishopPair;
        if (TRACE) T.BishopPair[US]++;
    }

    // Evaluate each bishop
    while (tempBishops) {

        // Pop off the next Bishop
        sq = poplsb(&tempBishops);
        if (TRACE) T.BishopValue[US]++;
        if (TRACE) T.BishopPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        attacks = bishopAttacks(sq, ei->occupiedMinusBishops[US]);
        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][BISHOP] |= attacks;

        // Apply a penalty for the bishop based on number of rammed pawns
        // of our own colour, which reside on the same shade of square as the bishop
        count = popcount(ei->rammedPawns[US] & squaresOfMatchingColour(sq));
        eval += count * BishopRammedPawns;
        if (TRACE) T.BishopRammedPawns[US] += count;

        // Apply a bonus if the bishop is on an outpost square, and cannot be attacked
        // by an enemy pawn. Increase the bonus if one of our pawns supports the bishop.
        if (testBit(outpostRanksMasks(US), sq)
            && !(outpostSquareMasks(US, sq) & enemyPawns)) {
            outside = testBit(FILE_A | FILE_H, sq);
            defended = testBit(ei->pawnAttacks[US], sq);
            eval += BishopOutpost[outside][defended];
            if (TRACE) T.BishopOutpost[outside][defended][US]++;
        }

        // Apply a bonus if the bishop is behind a pawn
        if (testBit(pawnAdvance(board->pieces[PAWN], 0ull, THEM), sq)) {
            eval += BishopBehindPawn;
            if (TRACE) T.BishopBehindPawn[US]++;
        }

        // Apply a bonus when controlling both central squares on a long diagonal
        if (testBit(LONG_DIAGONALS & ~CENTER_SQUARES, sq)
            && several(bishopAttacks(sq, board->pieces[PAWN]) & CENTER_SQUARES)) {
            eval += BishopLongDiagonal;
            if (TRACE) T.BishopLongDiagonal[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the bishop
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += BishopMobility[count];
        if (TRACE) T.BishopMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyBishopWeight;
            if (TRACE) T.SafetyBishopWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateRooks(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, open, count, eval = 0;
    uint64_t attacks;

    uint64_t myPawns = board->pieces[PAWN] & board->colours[US];
    uint64_t enemyPawns = board->pieces[PAWN] & board->colours[THEM];
    uint64_t tempRooks = board->pieces[ROOK] & board->colours[US];

    ei->attackedBy[US][ROOK] = 0ull;

    // Evaluate each rook
    while (tempRooks) {

        // Pop off the next rook
        sq = poplsb(&tempRooks);
        if (TRACE) T.RookValue[US]++;
        if (TRACE) T.RookPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        attacks = rookAttacks(sq, ei->occupiedMinusRooks[US]);
        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][ROOK] |= attacks;

        // Rook is on a semi-open file if there are no pawns of the rook's
        // colour on the file. If there are no pawns at all, it is an open file
        if (!(myPawns & Files[fileOf(sq)])) {
            open = !(enemyPawns & Files[fileOf(sq)]);
            eval += RookFile[open];
            if (TRACE) T.RookFile[open][US]++;
        }

        // Rook gains a bonus for being located on seventh rank relative to its
        // colour so long as the enemy king is on the last two ranks of the board
        if (relativeRankOf(US, sq) == 6
            && relativeRankOf(US, ei->kingSquare[THEM]) >= 6) {
            eval += RookOnSeventh;
            if (TRACE) T.RookOnSeventh[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the rook
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += RookMobility[count];
        if (TRACE) T.RookMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyRookWeight;
            if (TRACE) T.SafetyRookWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateQueens(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, count, eval = 0;
    uint64_t tempQueens, attacks, occupied;

    tempQueens = board->pieces[QUEEN] & board->colours[US];
    occupied = board->colours[WHITE] | board->colours[BLACK];

    ei->attackedBy[US][QUEEN] = 0ull;

    // Evaluate each queen
    while (tempQueens) {

        // Pop off the next queen
        sq = poplsb(&tempQueens);
        if (TRACE) T.QueenValue[US]++;
        if (TRACE) T.QueenPSQT[relativeSquare(US, sq)][US]++;

        // Compute possible attacks and store off information for king safety
        attacks = queenAttacks(sq, occupied);
        ei->attackedBy2[US] |= attacks & ei->attacked[US];
        ei->attacked[US] |= attacks;
        ei->attackedBy[US][QUEEN] |= attacks;

        // Apply a penalty if the Queen is at risk for a discovered attack
        if (discoveredAttacks(board, sq, US)) {
            eval += QueenRelativePin;
            if (TRACE) T.QueenRelativePin[US]++;
        }

        // Apply a bonus (or penalty) based on the mobility of the queen
        count = popcount(ei->mobilityAreas[US] & attacks);
        eval += QueenMobility[count];
        if (TRACE) T.QueenMobility[count][US]++;

        // Update King Safety calculations
        if ((attacks &= ei->kingAreas[THEM] & ~ei->pawnAttacksBy2[THEM])) {
            ei->kingAttacksCount[THEM] += popcount(attacks);
            ei->kingAttackersCount[THEM] += 1;
            ei->kingAttackersWeight[THEM] += SafetyQueenWeight;
            if (TRACE) T.SafetyQueenWeight[THEM]++;
        }
    }

    return eval;
}

int evaluateKingsPawns(EvalInfo* ei, Board* board, int colour) {
    // Skip computations if results are cached in the Pawn King Table
    if (ei->pkentry != NULL) return 0;

    const int US = colour, THEM = !colour;

    int dist, blocked;

    uint64_t myPawns = board->pieces[PAWN] & board->colours[US];
    uint64_t enemyPawns = board->pieces[PAWN] & board->colours[THEM];

    int kingSq = ei->kingSquare[US];

    // Evaluate based on the number of files between our King and the nearest
    // file-wise pawn. If there is no pawn, kingPawnFileDistance() returns the
    // same distance for both sides causing this evaluation term to be neutral
    dist = kingPawnFileDistance(board->pieces[PAWN], kingSq);
    ei->pkeval[US] += KingPawnFileProximity[dist];
    if (TRACE) T.KingPawnFileProximity[dist][US]++;

    // Evaluate King Shelter & King Storm threat by looking at the file of our King,
    // as well as the adjacent files. When looking at pawn distances, we will use a
    // distance of 7 to denote a missing pawn, since distance 7 is not possible otherwise.
    for (int file = Max(0, fileOf(kingSq) - 1); file <= Min(N_FILES - 1, fileOf(kingSq) + 1); file++) {

        // Find closest friendly pawn at or above our King on a given file
        uint64_t ours = myPawns & Files[file] & forwardRanksMasks(US, rankOf(kingSq));
        int ourDist = !ours ? 7 : abs(rankOf(kingSq) - rankOf(backmost(US, ours)));

        // Find closest enemy pawn at or above our King on a given file
        uint64_t theirs = enemyPawns & Files[file] & forwardRanksMasks(US, rankOf(kingSq));
        int theirDist = !theirs ? 7 : abs(rankOf(kingSq) - rankOf(backmost(US, theirs)));

        // Evaluate King Shelter using pawn distance. Use separate evaluation
        // depending on the file, and if we are looking at the King's file
        ei->pkeval[US] += KingShelter[file == fileOf(kingSq)][file][ourDist];
        if (TRACE) T.KingShelter[file == fileOf(kingSq)][file][ourDist][US]++;

        // Update the Shelter Safety
        ei->pksafety[US] += SafetyShelter[file == fileOf(kingSq)][ourDist];
        if (TRACE) T.SafetyShelter[file == fileOf(kingSq)][ourDist][US]++;

        // Evaluate King Storm using enemy pawn distance. Use a separate evaluation
        // depending on the file, and if the opponent's pawn is blocked by our own
        blocked = (ourDist != 7 && (ourDist == theirDist - 1));
        ei->pkeval[US] += KingStorm[blocked][mirrorFile(file)][theirDist];
        if (TRACE) T.KingStorm[blocked][mirrorFile(file)][theirDist][US]++;

        // Update the Storm Safety
        ei->pksafety[US] += SafetyStorm[blocked][theirDist];
        if (TRACE) T.SafetyStorm[blocked][theirDist][US]++;
    }

    return 0;
}

int evaluateKings(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;

    int count, safety, mg, eg, eval = 0;

    uint64_t enemyQueens = board->pieces[QUEEN] & board->colours[THEM];

    uint64_t defenders = (board->pieces[PAWN] & board->colours[US])
        | (board->pieces[KNIGHT] & board->colours[US])
        | (board->pieces[BISHOP] & board->colours[US]);

    int kingSq = ei->kingSquare[US];
    if (TRACE) T.KingValue[US]++;
    if (TRACE) T.KingPSQT[relativeSquare(US, kingSq)][US]++;

    // Bonus for our pawns and minors sitting within our king area
    count = popcount(defenders & ei->kingAreas[US]);
    eval += KingDefenders[count];
    if (TRACE) T.KingDefenders[count][US]++;

    // Perform King Safety when we have two attackers, or
    // one attacker with a potential for a Queen attacker
    if (ei->kingAttackersCount[US] > 1 - popcount(enemyQueens)) {

        // Weak squares are attacked by the enemy, defended no more
        // than once and only defended by our Queens or our King
        uint64_t weak = ei->attacked[THEM]
            & ~ei->attackedBy2[US]
            & (~ei->attacked[US] | ei->attackedBy[US][QUEEN] | ei->attackedBy[US][KING]);

        // Usually the King Area is 9 squares. Scale are attack counts to account for
        // when the king is in an open area and expects more attacks, or the opposite
        int scaledAttackCounts = (9 * ei->kingAttacksCount[US]) / popcount(ei->kingAreas[US]);

        // Safe target squares are defended or are weak and attacked by two.
        // We exclude squares containing pieces which we cannot capture.
        uint64_t safe = ~board->colours[THEM]
            & (~ei->attacked[US] | (weak & ei->attackedBy2[THEM]));

        // Find square and piece combinations which would check our King
        uint64_t occupied = board->colours[WHITE] | board->colours[BLACK];
        uint64_t knightThreats = knightAttacks(kingSq);
        uint64_t bishopThreats = bishopAttacks(kingSq, occupied);
        uint64_t rookThreats = rookAttacks(kingSq, occupied);
        uint64_t queenThreats = bishopThreats | rookThreats;

        // Identify if there are pieces which can move to the checking squares safely.
        // We consider forking a Queen to be a safe check, even with our own Queen.
        uint64_t knightChecks = knightThreats & safe & ei->attackedBy[THEM][KNIGHT];
        uint64_t bishopChecks = bishopThreats & safe & ei->attackedBy[THEM][BISHOP];
        uint64_t rookChecks = rookThreats & safe & ei->attackedBy[THEM][ROOK];
        uint64_t queenChecks = queenThreats & safe & ei->attackedBy[THEM][QUEEN];

        safety = ei->kingAttackersWeight[US];

        safety += SafetyAttackValue * scaledAttackCounts
            + SafetyWeakSquares * popcount(weak & ei->kingAreas[US])
            + SafetyNoEnemyQueens * !enemyQueens
            + SafetySafeQueenCheck * popcount(queenChecks)
            + SafetySafeRookCheck * popcount(rookChecks)
            + SafetySafeBishopCheck * popcount(bishopChecks)
            + SafetySafeKnightCheck * popcount(knightChecks)
            + ei->pksafety[US]
            + SafetyAdjustment;

        if (TRACE) T.SafetyAttackValue[US] = scaledAttackCounts;
        if (TRACE) T.SafetyWeakSquares[US] = popcount(weak & ei->kingAreas[US]);
        if (TRACE) T.SafetyNoEnemyQueens[US] = !enemyQueens;
        if (TRACE) T.SafetySafeQueenCheck[US] = popcount(queenChecks);
        if (TRACE) T.SafetySafeRookCheck[US] = popcount(rookChecks);
        if (TRACE) T.SafetySafeBishopCheck[US] = popcount(bishopChecks);
        if (TRACE) T.SafetySafeKnightCheck[US] = popcount(knightChecks);
        if (TRACE) T.SafetyAdjustment[US] = 1;

        // Convert safety to an MG and EG score
        mg = ScoreMG(safety), eg = ScoreEG(safety);
        eval += MakeScore(-mg * Max(0, mg) / 720, -Max(0, eg) / 20);
        if (TRACE) T.safety[US] = safety;
    }

    else if (TRACE) {
        T.SafetyKnightWeight[US] = 0;
        T.SafetyBishopWeight[US] = 0;
        T.SafetyRookWeight[US] = 0;
        T.SafetyQueenWeight[US] = 0;

        for (int i = 0; i < 8; i++) {
            T.SafetyShelter[0][i][US] = 0;
            T.SafetyShelter[1][i][US] = 0;
            T.SafetyStorm[0][i][US] = 0;
            T.SafetyStorm[1][i][US] = 0;
        }
    }

    return eval;
}

int evaluatePassed(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;

    int sq, rank, dist, flag, canAdvance, safeAdvance, eval = 0;

    uint64_t bitboard;
    uint64_t myPassers = board->colours[US] & ei->passedPawns;
    uint64_t occupied = board->colours[WHITE] | board->colours[BLACK];
    uint64_t tempPawns = myPassers;

    // Evaluate each passed pawn
    while (tempPawns) {

        // Pop off the next passed Pawn
        sq = poplsb(&tempPawns);
        rank = relativeRankOf(US, sq);
        bitboard = pawnAdvance(1ull << sq, 0ull, US);

        // Evaluate based on rank, ability to advance, and safety
        canAdvance = !(bitboard & occupied);
        safeAdvance = !(bitboard & ei->attacked[THEM]);
        eval += PassedPawn[canAdvance][safeAdvance][rank];
        if (TRACE) T.PassedPawn[canAdvance][safeAdvance][rank][US]++;

        // Short-circuit evaluation for additional passers on a file
        if (several(forwardFileMasks(US, sq) & myPassers)) continue;

        // Evaluate based on distance from our king
        dist = distanceBetween(sq, ei->kingSquare[US]);
        eval += dist * PassedFriendlyDistance[rank];
        if (TRACE) T.PassedFriendlyDistance[rank][US] += dist;

        // Evaluate based on distance from their king
        dist = distanceBetween(sq, ei->kingSquare[THEM]);
        eval += dist * PassedEnemyDistance[rank];
        if (TRACE) T.PassedEnemyDistance[rank][US] += dist;

        // Apply a bonus when the path to promoting is uncontested
        bitboard = forwardRanksMasks(US, rankOf(sq)) & Files[fileOf(sq)];
        flag = !(bitboard & (board->colours[THEM] | ei->attacked[THEM]));
        eval += flag * PassedSafePromotionPath;
        if (TRACE) T.PassedSafePromotionPath[US] += flag;
    }

    return eval;
}

int evaluateThreats(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;
    const uint64_t Rank3Rel = US == WHITE ? RANK_3 : RANK_6;

    int count, eval = 0;

    uint64_t friendly = board->colours[US];
    uint64_t enemy = board->colours[THEM];
    uint64_t occupied = friendly | enemy;

    uint64_t pawns = friendly & board->pieces[PAWN];
    uint64_t knights = friendly & board->pieces[KNIGHT];
    uint64_t bishops = friendly & board->pieces[BISHOP];
    uint64_t rooks = friendly & board->pieces[ROOK];
    uint64_t queens = friendly & board->pieces[QUEEN];

    uint64_t attacksByPawns = ei->attackedBy[THEM][PAWN];
    uint64_t attacksByMinors = ei->attackedBy[THEM][KNIGHT] | ei->attackedBy[THEM][BISHOP];
    uint64_t attacksByMajors = ei->attackedBy[THEM][ROOK] | ei->attackedBy[THEM][QUEEN];

    // Squares with more attackers, few defenders, and no pawn support
    uint64_t poorlyDefended = (ei->attacked[THEM] & ~ei->attacked[US])
        | (ei->attackedBy2[THEM] & ~ei->attackedBy2[US] & ~ei->attackedBy[US][PAWN]);

    uint64_t weakMinors = (knights | bishops) & poorlyDefended;

    // A friendly minor or major is overloaded if attacked and defended by exactly one
    uint64_t overloaded = (knights | bishops | rooks | queens)
        & ei->attacked[US] & ~ei->attackedBy2[US]
        & ei->attacked[THEM] & ~ei->attackedBy2[THEM];

    // Look for enemy non-pawn pieces which we may threaten with a pawn advance.
    // Don't consider pieces we already threaten, pawn moves which would be countered
    // by a pawn capture, and squares which are completely unprotected by our pieces.
    uint64_t pushThreat = pawnAdvance(pawns, occupied, US);
    pushThreat |= pawnAdvance(pushThreat & ~attacksByPawns & Rank3Rel, occupied, US);
    pushThreat &= ~attacksByPawns & (ei->attacked[US] | ~ei->attacked[THEM]);
    pushThreat = pawnAttackSpan(pushThreat, enemy & ~ei->attackedBy[US][PAWN], US);

    // Penalty for each of our poorly supported pawns
    count = popcount(pawns & ~attacksByPawns & poorlyDefended);
    eval += count * ThreatWeakPawn;
    if (TRACE) T.ThreatWeakPawn[US] += count;

    // Penalty for pawn threats against our minors
    count = popcount((knights | bishops) & attacksByPawns);
    eval += count * ThreatMinorAttackedByPawn;
    if (TRACE) T.ThreatMinorAttackedByPawn[US] += count;

    // Penalty for any minor threat against minor pieces
    count = popcount((knights | bishops) & attacksByMinors);
    eval += count * ThreatMinorAttackedByMinor;
    if (TRACE) T.ThreatMinorAttackedByMinor[US] += count;

    // Penalty for all major threats against poorly supported minors
    count = popcount(weakMinors & attacksByMajors);
    eval += count * ThreatMinorAttackedByMajor;
    if (TRACE) T.ThreatMinorAttackedByMajor[US] += count;

    // Penalty for pawn and minor threats against our rooks
    count = popcount(rooks & (attacksByPawns | attacksByMinors));
    eval += count * ThreatRookAttackedByLesser;
    if (TRACE) T.ThreatRookAttackedByLesser[US] += count;

    // Penalty for king threats against our poorly defended minors
    count = popcount(weakMinors & ei->attackedBy[THEM][KING]);
    eval += count * ThreatMinorAttackedByKing;
    if (TRACE) T.ThreatMinorAttackedByKing[US] += count;

    // Penalty for king threats against our poorly defended rooks
    count = popcount(rooks & poorlyDefended & ei->attackedBy[THEM][KING]);
    eval += count * ThreatRookAttackedByKing;
    if (TRACE) T.ThreatRookAttackedByKing[US] += count;

    // Penalty for any threat against our queens
    count = popcount(queens & ei->attacked[THEM]);
    eval += count * ThreatQueenAttackedByOne;
    if (TRACE) T.ThreatQueenAttackedByOne[US] += count;

    // Penalty for any overloaded minors or majors
    count = popcount(overloaded);
    eval += count * ThreatOverloadedPieces;
    if (TRACE) T.ThreatOverloadedPieces[US] += count;

    // Bonus for giving threats by safe pawn pushes
    count = popcount(pushThreat);
    eval += count * ThreatByPawnPush;
    if (TRACE) T.ThreatByPawnPush[colour] += count;

    return eval;
}

int evaluateSpace(EvalInfo* ei, Board* board, int colour) {

    const int US = colour, THEM = !colour;

    int count, eval = 0;

    uint64_t friendly = board->colours[US];
    uint64_t enemy = board->colours[THEM];

    // Squares we attack with more enemy attackers and no friendly pawn attacks
    uint64_t uncontrolled = ei->attackedBy2[THEM] & ei->attacked[US]
        & ~ei->attackedBy2[US] & ~ei->attackedBy[US][PAWN];

    // Penalty for restricted piece moves
    count = popcount(uncontrolled & (friendly | enemy));
    eval += count * SpaceRestrictPiece;
    if (TRACE) T.SpaceRestrictPiece[US] += count;

    count = popcount(uncontrolled & ~friendly & ~enemy);
    eval += count * SpaceRestrictEmpty;
    if (TRACE) T.SpaceRestrictEmpty[US] += count;

    // Bonus for uncontested central squares
    // This is mostly relevant in the opening and the early middlegame, while rarely correct
    // in the endgame where one rook or queen could control many uncontested squares.
    // Thus we don't apply this term when below a threshold of minors/majors count.
    if (popcount(board->pieces[KNIGHT] | board->pieces[BISHOP])
        + 2 * popcount(board->pieces[ROOK] | board->pieces[QUEEN]) > 12) {
        count = popcount(~ei->attacked[THEM] & (ei->attacked[US] | friendly) & CENTER_BIG);
        eval += count * SpaceCenterControl;
        if (TRACE) T.SpaceCenterControl[US] += count;
    }

    return eval;
}

int evaluateClosedness(EvalInfo* ei, Board* board) {

    int closedness, count, eval = 0;

    uint64_t white = board->colours[WHITE];
    uint64_t black = board->colours[BLACK];

    uint64_t knights = board->pieces[KNIGHT];
    uint64_t rooks = board->pieces[ROOK];

    // Compute Closedness factor for this position
    closedness = 1 * popcount(board->pieces[PAWN])
        + 3 * popcount(ei->rammedPawns[WHITE])
        - 4 * openFileCount(board->pieces[PAWN]);
    closedness = Max(0, Min(8, closedness / 3));

    // Evaluate Knights based on how Closed the position is
    count = popcount(white & knights) - popcount(black & knights);
    eval += count * ClosednessKnightAdjustment[closedness];
    if (TRACE) T.ClosednessKnightAdjustment[closedness][WHITE] += count;

    // Evaluate Rooks based on how Closed the position is
    count = popcount(white & rooks) - popcount(black & rooks);
    eval += count * ClosednessRookAdjustment[closedness];
    if (TRACE) T.ClosednessRookAdjustment[closedness][WHITE] += count;

    return eval;
}

int evaluateComplexity(EvalInfo* ei, Board* board, int eval) {

    // Adjust endgame evaluation based on features related to how
    // likely the stronger side is to convert the position.
    // More often than not, this is a penalty for drawish positions.

    (void)ei; // Silence compiler warning

    int complexity;
    int eg = ScoreEG(eval);
    int sign = (eg > 0) - (eg < 0);

    int pawnsOnBothFlanks = (board->pieces[PAWN] & LEFT_FLANK)
        && (board->pieces[PAWN] & RIGHT_FLANK);

    uint64_t knights = board->pieces[KNIGHT];
    uint64_t bishops = board->pieces[BISHOP];
    uint64_t rooks = board->pieces[ROOK];
    uint64_t queens = board->pieces[QUEEN];

    // Compute the initiative bonus or malus for the attacking side
    complexity = ComplexityTotalPawns * popcount(board->pieces[PAWN])
        + ComplexityPawnFlanks * pawnsOnBothFlanks
        + ComplexityPawnEndgame * !(knights | bishops | rooks | queens)
        + ComplexityAdjustment;

    if (TRACE) T.ComplexityTotalPawns[WHITE] += popcount(board->pieces[PAWN]);
    if (TRACE) T.ComplexityPawnFlanks[WHITE] += pawnsOnBothFlanks;
    if (TRACE) T.ComplexityPawnEndgame[WHITE] += !(knights | bishops | rooks | queens);
    if (TRACE) T.ComplexityAdjustment[WHITE] += 1;

    // Avoid changing which side has the advantage
    int v = sign * Max<int>(ScoreEG(complexity), -abs(eg));

    if (TRACE) T.eval = eval;
    if (TRACE) T.complexity = complexity;
    return MakeScore(0, v);
}

int evaluateScaleFactor(Board* board, int eval) 
{
    // Scale endgames based upon the remaining material. We check
    // for various Opposite Coloured Bishop cases, positions with
    // a lone Queen against multiple minor pieces and/or rooks, and
    // positions with a Lone minor that should not be winnable

    const uint64_t pawns = board->pieces[PAWN];
    const uint64_t knights = board->pieces[KNIGHT];
    const uint64_t bishops = board->pieces[BISHOP];
    const uint64_t rooks = board->pieces[ROOK];
    const uint64_t queens = board->pieces[QUEEN];

    const uint64_t minors = knights | bishops;
    const uint64_t pieces = knights | bishops | rooks;

    const uint64_t white = board->colours[WHITE];
    const uint64_t black = board->colours[BLACK];

    const uint64_t weak = ScoreEG(eval) < 0 ? white : black;
    const uint64_t strong = ScoreEG(eval) < 0 ? black : white;


    // Check for opposite coloured bishops
    if (onlyOne(white & bishops)
        && onlyOne(black & bishops)
        && onlyOne(bishops & WHITE_SQUARES)) {

        // Scale factor for OCB + knights
        if (!(rooks | queens)
            && onlyOne(white & knights)
            && onlyOne(black & knights))
            return SCALE_OCB_ONE_KNIGHT;

        // Scale factor for OCB + rooks
        if (!(knights | queens)
            && onlyOne(white & rooks)
            && onlyOne(black & rooks))
            return SCALE_OCB_ONE_ROOK;

        // Scale factor for lone OCB
        if (!(knights | rooks | queens))
            return SCALE_OCB_BISHOPS_ONLY;
    }

    // Lone Queens are weak against multiple pieces
    if (onlyOne(queens) && several(pieces) && pieces == (weak & pieces))
        return SCALE_LONE_QUEEN;

    // Lone Minor vs King + Pawns should never be won
    if ((strong & minors) && popcount(strong) == 2)
        return SCALE_DRAW;

    // Scale up lone pieces with massive pawn advantages
    if (!queens
        && !several(pieces & white)
        && !several(pieces & black)
        && popcount(strong & pawns) - popcount(weak & pawns) > 2)
        return SCALE_LARGE_PAWN_ADV;

    // Scale down as the number of pawns of the strong side reduces
    return Min<int>(SCALE_NORMAL, 96 + popcount(pawns & strong) * 8);
}

void initPSQTInfo(Thread* thread, Board* board, EvalInfo* ei) 
{
    uint64_t white = board->colours[WHITE];
    uint64_t black = board->colours[BLACK];

    uint64_t pawns = board->pieces[PAWN];
    uint64_t bishops = board->pieces[BISHOP] | board->pieces[QUEEN];
    uint64_t rooks = board->pieces[ROOK] | board->pieces[QUEEN];
    uint64_t kings = board->pieces[KING];

    // Save some general information about the pawn structure for later
    ei->pawnAttacks[WHITE] = pawnAttackSpan(white & pawns, ~0ull, WHITE);
    ei->pawnAttacks[BLACK] = pawnAttackSpan(black & pawns, ~0ull, BLACK);
    ei->pawnAttacksBy2[WHITE] = pawnAttackDouble(white & pawns, ~0ull, WHITE);
    ei->pawnAttacksBy2[BLACK] = pawnAttackDouble(black & pawns, ~0ull, BLACK);
    ei->rammedPawns[WHITE] = pawnAdvance(black & pawns, ~(white & pawns), BLACK);
    ei->rammedPawns[BLACK] = pawnAdvance(white & pawns, ~(black & pawns), WHITE);
    ei->blockedPawns[WHITE] = pawnAdvance(white | black, ~(white & pawns), BLACK);
    ei->blockedPawns[BLACK] = pawnAdvance(white | black, ~(black & pawns), WHITE);

    // Compute an area for evaluating our King's safety.
    // The definition of the King Area can be found in masks.c
    ei->kingSquare[WHITE] = getlsb(white & kings);
    ei->kingSquare[BLACK] = getlsb(black & kings);
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
    ei->pkentry = getCachedPawnKingEval(thread, board);
    ei->passedPawns = ei->pkentry == NULL ? 0ull : ei->pkentry->passed;
    ei->pkeval[WHITE] = ei->pkentry == NULL ? 0 : ei->pkentry->eval;
    ei->pkeval[BLACK] = ei->pkentry == NULL ? 0 : 0;
    ei->pksafety[WHITE] = ei->pkentry == NULL ? 0 : ei->pkentry->safetyw;
    ei->pksafety[BLACK] = ei->pkentry == NULL ? 0 : ei->pkentry->safetyb;
}

/// search.c

int LMRTable[64][64];
int LateMovePruningCounts[2][9];

volatile int ABORT_SIGNAL; // Global ABORT flag for threads
volatile int IS_PONDERING; // Global PONDER flag for threads
volatile int ANALYSISMODE; // Whether to make some changes for Analysis


static void select_from_threads(Thread* threads, uint16_t* best, uint16_t* ponder, int* score) {

    /// A thread is better than another if any are true:
    /// [1] The thread has an equal depth and greater score.
    /// [2] The thread has a mate score and is closer to mate.
    /// [3] The thread has a greater depth without replacing a closer mate

    Thread* best_thread = &threads[0];

    for (int i = 1; i < threads->nthreads; i++) {

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
    *best = best_thread->pvs[best_thread->completed].line[0];
    *ponder = best_thread->pvs[best_thread->completed].line[1];
    *score = best_thread->pvs[best_thread->completed].score;

    // Incomplete searches or low depth ones may result in a short PV
    if (best_thread->pvs[best_thread->completed].length < 2)
        *ponder = NONE_MOVE;

    // Report via UCI when our best thread is not the main thread
    if (best_thread != &threads[0]) {
        const int best_depth = best_thread->completed;
        best_thread->multiPV = 0;
        uciReport(best_thread, &best_thread->pvs[best_depth], -MATE, MATE);
    }
}

static void update_best_line(Thread* thread, PVariation* pv) {

    /// Upon finishing a depth, or reaching a fail-high, we update
    /// this Thread's line of best play for the newly completed depth.
    /// We store seperately the lines that we explore in multipv searches

    if (!thread->multiPV
        || pv->score > thread->pvs[thread->completed].score) {

        thread->completed = thread->depth;
        memcpy(&thread->pvs[thread->depth], pv, sizeof(PVariation));
    }

    memcpy(&thread->mpvs[thread->multiPV], pv, sizeof(PVariation));
}

static void revert_best_line(Thread* thread) {

    /// A fail-low during occured during the search, and therefore we need
    /// to remove any fail-highs that we may have originally marked as best
    /// lines, since we now believe the line to much worse than before

    if (!thread->multiPV)
        thread->completed = thread->depth - 1;
}

static void report_multipv_lines(Thread* thread) {

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

void* start_search_threads(void* arguments) 
{
    // Unpack the UCIGoStruct that was cast to void*
    Thread* threads = ((UCIGoStruct*)arguments)->threads;
    Board* board = ((UCIGoStruct*)arguments)->board;
    Limits* limits = &((UCIGoStruct*)arguments)->limits;

    int score;
    char str[6];
    uint16_t best = NONE_MOVE, ponder = NONE_MOVE;

    // Execute search, setting best and ponder moves
    getBestMove(threads, board, limits, &best, &ponder, &score);

    // UCI spec does not want reports until out of pondering
    while (IS_PONDERING);

    // Report best move ( we should always have one )
    moveToString(best, str, board->chess960);
    printf("bestmove %s", str);

    // Report ponder move ( if we have one )
    if (ponder != NONE_MOVE) {
        moveToString(ponder, str, board->chess960);
        printf(" ponder %s", str);
    }

    // Make sure this all gets reported
    printf("\n"); fflush(stdout);

    return NULL;
}

void getBestMove(Thread* threads, Board* board, Limits* limits, uint16_t* best, uint16_t* ponder, int* score) 
{
    vector<unique_ptr<thread>> pthreads(threads->nthreads);
    TimeManager tm = { 0 }; tm_init(limits, &tm);

    // Minor house keeping for starting a search
    tt_update(); // Table has an age component
    ABORT_SIGNAL = 0; // Otherwise Threads will exit
    newSearchThreadPool(threads, board, limits, &tm);

    // Allow Syzygy to refine the move list for optimal results
    if (!limits->limitedByMoves && limits->multiPV == 1)
        tablebasesProbeDTZ(board, limits);

    // Create a new thread for each of the helpers and reuse the current
    // thread for the main thread, which avoids some overhead and saves
    // us from having the current thread eating CPU time while waiting
    for (int i = 1; i < threads->nthreads; i++)
        pthreads[i].reset(new thread(&iterativeDeepening, &threads[i]));
    iterativeDeepening((void*)&threads[0]);

    // When the main thread exits it should signal for the helpers to
    // shutdown. Wait until all helpers have finished before moving on
    ABORT_SIGNAL = 1;
    for (int i = 1; i < threads->nthreads; i++)
        pthreads[i]->join();

    // Pick the best of our completed threads
    select_from_threads(threads, best, ponder, score);
}

void* iterativeDeepening(void* vthread) 
{
    Thread* const thread = (Thread*)vthread;
    TimeManager* const tm = thread->tm;
    Limits* const limits = thread->limits;
    const int mainThread = thread->index == 0;

    // Bind when we expect to deal with NUMA
    //if (thread->nthreads > 8)
    //    bindThisThread(thread->index);

    // Perform iterative deepening until exit conditions
    for (thread->depth = 1; thread->depth < MAX_PLY; thread->depth++) 
    {
        // If we abort to here, we stop searching
#ifdef _MSC_VER
        if (_setjmp(thread->jbuffer)) break;
#else
        if (setjmp(thread->jbuffer)) break;
#endif

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

    return NULL;
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

int search(Thread* thread, PVariation* pv, int alpha, int beta, int depth, bool cutnode) {

    Board* const board = &thread->board;
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
    if (depth <= 0 && !board->kingAttackers)
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
    if ((ABORT_SIGNAL && thread->depth > 1)
        || (tm_stop_early(thread) && !IS_PONDERING))
        longjmp(thread->jbuffer, 1);

    // Step 3. Check for early exit conditions. Don't take early exits in
    // the RootNode, since this would prevent us from having a best move
    if (!RootNode) {

        // Draw Detection. Check for the fifty move rule, repetition, or insufficient
        // material. Add variance to the draw score, to avoid blindness to 3-fold lines
        if (boardIsDrawn(board, thread->height)) return 1 - (thread->nodes & 2);

        // Check to see if we have exceeded the maxiumum search draft
        if (thread->height >= MAX_PLY)
            return board->kingAttackers ? 0 : evaluateBoard(thread, board);

        // Mate Distance Pruning. Check to see if this line is so
        // good, or so bad, that being mated in the ply, or  mating in
        // the next one, would still not create a more extreme line
        rAlpha = Max(alpha, -MATE + thread->height);
        rBeta = Min(beta, MATE - thread->height - 1);
        if (rAlpha >= rBeta) return rAlpha;
    }

    // Don't probe the TT or TB during singluar searches
    if (ns->excluded != NONE_MOVE)
        goto search_init_goto;

    // Step 4. Probe the Transposition Table, adjust the value, and consider cutoffs
    if ((ttHit = tt_probe(board->hash, thread->height, &ttMove, &ttValue, &ttEval, &ttDepth, &ttBound))) {

        // Only cut with a greater depth search, and do not return
        // when in a PvNode, unless we would otherwise hit a qsearch
        if (ttDepth >= depth
            && (depth == 0 || !PvNode)
            && (cutnode || ttValue <= alpha)) {

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
    // the conditions about the board, the existance of tables, the probe depth,
    // as well as to not probe at the Root. The return is defined by the Pyrrhic API
    if ((tbresult = tablebasesProbeWDL(board, depth, thread->height)) != TB_RESULT_FAILED) {

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

            tt_store(board->hash, thread->height, NONE_MOVE, value, VALUE_NONE, depth, tbBound);
            return value;
        }

        // Never score something worse than the known Syzygy value
        if (PvNode && tbBound == BOUND_LOWER)
            syzygyMin = value, alpha = Max(alpha, value);

        // Never score something better than the known Syzygy value
        if (PvNode && tbBound == BOUND_UPPER)
            syzygyMax = value;
    }

    // Step 6. Initialize flags and values used by pruning and search methods
search_init_goto:

    // We can grab in check based on the already computed king attackers bitboard
    inCheck = !!board->kingAttackers;

    // Save a history of the static evaluations when not checked
    eval = ns->eval = inCheck ? VALUE_NONE
        : ttEval != VALUE_NONE ? ttEval : evaluateBoard(thread, board);

    // Static Exchange Evaluation Pruning Margins
    seeMargin[0] = SEENoisyMargin * depth * depth;
    seeMargin[1] = SEEQuietMargin * depth;

    // Improving if our static eval increased in the last move
    improving = !inCheck && eval > (ns - 2)->eval;

    // Reset Killer moves for our children
    thread->killers[thread->height + 1][0] = NONE_MOVE;
    thread->killers[thread->height + 1][1] = NONE_MOVE;

    // Track the # of double extensions in this line
    ns->dextensions = RootNode ? 0 : (ns - 1)->dextensions;

    // Beta value for ProbCut Pruning
    rBeta = Min(beta + ProbCutMargin, MATE - MAX_PLY - 1);

    // Toss the static evaluation into the TT if we won't overwrite something
    if (!ttHit && !inCheck && !ns->excluded)
        tt_store(board->hash, thread->height, NONE_MOVE, VALUE_NONE, eval, 0, BOUND_NONE);

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
        && boardHasNonPawnMaterial(board, board->turn)
        && (!ttHit || !(ttBound & BOUND_UPPER) || ttValue >= beta)) {

        // Dynamic R based on Depth, Eval, and Tactical state
        R = 4 + depth / 6 + Min(3, (eval - beta) / 200) + (ns - 1)->tactical;

        apply(thread, board, NULL_MOVE);
        value = -search(thread, &lpv, -beta, -beta + 1, depth - R, !cutnode);
        revert(thread, board, NULL_MOVE);

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
            if (apply(thread, board, move)) {

                // For high depths, verify the move first with a qsearch
                if (depth >= 2 * ProbCutDepth)
                    value = -qsearch(thread, &lpv, -rBeta, -rBeta + 1);

                // For low depths, or after the above, verify with a reduced search
                if (depth < 2 * ProbCutDepth || value >= rBeta)
                    value = -search(thread, &lpv, -rBeta, -rBeta + 1, depth - 4, !cutnode);

                // Revert the board state
                revert(thread, board, move);

                // Store an entry if we don't have a better one already
                if (value >= rBeta && (!ttHit || ttDepth < depth - 3))
                    tt_store(board->hash, thread->height, move, value, eval, depth - 3, BOUND_LOWER);

                // Probcut failed high verifying the cutoff
                if (value >= rBeta) return value;
            }
        }
    }

    // Step 11. Internal Iterative Reductions. Artifically lower the depth on cutnodes
    // that are high enough up in the search tree that we would expect to have found
    // a Transposition. This is a modernized approach to Internal Iterative Deepening
    if (cutnode
        && depth >= 7
        && ttMove == NONE_MOVE)
        depth -= 1;

    // Step 12. Initialize the Move Picker and being searching through each
    // move one at a time, until we run out or a move generates a cutoff. We
    // reuse an already initialized MovePicker to verify Singular Extension
    if (!ns->excluded) init_picker(&ns->mp, thread, ttMove);
    while ((move = select_next(&ns->mp, thread, skipQuiets)) != NONE_MOVE) {

        const uint64_t starting_nodes = thread->nodes;

        // MultiPV and UCI searchmoves may limit our search options
        if (RootNode && moveExaminedByMultiPV(thread, move)) continue;
        if (RootNode && !moveIsInRootMoves(thread, move)) continue;

        // Track Moves Seen for Late Move Pruning
        movesSeen += 1;
        isQuiet = !moveIsTactical(board, move);

        // All moves have one or more History scores
        hist = !isQuiet ? get_capture_history(thread, move)
            : get_quiet_history(thread, move, &cmhist, &fmhist);

        // Step 13 (~80 elo). Late Move Pruning / Move Count Pruning. If we
        // have seen many moves in this position already, and we don't expect
        // anything from this move, we can skip all the remaining quiets
        if (best > -TBWIN_IN_MAX
            && depth <= LateMovePruningDepth
            && movesSeen >= LateMovePruningCounts[improving][depth])
            skipQuiets = 1;

        // Step 14 (~175 elo). Quiet Move Pruning. Prune any quiet move that meets one
        // of the criteria below, only after proving a non mated line exists
        if (isQuiet && best > -TBWIN_IN_MAX) {

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
            && !staticExchangeEvaluation(board, move, seeMargin[isQuiet]))
            continue;

        // Apply move, skip if move is illegal
        if (!apply(thread, board, move))
            continue;

        played += 1;
        if (isQuiet) quietsTried[quietsPlayed++] = move;
        else capturesTried[capturesPlayed++] = move;

        // The UCI spec allows us to output information about the current move
        // that we are going to search. We only do this from the main thread,
        // and we wait a few seconds in order to avoid floiding the output
        if (RootNode && !thread->index && elapsed_time(thread->tm) > CurrmoveTimerMS)
            uciReportCurrentMove(board, move, played + thread->multiPV, thread->depth);

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

        if (depth > 2 && played > 1) {

            // Step 18A (~249 elo). Quiet Late Move Reductions. Reduce the search depth
            // of Quiet moves after we've explored the main line. If a reduced search
            // manages to beat alpha, against our expectations, we perform a research

            if (isQuiet) {

                // Use the LMR Formula as a starting point
                R = LMRTable[Min(depth, 63)][Min(played, 63)];

                // Increase for non PV, non improving
                R += !PvNode + !improving;

                // Increase for King moves that evade checks
                R += inCheck && pieceType(board->squares[MoveTo(move)]) == KING;

                // Reduce for Killers and Counters
                R -= ns->mp.stage < STAGE_QUIET;

                // Adjust based on history scores
                R -= Max(-2, Min(2, hist / 5000));
            }

            // Step 18B (~3 elo). Noisy Late Move Reductions. The same as Step 18A, but
            // only applied to Tactical moves, based mostly on the Capture History scores

            else {

                // Initialize R based on Capture History
                R = 2 - (hist / 5000);

                // Reduce for moves that give check
                R -= !!board->kingAttackers;
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

        // Revert the board state
        revert(thread, board, move);

        // Reset the extension tracker
        if (extension > 1) ns->dextensions--;

        // Track where nodes were spent in the Main thread at the Root
        if (RootNode && !thread->index)
            thread->tm->nodes[move] += thread->nodes - starting_nodes;

        // Step 19. Update search stats for the best move and its value. Update
        // our lower bound (alpha) if exceeded, and also update the PV in that case
        if (value > best) {

            best = value;
            bestMove = move;

            if (value > alpha) {
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

    if (best >= beta && !moveIsTactical(board, bestMove))
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
        tt_store(board->hash, thread->height, bestMove, best, eval, depth, ttBound);
    }

    return best;
}

int qsearch(Thread* thread, PVariation* pv, int alpha, int beta) {

    Board* const board = &thread->board;
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
    if ((ABORT_SIGNAL && thread->depth > 1)
        || (tm_stop_early(thread) && !IS_PONDERING))
        longjmp(thread->jbuffer, 1);

    // Step 2. Draw Detection. Check for the fifty move rule, repetition, or insufficient
    // material. Add variance to the draw score, to avoid blindness to 3-fold lines
    if (boardIsDrawn(board, thread->height)) return 1 - (thread->nodes & 2);

    // Step 3. Max Draft Cutoff. If we are at the maximum search draft,
    // then end the search here with a static eval of the current board
    if (thread->height >= MAX_PLY)
        return evaluateBoard(thread, board);

    // Step 4. Probe the Transposition Table, adjust the value, and consider cutoffs
    if ((ttHit = tt_probe(board->hash, thread->height, &ttMove, &ttValue, &ttEval, &ttDepth, &ttBound))) {

        // Table is exact or produces a cutoff
        if (ttBound == BOUND_EXACT
            || (ttBound == BOUND_LOWER && ttValue >= beta)
            || (ttBound == BOUND_UPPER && ttValue <= alpha))
            return ttValue;
    }

    // Save a history of the static evaluations
    eval = ns->eval = ttEval != VALUE_NONE
        ? ttEval : evaluateBoard(thread, board);

    // Toss the static evaluation into the TT if we won't overwrite something
    if (!ttHit && !board->kingAttackers)
        tt_store(board->hash, thread->height, NONE_MOVE, VALUE_NONE, eval, 0, BOUND_NONE);

    // Step 5. Eval Pruning. If a static evaluation of the board will
    // exceed beta, then we can stop the search here. Also, if the static
    // eval exceeds alpha, we can call our static eval the new alpha
    best = eval;
    alpha = Max(alpha, eval);
    if (alpha >= beta) return eval;

    // Step 6. Delta Pruning. Even the best possible capture and or promotion
    // combo, with a minor boost for pawn captures, would still fail to cover
    // the distance between alpha and the evaluation. Playing a move is futile.
    if (Max(QSDeltaMargin, moveBestCaseValue(board)) < alpha - eval)
        return eval;

    // Step 7. Move Generation and Looping. Generate all tactical moves
    // and return those which are winning via SEE, and also strong enough
    // to beat the margin computed in the Delta Pruning step found above
    init_noisy_picker(&ns->mp, thread, NONE_MOVE, Max(1, alpha - eval - QSSeeMargin));
    while ((move = select_next(&ns->mp, thread, 1)) != NONE_MOVE) {

        // Worst case which assumes we lose our piece immediately
        int pessimism = moveEstimatedValue(board, move)
            - SEEPieceValues[pieceType(board->squares[MoveFrom(move)])];

        // Search the next ply if the move is legal
        if (!apply(thread, board, move)) continue;

        // Short-circuit QS and assume a stand-pat matches the SEE
        if (eval + pessimism > beta && abs(eval + pessimism) < MATE / 2) {
            revert(thread, board, move);
            pv->length = 1;
            pv->line[0] = move;
            return beta;
        }

        value = -qsearch(thread, &lpv, -beta, -alpha);
        revert(thread, board, move);

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
    ttBound = best >= beta ? BOUND_LOWER
        : best > oldAlpha ? BOUND_EXACT : BOUND_UPPER;
    tt_store(board->hash, thread->height, bestMove, best, eval, 0, ttBound);

    return best;
}

int staticExchangeEvaluation(Board* board, uint16_t move, int threshold) {

    int from, to, type, colour, balance, nextVictim;
    uint64_t bishops, rooks, occupied, attackers, myAttackers;

    // Unpack move information
    from = MoveFrom(move);
    to = MoveTo(move);
    type = MoveType(move);

    // Next victim is moved piece or promotion type
    nextVictim = type != PROMOTION_MOVE
        ? pieceType(board->squares[from])
        : MovePromoPiece(move);

    // Balance is the value of the move minus threshold. Function
    // call takes care for Enpass, Promotion and Castling moves.
    balance = moveEstimatedValue(board, move) - threshold;

    // Best case still fails to beat the threshold
    if (balance < 0) return 0;

    // Worst case is losing the moved piece
    balance -= SEEPieceValues[nextVictim];

    // If the balance is positive even if losing the moved piece,
    // the exchange is guaranteed to beat the threshold.
    if (balance >= 0) return 1;

    // Grab sliders for updating revealed attackers
    bishops = board->pieces[BISHOP] | board->pieces[QUEEN];
    rooks = board->pieces[ROOK] | board->pieces[QUEEN];

    // Let occupied suppose that the move was actually made
    occupied = (board->colours[WHITE] | board->colours[BLACK]);
    occupied = (occupied ^ (1ull << from)) | (1ull << to);
    if (type == ENPASS_MOVE) occupied ^= (1ull << board->epSquare);

    // Get all pieces which attack the target square. And with occupied
    // so that we do not let the same piece attack twice
    attackers = allAttackersToSquare(board, occupied, to) & occupied;

    // Now our opponents turn to recapture
    colour = !board->turn;

    while (1) {

        // If we have no more attackers left we lose
        myAttackers = attackers & board->colours[colour];
        if (myAttackers == 0ull) break;

        // Find our weakest piece to attack with
        for (nextVictim = PAWN; nextVictim <= QUEEN; nextVictim++)
            if (myAttackers & board->pieces[nextVictim])
                break;

        // Remove this attacker from the occupied
        occupied ^= (1ull << getlsb(myAttackers & board->pieces[nextVictim]));

        // A diagonal move may reveal bishop or queen attackers
        if (nextVictim == PAWN || nextVictim == BISHOP || nextVictim == QUEEN)
            attackers |= bishopAttacks(to, occupied) & bishops;

        // A vertical or horizontal move may reveal rook or queen attackers
        if (nextVictim == ROOK || nextVictim == QUEEN)
            attackers |= rookAttacks(to, occupied) & rooks;

        // Make sure we did not add any already used attacks
        attackers &= occupied;

        // Swap the turn
        colour = !colour;

        // Negamax the balance and add the value of the next victim
        balance = -balance - 1 - SEEPieceValues[nextVictim];

        // If the balance is non negative after giving away our piece then we win
        if (balance >= 0) {

            // As a slide speed up for move legality checking, if our last attacking
            // piece is a king, and our opponent still has attackers, then we've
            // lost as the move we followed would be illegal
            if (nextVictim == KING && (attackers & board->colours[colour]))
                colour = !colour;

            break;
        }
    }

    // Side to move after the loop loses
    return board->turn != colour;
}

int singularity(Thread* thread, uint16_t ttMove, int ttValue, int depth, int PvNode, int alpha, int beta, bool cutnode) {

    Board* const board = &thread->board;
    NodeState* const ns = &thread->states[thread->height - 1];

    PVariation lpv; lpv.length = 0;
    int value, rBeta = Max(ttValue - depth, -MATE);

    // Table move was already applied
    revert(thread, board, ttMove);

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
    else applyLegal(thread, board, ttMove);

    bool double_extend = !PvNode
        && value < rBeta - 15
        && (ns - 1)->dextensions <= 6;

    return double_extend ? 2 // Double extension in some non-pv nodes
        : value < rBeta ? 1 // Singular due to no cutoffs produced
        : ttValue >= beta ? -1 // Potential multi-cut even at current depth
        : ttValue <= alpha ? -1 // Negative extension if ttValue was already failing-low
        : 0;                    // Not singular, and unlikely to produce a cutoff
}


/// transposition.c

TTable Table; // Global Transposition Table

/// Mate and Tablebase scores need to be adjusted relative to the Root
/// when going into the Table and when coming out of the Table. Otherwise,
/// we will not know when we have a "faster" vs "slower" Mate or TB Win/Loss

static int tt_value_from(int value, int height) {
    return value == VALUE_NONE ? VALUE_NONE
        : value >= TBWIN_IN_MAX ? value - height
        : value <= -TBWIN_IN_MAX ? value + height : value;
}

static int tt_value_to(int value, int height) {
    return value == VALUE_NONE ? VALUE_NONE
        : value >= TBWIN_IN_MAX ? value + height
        : value <= -TBWIN_IN_MAX ? value - height : value;
}


/// Trivial helper functions to Transposition Table handleing

void tt_update() { Table.generation += TT_MASK_BOUND + 1; }
void tt_prefetch(uint64_t hash) { Prefetch<2>(reinterpret_cast<const char*>(&Table.buckets[hash & Table.hashMask])); }


int tt_init(size_t nthreads, int megabytes) 
{
    const uint64_t MB = 1ull << 20;
    uint64_t keySize = 16ull;

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

int tt_hashfull() {

    /// Estimate the permill of the table being used, by looking at a thousand
    /// Buckets and seeing how many Entries contain a recent Transposition.

    int used = 0;

    for (int i = 0; i < 1000; i++)
        for (int j = 0; j < TT_BUCKET_NB; j++)
            used += (Table.buckets[i].slots[j].generation & TT_MASK_BOUND) != BOUND_NONE
            && (Table.buckets[i].slots[j].generation & TT_MASK_AGE) == Table.generation;

    return used / TT_BUCKET_NB;
}

bool tt_probe(uint64_t hash, int height, uint16_t* move, int* value, int* eval, int* depth, int* bound) {

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

void tt_store(uint64_t hash, int height, uint16_t move, int value, int eval, int depth, int bound) {

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
    replace->value = (int16_t)tt_value_to(value, height);
    replace->eval = (int16_t)eval;
    replace->hash16 = (uint16_t)hash16;
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

void* tt_clear_threaded(void* cargo) {

    const uint64_t MB = 1ull << 20;
    struct TTClear* ttclear = (struct TTClear*)cargo;

    // Logic for dividing the Table taken from Weiss and CFish
    const uint64_t size = (Table.hashMask + 1) * sizeof(TTBucket);
    const uint64_t slice = (size + ttclear->count - 1) / ttclear->count;
    const uint64_t blocks = (slice + 2 * MB - 1) / (2 * MB);
    const uint64_t begin = Min(size, ttclear->index * blocks * 2 * MB);
    const uint64_t end = Min(size, begin + blocks * 2 * MB);

    memset(&Table.buckets[0] + begin / sizeof(TTBucket), 0, end - begin);
    return NULL;
}

/// Simple Pawn+King Evaluation Hash Table, which also stores some additional
/// safety information for use in King Safety, when not using NNUE evaluations

PKEntry* getCachedPawnKingEval(Thread* thread, const Board* board) {
    PKEntry* pke = &thread->pktable[board->pkhash & PK_CACHE_MASK];
    return pke->pkhash == board->pkhash ? pke : NULL;
}

void storeCachedPawnKingEval(Thread* thread, const Board* board, uint64_t passed, int eval, int safety[2]) {
    PKEntry& pke = thread->pktable[board->pkhash & PK_CACHE_MASK];
    pke = { board->pkhash, passed, eval, safety[WHITE], safety[BLACK] };
}


/// attacks.c


#ifdef USE_PEXT
#include <immintrin.h>
#endif

ALIGN64 uint64_t PawnAttacks[N_COLORS][N_SQUARES];
ALIGN64 uint64_t KnightAttacks[N_SQUARES];
ALIGN64 uint64_t BishopAttacks[0x1480];
ALIGN64 uint64_t RookAttacks[0x19000];
ALIGN64 uint64_t KingAttacks[N_SQUARES];

ALIGN64 Magic BishopTable[N_SQUARES];
ALIGN64 Magic RookTable[N_SQUARES];

static int validCoordinate(int rank, int file) {
    return 0 <= rank && rank < N_RANKS
        && 0 <= file && file < N_FILES;
}

static void setSquare(uint64_t* bb, int rank, int file) {
    if (validCoordinate(rank, file))
        *bb |= 1ull << square(rank, file);
}

static int sliderIndex(uint64_t occupied, Magic* table) 
{
#ifdef USE_PEXT
    return _pext_u64(occupied, table->mask);
#else
    return static_cast<int>(((occupied & table->mask) * table->magic) >> table->shift);
#endif
}

static uint64_t sliderAttacks(int sq, uint64_t occupied, const int delta[4][2]) {

    int rank, file, dr, df;
    uint64_t result = 0ull;

    for (int i = 0; i < 4; i++) {

        dr = delta[i][0], df = delta[i][1];

        for (rank = rankOf(sq) + dr, file = fileOf(sq) + df; validCoordinate(rank, file); rank += dr, file += df) {
            setBit(&result, square(rank, file));
            if (testBit(occupied, square(rank, file)))
                break;
        }
    }

    return result;
}

static void initSliderAttacks(int sq, Magic* table, uint64_t magic, const int delta[4][2]) 
{
    uint64_t edges = ((RANK_1 | RANK_8) & ~Ranks[rankOf(sq)])
        | ((FILE_A | FILE_H) & ~Files[fileOf(sq)]);

    uint64_t occupied = 0ull;

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


void initAttacks() {

    const int PawnDelta[2][2] = { { 1,-1}, { 1, 1} };
    const int KnightDelta[8][2] = { {-2,-1}, {-2, 1}, {-1,-2}, {-1, 2},{ 1,-2}, { 1, 2}, { 2,-1}, { 2, 1} };
    const int KingDelta[8][2] = { {-1,-1}, {-1, 0}, {-1, 1}, { 0,-1},{ 0, 1}, { 1,-1}, { 1, 0}, { 1, 1} };
    const int BishopDelta[4][2] = { {-1,-1}, {-1, 1}, { 1,-1}, { 1, 1} };
    const int RookDelta[4][2] = { {-1, 0}, { 0,-1}, { 0, 1}, { 1, 0} };

    // First square has initial offset
    BishopTable[0].offset = BishopAttacks;
    RookTable[0].offset = RookAttacks;

    // Init attack tables for Pawns
    for (int sq = 0; sq < 64; sq++) {
        for (int dir = 0; dir < 2; dir++) {
            setSquare(&PawnAttacks[WHITE][sq], rankOf(sq) + PawnDelta[dir][0], fileOf(sq) + PawnDelta[dir][1]);
            setSquare(&PawnAttacks[BLACK][sq], rankOf(sq) - PawnDelta[dir][0], fileOf(sq) - PawnDelta[dir][1]);
        }
    }

    // Init attack tables for Knights & Kings
    for (int sq = 0; sq < 64; sq++) {
        for (int dir = 0; dir < 8; dir++) {
            setSquare(&KnightAttacks[sq], rankOf(sq) + KnightDelta[dir][0], fileOf(sq) + KnightDelta[dir][1]);
            setSquare(&KingAttacks[sq], rankOf(sq) + KingDelta[dir][0], fileOf(sq) + KingDelta[dir][1]);
        }
    }

    // Init attack tables for sliding pieces
    for (int sq = 0; sq < 64; sq++) {
        initSliderAttacks(sq, BishopTable, BishopMagics[sq], BishopDelta);
        initSliderAttacks(sq, RookTable, RookMagics[sq], RookDelta);
    }
}

uint64_t pawnAttacks(int colour, int sq) {
    assert(0 <= colour && colour < N_COLORS);
    assert(0 <= sq && sq < N_SQUARES);
    return PawnAttacks[colour][sq];
}

uint64_t knightAttacks(int sq) {
    assert(0 <= sq && sq < N_SQUARES);
    return KnightAttacks[sq];
}

uint64_t bishopAttacks(int sq, uint64_t occupied) {
    assert(0 <= sq && sq < N_SQUARES);
    return BishopTable[sq].offset[sliderIndex(occupied, &BishopTable[sq])];
}

uint64_t rookAttacks(int sq, uint64_t occupied) {
    assert(0 <= sq && sq < N_SQUARES);
    return RookTable[sq].offset[sliderIndex(occupied, &RookTable[sq])];
}

uint64_t queenAttacks(int sq, uint64_t occupied) {
    assert(0 <= sq && sq < N_SQUARES);
    return bishopAttacks(sq, occupied) | rookAttacks(sq, occupied);
}

uint64_t kingAttacks(int sq) {
    assert(0 <= sq && sq < N_SQUARES);
    return KingAttacks[sq];
}


uint64_t pawnLeftAttacks(uint64_t pawns, uint64_t targets, int colour) {
    return targets & (colour == WHITE ? (pawns << 7) & ~FILE_H
        : (pawns >> 7) & ~FILE_A);
}

uint64_t pawnRightAttacks(uint64_t pawns, uint64_t targets, int colour) {
    return targets & (colour == WHITE ? (pawns << 9) & ~FILE_A
        : (pawns >> 9) & ~FILE_H);
}

uint64_t pawnAttackSpan(uint64_t pawns, uint64_t targets, int colour) {
    return pawnLeftAttacks(pawns, targets, colour)
        | pawnRightAttacks(pawns, targets, colour);
}

uint64_t pawnAttackDouble(uint64_t pawns, uint64_t targets, int colour) {
    return pawnLeftAttacks(pawns, targets, colour)
        & pawnRightAttacks(pawns, targets, colour);
}

uint64_t pawnAdvance(uint64_t pawns, uint64_t occupied, int colour) {
    return ~occupied & (colour == WHITE ? (pawns << 8) : (pawns >> 8));
}

uint64_t pawnEnpassCaptures(uint64_t pawns, int epsq, int colour) {
    return epsq == -1 ? 0ull : pawnAttacks(!colour, epsq) & pawns;
}


int squareIsAttacked(Board* board, int colour, int sq) {

    uint64_t enemy = board->colours[!colour];
    uint64_t occupied = board->colours[colour] | enemy;

    uint64_t enemyPawns = enemy & board->pieces[PAWN];
    uint64_t enemyKnights = enemy & board->pieces[KNIGHT];
    uint64_t enemyBishops = enemy & (board->pieces[BISHOP] | board->pieces[QUEEN]);
    uint64_t enemyRooks = enemy & (board->pieces[ROOK] | board->pieces[QUEEN]);
    uint64_t enemyKings = enemy & board->pieces[KING];

    // Check for attacks to this square. While this function has the same
    // result as using attackersToSquare(board, colour, sq) != 0ull, this
    // has a better running time by avoiding some slider move lookups. The
    // speed gain is easily proven using the provided PERFT suite

    return (pawnAttacks(colour, sq) & enemyPawns)
        || (knightAttacks(sq) & enemyKnights)
        || (enemyBishops && (bishopAttacks(sq, occupied) & enemyBishops))
        || (enemyRooks && (rookAttacks(sq, occupied) & enemyRooks))
        || (kingAttacks(sq) & enemyKings);
}

uint64_t allAttackersToSquare(Board* board, uint64_t occupied, int sq) {

    // When performing a static exchange evaluation we need to find all
    // attacks to a given square, but we also are given an updated occupied
    // bitboard, which will likely not match the actual board, as pieces are
    // removed during the iterations in the static exchange evaluation

    return (pawnAttacks(WHITE, sq) & board->colours[BLACK] & board->pieces[PAWN])
        | (pawnAttacks(BLACK, sq) & board->colours[WHITE] & board->pieces[PAWN])
        | (knightAttacks(sq) & board->pieces[KNIGHT])
        | (bishopAttacks(sq, occupied) & (board->pieces[BISHOP] | board->pieces[QUEEN]))
        | (rookAttacks(sq, occupied) & (board->pieces[ROOK] | board->pieces[QUEEN]))
        | (kingAttacks(sq) & board->pieces[KING]);
}

uint64_t allAttackedSquares(Board* board, int colour) {

    uint64_t friendly = board->colours[colour];
    uint64_t occupied = board->colours[!colour] | friendly;

    uint64_t pawns = friendly & board->pieces[PAWN];
    uint64_t knights = friendly & board->pieces[KNIGHT];
    uint64_t bishops = friendly & (board->pieces[BISHOP] | board->pieces[QUEEN]);
    uint64_t rooks = friendly & (board->pieces[ROOK] | board->pieces[QUEEN]);
    uint64_t kings = friendly & board->pieces[KING];

    uint64_t threats = pawnAttackSpan(pawns, ~0ULL, colour);
    while (knights) threats |= knightAttacks(poplsb(&knights));
    while (bishops) threats |= bishopAttacks(poplsb(&bishops), occupied);
    while (rooks)   threats |= rookAttacks(poplsb(&rooks), occupied);
    while (kings)   threats |= kingAttacks(poplsb(&kings));

    return threats;
}

uint64_t attackersToKingSquare(Board* board) {

    // Wrapper for allAttackersToSquare() for use in check detection
    int kingsq = getlsb(board->colours[board->turn] & board->pieces[KING]);
    uint64_t occupied = board->colours[WHITE] | board->colours[BLACK];
    return allAttackersToSquare(board, occupied, kingsq) & board->colours[!board->turn];
}

uint64_t discoveredAttacks(Board* board, int sq, int US) {

    uint64_t enemy = board->colours[!US];
    uint64_t occupied = board->colours[US] | enemy;

    uint64_t rAttacks = rookAttacks(sq, occupied);
    uint64_t bAttacks = bishopAttacks(sq, occupied);

    uint64_t rooks = (enemy & board->pieces[ROOK]) & ~rAttacks;
    uint64_t bishops = (enemy & board->pieces[BISHOP]) & ~bAttacks;

    return (rooks & rookAttacks(sq, occupied & ~rAttacks))
        | (bishops & bishopAttacks(sq, occupied & ~bAttacks));
}


/// movegen.c


typedef uint64_t(*JumperFunc)(int);
typedef uint64_t(*SliderFunc)(int, uint64_t);

uint16_t* buildEnpassMoves(uint16_t* moves, uint64_t attacks, int epsq) {

    while (attacks)
        *(moves++) = MoveMake(poplsb(&attacks), epsq, ENPASS_MOVE);

    return moves;
}

uint16_t* buildPawnMoves(uint16_t* moves, uint64_t attacks, int delta) {

    while (attacks) {
        int sq = poplsb(&attacks);
        *(moves++) = MoveMake(sq + delta, sq, NORMAL_MOVE);
    }

    return moves;
}

uint16_t* buildPawnPromotions(uint16_t* moves, uint64_t attacks, int delta) {

    while (attacks) {
        int sq = poplsb(&attacks);
        *(moves++) = MoveMake(sq + delta, sq, QUEEN_PROMO_MOVE);
        *(moves++) = MoveMake(sq + delta, sq, ROOK_PROMO_MOVE);
        *(moves++) = MoveMake(sq + delta, sq, BISHOP_PROMO_MOVE);
        *(moves++) = MoveMake(sq + delta, sq, KNIGHT_PROMO_MOVE);
    }

    return moves;
}

uint16_t* buildNormalMoves(uint16_t* moves, uint64_t attacks, int sq) {

    while (attacks)
        *(moves++) = MoveMake(sq, poplsb(&attacks), NORMAL_MOVE);

    return moves;
}

uint16_t* buildJumperMoves(JumperFunc F, uint16_t* moves, uint64_t pieces, uint64_t targets) {

    while (pieces) {
        int sq = poplsb(&pieces);
        moves = buildNormalMoves(moves, F(sq) & targets, sq);
    }

    return moves;
}

uint16_t* buildSliderMoves(SliderFunc F, uint16_t* moves, uint64_t pieces, uint64_t targets, uint64_t occupied) {

    while (pieces) {
        int sq = poplsb(&pieces);
        moves = buildNormalMoves(moves, F(sq, occupied) & targets, sq);
    }

    return moves;
}


ptrdiff_t genAllLegalMoves(Board* board, uint16_t* moves) 
{
    Undo undo[1];
    int size = 0;
    uint16_t pseudoMoves[MAX_MOVES];

    // Call genAllNoisyMoves() & genAllNoisyMoves()
    ptrdiff_t pseudo = genAllNoisyMoves(board, pseudoMoves);
    pseudo += genAllQuietMoves(board, pseudoMoves + pseudo);

    // Check each move for legality before copying
    for (int i = 0; i < pseudo; i++) {
        applyMove(board, pseudoMoves[i], undo);
        if (moveWasLegal(board)) moves[size++] = pseudoMoves[i];
        revertMove(board, pseudoMoves[i], undo);
    }

    return size;
}

ptrdiff_t genAllNoisyMoves(Board* board, uint16_t* moves) 
{
    const uint16_t* start = moves;

    const int Left = board->turn == WHITE ? -7 : 7;
    const int Right = board->turn == WHITE ? -9 : 9;
    const int Forward = board->turn == WHITE ? -8 : 8;

    uint64_t destinations, pawnEnpass, pawnLeft, pawnRight;
    uint64_t pawnPromoForward, pawnPromoLeft, pawnPromoRight;

    uint64_t us = board->colours[board->turn];
    uint64_t them = board->colours[!board->turn];
    uint64_t occupied = us | them;

    uint64_t pawns = us & (board->pieces[PAWN]);
    uint64_t knights = us & (board->pieces[KNIGHT]);
    uint64_t bishops = us & (board->pieces[BISHOP]);
    uint64_t rooks = us & (board->pieces[ROOK]);
    uint64_t kings = us & (board->pieces[KING]);

    // Merge together duplicate piece ideas
    bishops |= us & board->pieces[QUEEN];
    rooks |= us & board->pieces[QUEEN];

    // Double checks can only be evaded by moving the King
    if (several(board->kingAttackers))
        return buildJumperMoves(&kingAttacks, moves, kings, them) - start;

    // When checked, we may only uncheck by capturing the checker
    destinations = board->kingAttackers ? board->kingAttackers : them;

    // Compute bitboards for each type of Pawn movement
    pawnEnpass = pawnEnpassCaptures(pawns, board->epSquare, board->turn);
    pawnLeft = pawnLeftAttacks(pawns, them, board->turn);
    pawnRight = pawnRightAttacks(pawns, them, board->turn);
    pawnPromoForward = pawnAdvance(pawns, occupied, board->turn) & PROMOTION_RANKS;
    pawnPromoLeft = pawnLeft & PROMOTION_RANKS; pawnLeft &= ~PROMOTION_RANKS;
    pawnPromoRight = pawnRight & PROMOTION_RANKS; pawnRight &= ~PROMOTION_RANKS;

    // Generate moves for all the Pawns, so long as they are noisy
    moves = buildEnpassMoves(moves, pawnEnpass, board->epSquare);
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

ptrdiff_t genAllQuietMoves(Board* board, uint16_t* moves) 
{
    const uint16_t* start = moves;

    const int Forward = board->turn == WHITE ? -8 : 8;
    const uint64_t Rank3Relative = board->turn == WHITE ? RANK_3 : RANK_6;

    int rook, king, rookTo, kingTo, attacked;
    uint64_t destinations, pawnForwardOne, pawnForwardTwo, mask;

    uint64_t us = board->colours[board->turn];
    uint64_t occupied = us | board->colours[!board->turn];
    uint64_t castles = us & board->castleRooks;

    uint64_t pawns = us & (board->pieces[PAWN]);
    uint64_t knights = us & (board->pieces[KNIGHT]);
    uint64_t bishops = us & (board->pieces[BISHOP]);
    uint64_t rooks = us & (board->pieces[ROOK]);
    uint64_t kings = us & (board->pieces[KING]);

    // Merge together duplicate piece ideas
    bishops |= us & board->pieces[QUEEN];
    rooks |= us & board->pieces[QUEEN];

    // Double checks can only be evaded by moving the King
    if (several(board->kingAttackers))
        return buildJumperMoves(&kingAttacks, moves, kings, ~occupied) - start;

    // When checked, we must block the checker with non-King pieces
    destinations = !board->kingAttackers ? ~occupied
        : bitsBetweenMasks(getlsb(kings), getlsb(board->kingAttackers));

    // Compute bitboards for each type of Pawn movement
    pawnForwardOne = pawnAdvance(pawns, occupied, board->turn) & ~PROMOTION_RANKS;
    pawnForwardTwo = pawnAdvance(pawnForwardOne & Rank3Relative, occupied, board->turn);

    // Generate moves for all the pawns, so long as they are quiet
    moves = buildPawnMoves(moves, pawnForwardOne & destinations, Forward);
    moves = buildPawnMoves(moves, pawnForwardTwo & destinations, Forward * 2);

    // Generate moves for the remainder of the pieces, so long as they are quiet
    moves = buildJumperMoves(&knightAttacks, moves, knights, destinations);
    moves = buildSliderMoves(&bishopAttacks, moves, bishops, destinations, occupied);
    moves = buildSliderMoves(&rookAttacks, moves, rooks, destinations, occupied);
    moves = buildJumperMoves(&kingAttacks, moves, kings, ~occupied);

    // Attempt to generate a castle move for each rook
    while (castles && !board->kingAttackers) {

        // Figure out which pieces are moving to which squares
        rook = poplsb(&castles), king = getlsb(kings);
        rookTo = castleRookTo(king, rook);
        kingTo = castleKingTo(king, rook);
        attacked = 0;

        // Castle is illegal if we would go over a piece
        mask = bitsBetweenMasks(king, kingTo) | (1ull << kingTo);
        mask |= bitsBetweenMasks(rook, rookTo) | (1ull << rookTo);
        mask &= ~((1ull << king) | (1ull << rook));
        if (occupied & mask) continue;

        // Castle is illegal if we move through a checking threat
        mask = bitsBetweenMasks(king, kingTo);
        while (mask)
            if (squareIsAttacked(board, board->turn, poplsb(&mask)))
            {
                attacked = 1; break;
            }
        if (attacked) continue;

        // All conditions have been met. Identify which side we are castling to
        *(moves++) = MoveMake(king, rook, CASTLE_MOVE);
    }

    return moves - start;
}



/// pgn.h


enum { PGN_LOSS, PGN_DRAW, PGN_WIN, PGN_NO_RESULT, PGN_UNKNOWN_RESULT };

typedef struct PGNData {
    char* startpos;
    bool is_white, is_black;
    int result, plies;
    char buffer[65536];
} PGNData;

void process_pgn(const char* fin, const char* fout);


/// pgn.c


/// Ethereal's NNUE Data Format

typedef struct HalfKPSample {
    uint64_t occupied;   // 8-byte occupancy bitboard ( No Kings )
    int16_t  eval;       // 2-byte int for the target evaluation
    uint8_t  result;     // 1-byte int for result. { L=0, D=1, W=2 }
    uint8_t  turn;       // 1-byte int for the side-to-move flag
    uint8_t  wking;      // 1-byte int for the White King Square
    uint8_t  bking;      // 1-byte int for the Black King Square
    uint8_t  packed[15]; // 1-byte int per two non-King pieces
} HalfKPSample;

static void pack_bitboard(uint8_t* packed, Board* board, uint64_t pieces) {

#define encode_piece(p) (8 * pieceColour(p) + pieceType(p))
#define pack_pieces(p1, p2) (((p1) << 4) | (p2))

    uint8_t types[32] = { 0 };
    int N = (1 + popcount(pieces)) / 2;

    for (int i = 0; pieces; i++) {
        int sq = poplsb(&pieces);
        types[i] = encode_piece(board->squares[sq]);
    }

    for (int i = 0; i < N; i++)
        packed[i] = pack_pieces(types[i * 2], types[i * 2 + 1]);

#undef encode_piece
#undef pack_pieces
}

static void build_halfkp_sample(Board* board, HalfKPSample* sample, unsigned result, int16_t eval) {

    const uint64_t white = board->colours[WHITE];
    const uint64_t black = board->colours[BLACK];
    const uint64_t pieces = (white | black);

    sample->occupied = pieces & ~board->pieces[KING];
    sample->eval = board->turn == BLACK ? -eval : eval;
    sample->result = board->turn == BLACK ? 2u - result : result;
    sample->turn = board->turn;
    sample->wking = getlsb(white & board->pieces[KING]);
    sample->bking = getlsb(black & board->pieces[KING]);
    pack_bitboard(sample->packed, board, sample->occupied);
}


static bool san_is_file(char chr) {
    return 'a' <= chr && chr <= 'h';
}

static bool san_is_rank(char chr) {
    return '1' <= chr && chr <= '8';
}

static bool san_is_square(const char* SAN) {
    return san_is_file(SAN[0]) && san_is_rank(SAN[1]);
}


static bool san_has_promotion(const char* SAN) {
    for (const char* ptr = SAN; *ptr != '\0' && *ptr != ' '; ptr++)
        if (*ptr == '=') return true;
    return false;
}

static bool san_has_capture(const char* SAN) {
    for (const char* ptr = SAN; *ptr != '\0' && *ptr != ' '; ptr++)
        if (*ptr == 'x') return true;
    return false;
}

static int san_square(const char* str) {
    return 8 * (str[1] - '1') + (str[0] - 'a');
}

static int san_promotion_type(char chr) {

    switch (chr) {
    case 'N': return KNIGHT_PROMO_MOVE;
    case 'B': return BISHOP_PROMO_MOVE;
    case 'R': return ROOK_PROMO_MOVE;
    default: return QUEEN_PROMO_MOVE;
    }
}


static uint16_t san_pawn_push(Board* board, const char* SAN) {

    int to, from, type;

    if (!san_is_square(SAN))
        return NONE_MOVE;

    // Assume a single pawn push
    to = san_square(SAN);
    from = board->turn == WHITE ? to - 8 : to + 8;

    // Promotion is entirely handled by a move flag
    type = san_has_promotion(SAN)
        ? san_promotion_type(SAN[3]) : NORMAL_MOVE;

    // Account for double pawn pushes
    if (board->squares[from] != makePiece(PAWN, board->turn))
        from = board->turn == WHITE ? from - 8 : from + 8;

    // We can assert legality later
    return MoveMake(from, to, type);
}

static uint16_t san_pawn_capture(Board* board, const char* SAN) {

    uint64_t pawns;
    int file, tosq, type;

    // Pawn Captures have a file and then an 'x'
    if (!san_is_file(SAN[0]) || !san_has_capture(SAN))
        return NONE_MOVE;

    // Their could be a rank given for the moving piece (???)
    file = SAN[0] - 'a';
    tosq = san_square(SAN + (SAN[1] != 'x') + 2);

    // If we capture "nothing", then we really En Passant
    if (board->squares[tosq] == EMPTY) {
        int rank = board->turn == WHITE ? 4 : 3;
        return MoveMake(8 * rank + file, board->epSquare, ENPASS_MOVE);
    }

    // Promotion is entirely handled by a move flag
    type = !san_has_promotion(SAN) ? NORMAL_MOVE
        : san_promotion_type(SAN[(SAN[1] != 'x') + 5]);

    // Narrow down the position of the capturing Pawn
    pawns = Files[file]
        & board->pieces[PAWN]
        & board->colours[board->turn]
        & pawnAttacks(!board->turn, tosq);

    return MoveMake(getlsb(pawns), tosq, type);
}

static uint16_t san_castle_move(Board* board, const char* SAN) {

    // Trivially check and build Queen Side Castles
    if (!strncmp(SAN, "O-O-O", 5)) {
        uint64_t friendly = board->colours[board->turn];
        int king = getlsb(friendly & board->pieces[KING]);
        int rook = getlsb(friendly & board->castleRooks);
        return MoveMake(king, rook, CASTLE_MOVE);
    }

    // Trivially check and build King Side Castles
    if (!strncmp(SAN, "O-O", 3)) {
        uint64_t friendly = board->colours[board->turn];
        int king = getlsb(friendly & board->pieces[KING]);
        int rook = getmsb(friendly & board->castleRooks);
        return MoveMake(king, rook, CASTLE_MOVE);
    }

    return NONE_MOVE;
}

static uint16_t san_piece_move(Board* board, const char* SAN) {

    int piece, tosq = -1;
    bool has_file, has_rank, has_capt;
    uint64_t options, occupied;

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

    occupied = board->colours[WHITE] | board->colours[BLACK];

    options = piece == KING ? kingAttacks(tosq)
        : piece == QUEEN ? queenAttacks(tosq, occupied)
        : piece == ROOK ? rookAttacks(tosq, occupied)
        : piece == BISHOP ? bishopAttacks(tosq, occupied)
        : piece == KNIGHT ? knightAttacks(tosq) : 0ull;

    options &= board->colours[board->turn] & board->pieces[piece];

    // Narrow down our options using the file disambiguation
    if (has_file)
        options &= Files[SAN[1] - 'a'];

    // Narrow down our options using the rank disambiguation
    if (has_rank)
        options &= Ranks[SAN[1 + has_file] - '1'];

    // If we only have one option, we can delay the legality check
    if (onlyOne(options))
        return MoveMake(getlsb(options), tosq, NORMAL_MOVE);

    // If we have multiple options due to pins, we must verify now
    while (options) {
        uint16_t move = MoveMake(poplsb(&options), tosq, NORMAL_MOVE);
        if (moveIsLegal(board, move)) return move;
    }

    // This should never happen, based on the call order of parse_san()
    return NONE_MOVE;
}

static uint16_t parse_san(Board* board, const char* SAN) {

    uint16_t move = NONE_MOVE;

    // Keep trying to parse the move until success or out of attempts
    if (move == NONE_MOVE) move = san_pawn_push(board, SAN);
    if (move == NONE_MOVE) move = san_pawn_capture(board, SAN);
    if (move == NONE_MOVE) move = san_castle_move(board, SAN);
    if (move == NONE_MOVE) move = san_piece_move(board, SAN);

    // This should not be needed, but lets verify to be safe
    return !moveIsLegal(board, move) ? NONE_MOVE : move;
}


static int pgn_read_until_move(char* buffer, int index) {
    for (; !isalpha(buffer[index]) && buffer[index] != '\0'; index++);
    return index;
}

static int pgn_read_until_space(char* buffer, int index) {
    for (; buffer[index] != ' ' && buffer[index] != '\0'; index++);
    return index;
}


static bool pgn_read_headers(FILE* pgn, PGNData* data) {

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

static void pgn_read_moves(FILE* pgn, FILE* bindata, PGNData* data, HalfKPSample* samples, Board* board) {

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
        move = parse_san(board, data->buffer + index);

        // Assume that each move has an associated score
        index = pgn_read_until_space(data->buffer, index);

        // Scan for an eval and ignore Mate scores
        if (sscanf(data->buffer + index + 1, "%lf", &feval) == 1)
            eval = static_cast<int>(0.5 + 100.0 * feval);
        else eval = MATE;

        // Use White's POV for all evaluations
        if (board->turn == BLACK) eval = -eval;

        // Use the sample if it is quiet and within [-2000, 2000] cp
        if (abs(eval) <= 2000
            && !board->kingAttackers
            && !moveIsTactical(board, move)
            && (board->turn == WHITE ? data->is_white : data->is_black))
            build_halfkp_sample(board, &samples[placed++], data->result, eval);

        // Skip head to the end of this comment to prepare for the next Move
        index = pgn_read_until_space(data->buffer, index + 1); data->plies++;
        applyMove(board, move, &undo);
    }

    if (data->result != PGN_UNKNOWN_RESULT)
        fwrite(samples, sizeof(HalfKPSample), placed, bindata);
}

static bool process_next_pgn(FILE* pgn, FILE* bindata, PGNData* data, HalfKPSample* samples, Board* board) {

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

    // Init the board, let Ethereal determine FRC
    boardFromFEN(board, data->startpos, 0);

    // Use all positions if neither matched Ethereal
    if (!data->is_white && !data->is_black)
        data->is_white = data->is_black = true;

    // Read Result & Fen and skip to Moves
    pgn_read_moves(pgn, bindata, data, samples, board);

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

    Board board;
    while (process_next_pgn(pgn, bindata, data.get(), &samples[0], &board));
    fclose(pgn); fclose(bindata); 
}


/// board.c again

void boardFromFEN(Board* board, const char* fen, int chess960) 
{
    static const uint64_t StandardCastles = (1ull << 0) | (1ull << 7)
        | (1ull << 56) | (1ull << 63);

    int sq = 56;
    char ch;
    char* str = strdup(fen), * strPos = NULL;
    char* token = strtok_r(str, " ", &strPos);
    uint64_t rooks, kings, white, black;

    clearBoard(board); // Zero out, set squares to EMPTY

    // Piece placement
    while ((ch = *token++)) {
        if (isdigit(ch))
            sq += ch - '0';
        else if (ch == '/')
            sq -= 16;
        else {
            const bool colour = islower(ch);
            if (const char* piece = strchr(PieceLabel[colour], ch))
                setSquare(board, colour, static_cast<int>(piece - PieceLabel[colour]), sq++);
        }
    }

    // Turn of play
    token = strtok_r(NULL, " ", &strPos);
    board->turn = token[0] == 'w' ? WHITE : BLACK;
    if (board->turn == BLACK) board->hash ^= ZobristTurnKey;

    // Castling rights
    token = strtok_r(NULL, " ", &strPos);

    rooks = board->pieces[ROOK];
    kings = board->pieces[KING];
    white = board->colours[WHITE];
    black = board->colours[BLACK];

    while ((ch = *token++)) {
        if (ch == 'K') setBit(&board->castleRooks, getmsb(white & rooks & RANK_1));
        if (ch == 'Q') setBit(&board->castleRooks, getlsb(white & rooks & RANK_1));
        if (ch == 'k') setBit(&board->castleRooks, getmsb(black & rooks & RANK_8));
        if (ch == 'q') setBit(&board->castleRooks, getlsb(black & rooks & RANK_8));
        if ('A' <= ch && ch <= 'H') setBit(&board->castleRooks, square(0, ch - 'A'));
        if ('a' <= ch && ch <= 'h') setBit(&board->castleRooks, square(7, ch - 'a'));
    }

    for (sq = 0; sq < N_SQUARES; sq++) {
        board->castleMasks[sq] = ~0ull;
        if (testBit(board->castleRooks, sq)) clearBit(&board->castleMasks[sq], sq);
        if (testBit(white & kings, sq)) board->castleMasks[sq] &= ~white;
        if (testBit(black & kings, sq)) board->castleMasks[sq] &= ~black;
    }

    rooks = board->castleRooks;
    while (rooks) board->hash ^= ZobristCastleKeys[poplsb(&rooks)];

    // En passant square
    board->epSquare = stringToSquare(strtok_r(NULL, " ", &strPos));
    if (board->epSquare != -1)
        board->hash ^= ZobristEnpassKeys[fileOf(board->epSquare)];

    // Half & Full Move Counters
    board->halfMoveCounter = atoi(strtok_r(NULL, " ", &strPos));
    board->fullMoveCounter = atoi(strtok_r(NULL, " ", &strPos));

    // Move count: ignore and use zero, as we count since root
    board->numMoves = 0;

    // Need king attackers for move generation
    board->kingAttackers = attackersToKingSquare(board);

    // Need squares attacked by the opposing player
    board->threats = allAttackedSquares(board, !board->turn);

    // We save the game mode in order to comply with the UCI rules for printing
    // moves. If chess960 is not enabled, but we have detected an unconventional
    // castle setup, then we set chess960 to be true on our own. Currently, this
    // is simply a hack so that FRC positions may be added to the bench.csv
    board->chess960 = chess960 || (board->castleRooks & ~StandardCastles);

    board->thread = NULL; // By default, a Board is not tied to any Thread

    free(str);
}

uint64_t perft(Board* board, int depth) 
{
    Undo undo[1];
    ptrdiff_t size = 0;
    uint64_t found = 0ull;
    uint16_t moves[MAX_MOVES];

    if (depth == 0) return 1ull;

    // Call genAllNoisyMoves() & genAllNoisyMoves()
    size += genAllNoisyMoves(board, moves);
    size += genAllQuietMoves(board, moves + size);

    // Recurse on all valid moves
    for (size -= 1; size >= 0; size--) {
        applyMove(board, moves[size], undo);
        if (moveWasLegal(board)) found += perft(board, depth - 1);
        revertMove(board, moves[size], undo);
    }

    return found;
}


/// cmdline.h

void handleCommandLine(int argc, char** argv);


/// cmdline.c

static void runBenchmark(int argc, char** argv)
{
    static const char* Benchmarks[] = {
        #include "bench.csv"
        ""
    };

    Board board;
    Limits limits = { 0 };

    int scores[256];
    double times[256];
    uint64_t nodes[256];
    uint16_t bestMoves[256];
    uint16_t ponderMoves[256];

    double time;
    uint64_t totalNodes = 0ull;

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

    for (int i = 0; strcmp(Benchmarks[i], ""); i++) {

        // Perform the search on the position
        limits.start = get_real_time();
        boardFromFEN(&board, Benchmarks[i], 0);
        getBestMove(&threads[0], &board, &limits, &bestMoves[i], &ponderMoves[i], &scores[i]);

        // Stat collection for later printing
        times[i] = get_real_time() - limits.start;
        nodes[i] = nodesSearchedThreadPool(&threads[0]);

        tt_clear(nthreads); // Reset TT between searches
    }

    printf("\n===============================================================================\n");

    for (int i = 0; strcmp(Benchmarks[i], ""); i++) {

        // Convert moves to typical UCI notation
        char bestStr[6], ponderStr[6];
        moveToString(bestMoves[i], bestStr, 0);
        moveToString(ponderMoves[i], ponderStr, 0);

        // Log all collected information for the current position
        printf("[# %2d] %5d cp  Best:%6s  Ponder:%6s %12d nodes %12d nps\n", i + 1, scores[i],
            bestStr, ponderStr, (int)nodes[i], (int)(1000.0f * nodes[i] / (times[i] + 1)));
    }

    printf("===============================================================================\n");

    // Report the overall statistics
    time = get_real_time() - time;
    for (int i = 0; strcmp(Benchmarks[i], ""); i++) totalNodes += nodes[i];
    printf("OVERALL: %47d nodes %12d nps\n", (int)totalNodes, (int)(1000.0f * totalNodes / (time + 1)));

    clearThreadPool(&threads);
}

static void runEvalBook(int argc, char** argv) {

    int score;
    Board board;
    char line[256];
    Limits limits = { 0 };
    uint16_t best, ponder;
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
        boardFromFEN(&board, line, 0);
        getBestMove(&threads[0], &board, &limits, &best, &ponder, &score);
        resetThreadPool(&threads[0]);
        tt_clear(nthreads);
        printf("FEN: %s", line);
    }

    printf("Time %dms\n", (int)(get_real_time() - start));
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
    for (auto& thread: *threads)
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

void newSearchThreadPool(Thread* threads, Board* board, Limits* limits, TimeManager* tm) 
{
    // Initialize each Thread in the Thread Pool. We need a reference
    // to the UCI seach parameters, access to the timing information,
    // somewhere to store the results of each iteration by the main, and
    // our own copy of the board. Also, we reset the seach statistics

    for (int i = 0; i < threads->nthreads; i++) 
    {
        threads[i].limits = limits;
        threads[i].tm = tm;
        threads[i].height = 0;
        threads[i].nodes = 0ull;
        threads[i].tbhits = 0ull;

        memcpy(&threads[i].board, board, sizeof(Board));
        threads[i].board.thread = &threads[i];

        // Reset the accumulator stack. The table can remain
        threads[i].nnue->current = &threads[i].nnue->stack[0];
        threads[i].nnue->current->accurate[WHITE] = 0;
        threads[i].nnue->current->accurate[BLACK] = 0;

        memset(threads[i].nodeStates, 0, sizeof(NodeState) * STACK_SIZE);
    }
}

uint64_t nodesSearchedThreadPool(Thread* threads) {

    // Sum up the node counters across each Thread. Threads have
    // their own node counters to avoid true sharing the cache

    uint64_t nodes = 0ull;

    for (int i = 0; i < threads->nthreads; i++)
        nodes += threads->threads[i].nodes;

    return nodes;
}

uint64_t tbhitsThreadPool(Thread* threads) {

    // Sum up the tbhit counters across each Thread. Threads have
    // their own tbhit counters to avoid true sharing the cache

    uint64_t tbhits = 0ull;

    for (int i = 0; i < threads->nthreads; i++)
        tbhits += threads->threads[i].tbhits;

    return tbhits;
}


/// uci.c

const char* StartPosition = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

int main(int argc, char** argv) 
{
    Board board;
    char str[8192] = { 0 };
    unique_ptr<thread> pthreadsgo;
    UCIGoStruct uciGoStruct;

    int chess960 = 0;
    int multiPV = 1;

    // Initialize core components of Ethereal
    initAttacks(); initMasks(); initPSQT();
    initSearch(); initZobrist(); tt_init(1, 16);
    initPKNetwork(); nnue_incbin_init();

    // Create the UCI-board and our threads
    vector<Thread> threads(1);
    populateThreadPool(&threads);
    boardFromFEN(&board, StartPosition, chess960);

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
    |   position | *  Sets the board position via an optional FEN and optional move list |
    |         go | *       Searches the current position with the provided time controls |
    |  ponderhit |          Flags the search to indicate that the ponder move was played |
    |       stop |            Signals the search threads to finish and report a bestmove |
    |       quit |             Exits the engine and any searches by killing the UCI loop |
    |      perft |            Custom command to compute PERFT(N) of the current position |
    |      print |         Custom command to print an ASCII view of the current position |
    |------------|-----------------------------------------------------------------------|
    */

    while (getInput(str)) {

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
            uciPosition(str, &board, chess960);

        else if (strStartsWith(str, "go"))
        {
            pthreadsgo.reset(uciGo(&uciGoStruct, &threads[0], &board, multiPV, str));
            pthreadsgo->detach();   // maybe not needed?
        }

        else if (strEquals(str, "ponderhit"))
            IS_PONDERING = 0;

        else if (strEquals(str, "stop"))
            ABORT_SIGNAL = 1, IS_PONDERING = 0;

        else if (strEquals(str, "quit"))
            break;

        else if (strStartsWith(str, "perft"))
            cout << perft(&board, atoi(str + strlen("perft "))) << endl;

        else if (strStartsWith(str, "print"))
            printBoard(&board), fflush(stdout);
    }

    return 0;
}

thread* uciGo(UCIGoStruct* ucigo, Thread* threads, Board* board, int multiPV, char* str) 
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
    int size = static_cast<int>(genAllLegalMoves(board, moves)), idx = 0;

    Limits* limits = &ucigo->limits;
    memset(limits, 0, sizeof(Limits));

    IS_PONDERING = FALSE; // Reset PONDERING every time to be safe

    for (ptr = strtok(NULL, " "); ptr != NULL; ptr = strtok(NULL, " ")) {

        // Parse time control conditions
        if (strEquals(ptr, "wtime")) wtime = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "btime")) btime = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "winc")) winc = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "binc")) binc = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "movestogo")) mtg = atoi(strtok(NULL, " "));

        // Parse special search termination conditions
        if (strEquals(ptr, "depth")) limits->depthLimit = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "movetime")) limits->timeLimit = atoi(strtok(NULL, " "));
        if (strEquals(ptr, "nodes")) limits->nodeLimit = static_cast<uint64_t>(atof(strtok(NULL, " ")));

        // Parse special search modes
        if (strEquals(ptr, "infinite")) limits->limitedByNone = TRUE;
        if (strEquals(ptr, "searchmoves")) limits->limitedByMoves = TRUE;
        if (strEquals(ptr, "ponder")) IS_PONDERING = TRUE;

        // Parse any specific moves that we are to search
        for (int i = 0; i < size; i++) {
            moveToString(moves[i], moveStr, board->chess960);
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
    limits->start = (board->turn == WHITE) ? start : start;
    limits->time = (board->turn == WHITE) ? wtime : btime;
    limits->inc = (board->turn == WHITE) ? winc : binc;
    limits->mtg = (board->turn == WHITE) ? mtg : mtg;

    // Cap our MultiPV search based on the suggested or legal moves
    limits->multiPV = Min(multiPV, limits->limitedByMoves ? idx : size);

    // Prepare the uciGoStruct for the new pthread
    ucigo->board = board;
    ucigo->threads = threads;

    // Spawn a new thread to handle the search
    return new thread(&start_search_threads, ucigo);
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

void uciPosition(char* str, Board* board, int chess960) 
{
    int size;
    uint16_t moves[MAX_MOVES];
    char* ptr, moveStr[6], testStr[6];
    Undo undo[1];

    // Position is defined by a FEN, X-FEN or Shredder-FEN
    if (strContains(str, "fen"))
        boardFromFEN(board, strstr(str, "fen") + strlen("fen "), chess960);

    // Position is simply the usual starting position
    else if (strContains(str, "startpos"))
        boardFromFEN(board, StartPosition, chess960);

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
        size = static_cast<int>(genAllLegalMoves(board, moves));

        // Find and apply the given move
        for (int i = 0; i < size; i++) {
            moveToString(moves[i], testStr, board->chess960);
            if (strEquals(moveStr, testStr)) {
                applyMove(board, moves[i], undo);
                break;
            }
        }

        // Reset move history whenever we reset the fifty move rule. This way
        // we can track all positions that are candidates for repetitions, and
        // are still able to use a fixed size for the history array (512)
        if (board->halfMoveCounter == 0)
            board->numMoves = 0;

        // Skip over all white space
        while (*ptr == ' ') ptr++;
    }
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
    uint64_t nodes = nodesSearchedThreadPool(threads);
    uint64_t tbhits = tbhitsThreadPool(threads);
    int nps = (int)(1000 * (nodes / (1 + elapsed)));

    // If the score is MATE or MATED in X, convert to X
    int score = bounded >= MATE_IN_MAX ? (MATE - bounded + 1) / 2
        : bounded <= -MATE_IN_MAX ? -(bounded + MATE) / 2 : bounded;

    // Two possible score types, mate and cp = centipawns
    const char* type = abs(bounded) >= MATE_IN_MAX ? "mate" : "cp";

    // Partial results from a windowed search have bounds
    const char* bound = bounded >= beta ? " lowerbound "
        : bounded <= alpha ? " upperbound " : " ";

    printf("info depth %d seldepth %d multipv %d score %s %d%stime %d "
        "knodes %d nps %d tbhits %d hashfull %d pv ",
        depth, seldepth, multiPV, type, score, bound, static_cast<int>(elapsed), static_cast<int>(nodes >> 10), nps, static_cast<int>(tbhits), hashfull);

    // Iterate over the PV and print each move
    for (int i = 0; i < pv->length; i++) {
        char moveStr[6];
        moveToString(pv->line[i], moveStr, threads->board.chess960);
        printf("%s ", moveStr);
    }

    // Send out a newline and flush
    puts(""); fflush(stdout);
}

void uciReportCurrentMove(Board* board, uint16_t move, int currmove, int depth) {

    char moveStr[6];
    moveToString(move, moveStr, board->chess960);
    printf("info depth %d currmove %s currmovenumber %d\n", depth, moveStr, currmove);
    fflush(stdout);

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
