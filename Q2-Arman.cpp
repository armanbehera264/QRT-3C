// Toroidal word-search generation (C++17, standard library only).
//
// Reads: required count, required words, forbidden count, forbidden words.
// Writes: exactly N rows of N uppercase letters.
// If a HackerRank driver supplies main(), compile with -DNO_MAIN (or delete
// main) and call generate_grid directly.
//
// Strategy (density first):
//   1. Lossless preprocessing: drop duplicates/reversals, drop required words
//      contained in other required words (they are then free in the score),
//      drop forbidden words implied by shorter ones, detect contradictions.
//   2. Guaranteed-valid fallback: separated shelf packing with a "safe" letter
//      (a letter in no forbidden word, so filler never creates a forbidden word).
//   3. Small instances: exhaustive DFS from the lower bound upward. The first
//      size it solves is provably minimum; sizes it exhausts are proved
//      infeasible.
//   4. All instances: a ruin-and-recreate local search (min-conflict with
//      adaptive weights) at a fixed N, used inside a binary search over N
//      and then repeatedly at best-1 until the time budget is spent.
//   Every returned grid passes an independent 8-direction validator.

#include <bits/stdc++.h>
using namespace std;

// Total wall-clock budget per call, in seconds. Raise it if the judge allows
// more time: more time = more attempts at smaller N = higher density.
static double SEARCH_SECONDS = 1.5;

struct NoSolutionError : runtime_error { using runtime_error::runtime_error; };
struct SearchLimitError : runtime_error { using runtime_error::runtime_error; };

namespace {

using Clock = chrono::steady_clock;
double now() {
    static const auto t0 = Clock::now();
    return chrono::duration<double>(Clock::now() - t0).count();
}

string reversed(const string& s) { return string(s.rbegin(), s.rend()); }

// Every allowed direction on an N x N torus has period exactly N, so a word
// longer than N can only be read if it repeats with period N.
bool periodic(const string& w, int n) {
    for (size_t k = n; k < w.size(); ++k)
        if (w[k] != w[k % n]) return false;
    return true;
}

long long isqrtll(long long x) {
    if (x <= 0) return 0;
    long long r = (long long)sqrtl((long double)x);
    while (r * r > x) --r;
    while ((r + 1) * (r + 1) <= x) ++r;
    return r;
}
int ceilSqrt(long long s) { s = max(1LL, s); return (int)isqrtll(s - 1) + 1; }

void checkWords(const vector<string>& ws, const char* name) {
    for (const string& w : ws) {
        if (w.empty()) throw invalid_argument(string(name) + " must contain nonempty A-Z strings");
        for (char c : w)
            if (c < 'A' || c > 'Z')
                throw invalid_argument(string(name) + " must contain nonempty A-Z strings");
    }
}

// Lossless reduction. A word and its reversal impose the same condition.
// Required: a word contained in a longer required word is redundant.
// Forbidden: a word containing a shorter forbidden word is redundant.
vector<string> reduceWords(const vector<string>& words, bool required) {
    set<string> uniq;
    for (const string& w : words) uniq.insert(min(w, reversed(w)));
    vector<string> ordered(uniq.begin(), uniq.end());
    stable_sort(ordered.begin(), ordered.end(), [&](const string& a, const string& b) {
        if (a.size() != b.size()) return required ? a.size() > b.size() : a.size() < b.size();
        return a < b;
    });
    map<size_t, unordered_set<string>> byLen;
    if (required)
        for (const string& w : uniq) byLen[w.size()].insert(w);
    unordered_set<string> redundant;
    vector<string> keep;
    for (const string& w : ordered) {
        if (required) {
            if (redundant.count(w)) continue;
            keep.push_back(w);
            for (auto& [len, cand] : byLen) {
                if (len >= w.size()) continue;
                for (size_t s = 0; s + len <= w.size(); ++s) {
                    string sub = w.substr(s, len);
                    if (cand.count(sub)) redundant.insert(sub);
                    string r = reversed(sub);
                    if (cand.count(r)) redundant.insert(r);
                }
            }
        } else {
            bool containsShorter = false;
            for (auto& [len, cand] : byLen) {
                if (len >= w.size()) continue;
                for (size_t s = 0; s + len <= w.size() && !containsShorter; ++s) {
                    string sub = w.substr(s, len);
                    if (cand.count(sub) || cand.count(reversed(sub))) containsShorter = true;
                }
                if (containsShorter) break;
            }
            if (!containsShorter) {
                keep.push_back(w);
                byLen[w.size()].insert(w);
            }
        }
    }
    return keep;
}

// ---------------------------------------------------------------- geometry
// Four families of N cyclic lines (rows, columns, two diagonals) cover all
// eight directions once both word orientations are considered.
struct Torus {
    int n;
    vector<int> lc[4];          // lc[d][l*n + p] = cell at position p of line l
    vector<int> cl[4], cp[4];   // cell -> (line, position) in family d
    explicit Torus(int n_) : n(n_) {
        for (int d = 0; d < 4; ++d) {
            lc[d].assign(n * n, 0); cl[d].assign(n * n, 0); cp[d].assign(n * n, 0);
            for (int l = 0; l < n; ++l)
                for (int p = 0; p < n; ++p) {
                    int r, c;
                    if (d == 0) { r = l; c = p; }
                    else if (d == 1) { r = p; c = l; }
                    else if (d == 2) { r = p; c = (l + p) % n; }
                    else { r = p; c = ((l - p) % n + n) % n; }
                    int cell = r * n + c;
                    lc[d][l * n + p] = cell; cl[d][cell] = l; cp[d][cell] = p;
                }
        }
    }
};

// Forbidden patterns as they can appear on a cyclic line of length n,
// indexed by (letter, offset) so a cell only checks patterns it could be in.
struct Needles {
    vector<string> list;
    vector<pair<int, int>> byChar[26];
    Needles(const vector<string>& forbidden, int n) {
        set<string> s;
        for (const string& w : forbidden) {
            if (!periodic(w, n)) continue;
            size_t m = min<size_t>(n, w.size());
            s.insert(w.substr(0, m));
            s.insert(reversed(w).substr(0, m));
        }
        list.assign(s.begin(), s.end());
        for (int i = 0; i < (int)list.size(); ++i)
            for (int j = 0; j < (int)list[i].size(); ++j)
                byChar[list[i][j] - 'A'].push_back({i, j});
    }
    bool empty() const { return list.empty(); }
};

// --------------------------------------------------------------- validator
}  // namespace

// Independent, direct eight-direction verification of a grid.
bool validate_grid(const vector<string>& grid, const vector<string>& required,
                   const vector<string>& forbidden) {
    if (grid.empty()) return false;
    int n = grid.size();
    for (const string& row : grid) {
        if ((int)row.size() != n) return false;
        for (char c : row) if (c < 'A' || c > 'Z') return false;
    }
    for (const string& w : required) if (w.empty() || (int)w.size() > n) return false;
    for (const string& w : forbidden) if (w.empty()) return false;
    vector<string> lines;
    lines.reserve(4 * n);
    for (const string& row : grid) lines.push_back(row + row.substr(0, n - 1));
    for (int c = 0; c < n; ++c)
        for (int dc : {0, 1, -1}) {
            string line(n, ' ');
            for (int r = 0; r < n; ++r) line[r] = grid[r][((c + r * dc) % n + n) % n];
            lines.push_back(line + line.substr(0, n - 1));
        }
    auto contains = [&](const string& w) {
        if (!periodic(w, n)) return false;
        size_t m = min<size_t>(n, w.size());
        string f = w.substr(0, m), b = reversed(w).substr(0, m);
        for (const string& line : lines)
            if (line.find(f) != string::npos || line.find(b) != string::npos) return true;
        return false;
    };
    for (const string& w : required) if (!contains(w)) return false;
    for (const string& w : forbidden) if (contains(w)) return false;
    return true;
}

namespace {

// ------------------------------------------------------------- free cells
// Used only when every allowed letter occurs in some forbidden word: letter
// the unused cells without creating a forbidden word. Greedy choice per
// cell, then min-conflict repair; letters of required words never change.
struct FreeFiller {
    int n;
    const Torus& T;
    const Needles& F;
    mt19937_64& rng;
    vector<char> grid;
    FreeFiller(const Torus& t, const Needles& f, mt19937_64& g, vector<char> letters)
        : n(t.n), T(t), F(f), rng(g), grid(move(letters)) {}

    int forbiddenCount(int cell) const {
        char ch = grid[cell];
        if (!ch) return 0;
        int hits = 0;
        for (auto [ni, j] : F.byChar[ch - 'A']) {
            const string& nd = F.list[ni];
            int m = nd.size();
            for (int d = 0; d < 4; ++d) {
                const int* line = &T.lc[d][T.cl[d][cell] * n];
                int q = T.cp[d][cell] - j;
                if (q < 0) q += n;
                int k = 0;
                for (; k < m; ++k) { if (grid[line[q]] != nd[k]) break; if (++q == n) q = 0; }
                hits += k == m;
            }
        }
        return hits;
    }

    bool fill(const string& alphabet, double deadline) {
        vector<int> freeCells;
        for (int c = 0; c < n * n; ++c) if (!grid[c]) freeCells.push_back(c);
        shuffle(freeCells.begin(), freeCells.end(), rng);
        string letters = alphabet;
        for (int c : freeCells) {
            shuffle(letters.begin(), letters.end(), rng);
            int bestHits = INT_MAX; char bestCh = letters[0];
            for (char x : letters) {
                grid[c] = x;
                int h = forbiddenCount(c);
                if (h < bestHits) { bestHits = h; bestCh = x; if (!h) break; }
            }
            grid[c] = bestCh;
        }
        for (long long it = 0;; ++it) {
            if ((it & 15) == 0 && now() > deadline) return false;
            vector<int> bad;
            for (int c : freeCells) if (forbiddenCount(c)) bad.push_back(c);
            if (bad.empty()) return true;
            int c = bad[rng() % bad.size()];
            shuffle(letters.begin(), letters.end(), rng);
            int bestHits = INT_MAX; char bestCh = grid[c], old = grid[c];
            for (char x : letters) {
                if (x == old && letters.size() > 1 && (rng() & 3)) continue;  // encourage moves
                grid[c] = x;
                int h = forbiddenCount(c);
                if (h < bestHits) { bestHits = h; bestCh = x; }
            }
            grid[c] = bestCh;
        }
    }
};

vector<string> toRows(const vector<char>& g, int n) {
    vector<string> out(n);
    for (int r = 0; r < n; ++r) out[r] = string(&g[r * n], &g[r * n] + n);
    return out;
}

// ------------------------------------------------------------------ greedy
// One-pass construction at a fixed N, longest word first: each word goes to
// the placement with the fewest letter clashes, then the most shared letters
// (sharing is what raises density). Fast; succeeds outright when N is roomy.
// A cell holding k letters whose most common letter appears m times has
// k - m conflicts; the grid is a solution when there are none.
struct Greedy {
    int n, N2;
    const Torus& T;
    const Needles& F;
    const vector<string>& W;
    vector<string> R;
    vector<char> pal;
    mt19937_64& rng;

    vector<array<uint16_t, 26>> cnt;
    vector<int> tot, mx;
    vector<uint32_t> maxMask, pres;   // letters at the max count / present
    vector<char> grid;                 // a majority letter, 0 if empty
    vector<int> at;
    // Per line, doubled (length 2n) copies of maxMask / pres so a scan reads
    // contiguous memory; kept current on every cell change.
    vector<uint32_t> LM[4], LP[4];
    long long confSum = 0;             // sum over cells of (tot - mx)
    uint64_t xs = 0x9E3779B97F4A7C15ULL;
    uint64_t fast() { xs ^= xs << 13; xs ^= xs >> 7; xs ^= xs << 17; return xs; }

    void sync(int c) {
        for (int d = 0; d < 4; ++d) {
            int base = T.cl[d][c] * 2 * n, p = T.cp[d][c];
            LM[d][base + p] = LM[d][base + p + n] = maxMask[c];
            LP[d][base + p] = LP[d][base + p + n] = pres[c];
        }
    }

    Greedy(const Torus& t, const Needles& f, const vector<string>& words, mt19937_64& g)
        : n(t.n), N2(t.n * t.n), T(t), F(f), W(words), rng(g), cnt(N2), tot(N2, 0), mx(N2, 0),
          maxMask(N2, ~0u), pres(N2, 0), grid(N2, 0), at(words.size(), -1) {
        for (auto& a : cnt) a.fill(0);
        for (const string& w : W) { R.push_back(reversed(w)); pal.push_back(R.back() == w); }
        xs ^= rng();
        for (int d = 0; d < 4; ++d) { LM[d].assign(2 * N2, ~0u); LP[d].assign(2 * N2, 0); }
    }

    void decode(int code, int& d, int& l, int& s, int& o) const {
        o = code & 1; int r = code >> 1; s = r % n; r /= n; l = r % n; d = r / n;
    }
    int encode(int d, int l, int s, int o) const { return (((d * n + l) * n + s) << 1) | o; }

    void refresh(int c) {
        int m = 0; uint32_t mm = 0, p = pres[c];
        while (p) {
            int b = __builtin_ctz(p); p &= p - 1;
            int k = cnt[c][b];
            if (k > m) { m = k; mm = 1u << b; } else if (k == m) mm |= 1u << b;
        }
        mx[c] = m;
        maxMask[c] = tot[c] ? mm : ~0u;
        grid[c] = tot[c] ? char('A' + __builtin_ctz(mm)) : 0;
        sync(c);
    }

    template <class Fn> void forCells(int w, int code, Fn&& f) const {
        int d, l, s, o; decode(code, d, l, s, o);
        const string& str = o ? R[w] : W[w];
        const int* line = &T.lc[d][l * n];
        int q = s;
        for (char ch : str) { f(line[q], ch - 'A'); if (++q == n) q = 0; }
    }

    void place(int w, int code) {
        forCells(w, code, [&](int c, int b) {
            confSum -= tot[c] - mx[c];
            if (cnt[c][b]++ == 0) pres[c] |= 1u << b;
            ++tot[c]; refresh(c);
            confSum += tot[c] - mx[c];
        });
        at[w] = code;
    }
    void unplace(int w) {
        forCells(w, at[w], [&](int c, int b) {
            confSum -= tot[c] - mx[c];
            if (--cnt[c][b] == 0) pres[c] &= ~(1u << b);
            --tot[c]; refresh(c);
            confSum += tot[c] - mx[c];
        });
        at[w] = -1;
    }
    bool forbiddenAt(int cell) const {
        char ch = grid[cell];
        if (!ch) return false;
        for (auto [ni, j] : F.byChar[ch - 'A']) {
            const string& nd = F.list[ni];
            int m = nd.size();
            for (int d = 0; d < 4; ++d) {
                const int* line = &T.lc[d][T.cl[d][cell] * n];
                int q = T.cp[d][cell] - j;
                if (q < 0) q += n;
                int k = 0;
                for (; k < m; ++k) { if (grid[line[q]] != nd[k]) break; if (++q == n) q = 0; }
                if (k == m) return true;
            }
        }
        return false;
    }

    // Best placements for w: fewest clashes, then most shared letters, random
    // tie-break. Returns up to `keep` (<= 8), best first.
    int bestPlacements(int w, int keep, int* out) {
        const string& A = W[w];
        const string& B = R[w];
        int L = A.size();
        int orients = pal[w] ? 1 : 2;
        int dmax = (L == 1) ? 1 : 4;
        int best = INT_MAX;
        // top-k (k <= 8) of (overlap<<32 | random) among placements at `best`.
        unsigned long long key[8]; int code8[8]; int have = 0;
        static thread_local vector<uint32_t> bitBuf;
        bitBuf.resize(2 * L);
        uint32_t* bits[2] = {bitBuf.data(), bitBuf.data() + L};
        for (int k = 0; k < L; ++k) { bits[0][k] = 1u << (A[k] - 'A'); bits[1][k] = 1u << (B[k] - 'A'); }
        for (int d = 0; d < dmax; ++d)
            for (int l = 0; l < n; ++l) {
                const uint32_t* bm = &LM[d][l * 2 * n];
                const uint32_t* bp = &LP[d][l * 2 * n];
                for (int o = 0; o < orients; ++o) {
                    const uint32_t* sb = bits[o];
                    for (int st = 0; st < n; ++st) {
                        int delta = 0, ov = 0, k = 0;
                        for (; k < L; ++k) {
                            uint32_t b = sb[k];
                            if (!(bm[st + k] & b)) { if (++delta > best) break; }
                            ov += (bp[st + k] & b) != 0;
                        }
                        if (k < L) continue;
                        int code = encode(d, l, st, o);
                        if (delta < best) { best = delta; have = 0; }
                        unsigned long long kk = ((unsigned long long)ov << 32) | (fast() & 0xffffffffULL);
                        if (have < keep) { key[have] = kk; code8[have] = code; ++have; }
                        else {
                            int mi = 0;
                            for (int i = 1; i < have; ++i) if (key[i] < key[mi]) mi = i;
                            if (kk > key[mi]) { key[mi] = kk; code8[mi] = code; }
                        }
                    }
                }
            }
        for (int i = 0; i < have; ++i)          // sort best-first (have <= 8)
            for (int j = i + 1; j < have; ++j)
                if (key[j] > key[i]) { swap(key[i], key[j]); swap(code8[i], code8[j]); }
        for (int i = 0; i < have; ++i) out[i] = code8[i];
        return have;
    }

    // Place w at its best spot, avoiding new forbidden words when possible.
    void putBest(int w) {
        int cands[8];
        int k = bestPlacements(w, F.empty() ? 1 : 6, cands);
        for (int i = 0; i < k; ++i) {
            int code = cands[i];
            if (F.empty() || i + 1 == k) { place(w, code); return; }
            static thread_local vector<int> fresh;
            fresh.clear();
            forCells(w, code, [&](int c, int) { if (!tot[c]) fresh.push_back(c); });
            place(w, code);
            bool bad = false;
            for (int c : fresh) if (forbiddenAt(c)) { bad = true; break; }
            if (!bad) return;
            unplace(w);
        }
    }

    bool anyForbidden() const {
        if (F.empty()) return false;
        for (int c = 0; c < N2; ++c) if (grid[c] && forbiddenAt(c)) return true;
        return false;
    }

    // Returns true if the greedy packing is already a valid solution.
    bool run(double deadline) {
        vector<int> order(W.size());
        iota(order.begin(), order.end(), 0);
        stable_sort(order.begin(), order.end(), [&](int a, int b) { return W[a].size() > W[b].size(); });
        if (order.empty()) return true;
        place(order[0], 0);   // symmetry: longest word at the origin, heading east
        for (size_t i = 1; i < order.size(); ++i) {
            if (now() > deadline) return false;
            putBest(order[i]);
        }
        return confSum == 0 && !anyForbidden();
    }
};

// ------------------------------------------------------------- tree search
// Depth-first search over word placements: always branch on the word with
// the fewest placements still consistent with the letters already fixed
// (fail-first), trying placements that share the most letters first.
// Per-placement "conflicting cells" and "matching cells" counters are
// updated incrementally whenever a cell gets a letter, so choosing the next
// word costs O(words) rather than a rescan of every placement.
// Run without a node limit it is complete for a fixed N (given a safe filler
// letter); with node limits and random tie-breaks it is a restart heuristic.
bool forbiddenAtGrid(const Torus& T, const Needles& F, const vector<char>& grid, int cell) {
    char ch = grid[cell];
    if (!ch) return false;
    int n = T.n;
    for (auto [ni, j] : F.byChar[ch - 'A']) {
        const string& nd = F.list[ni];
        int m = nd.size();
        for (int d = 0; d < 4; ++d) {
            const int* line = &T.lc[d][T.cl[d][cell] * n];
            int q = T.cp[d][cell] - j;
            if (q < 0) q += n;
            int k = 0;
            for (; k < m; ++k) { if (grid[line[q]] != nd[k]) break; if (++q == n) q = 0; }
            if (k == m) return true;
        }
    }
    return false;
}

struct TreeSearch {
    int n, N2, U, P;
    const Torus& T;
    const Needles& F;
    const vector<string>& W;
    vector<string> R;
    vector<int> dmax, orients;
    vector<uint8_t> killed, filled;    // [w * P + code]
    vector<int> alive, present, placed;
    vector<char> grid;
    vector<int> cellUse;
    vector<int> bestPlaced;            // best partial assignment seen by dfs
    int bestSat = -1, bestWords = 0;
    // Only words that are still unplaced keep live counters ("active");
    // a word's counters are rebuilt from the grid when it re-activates.
    vector<int> activeList, activePos;
    uint64_t xs;
    long long nodes = 0, nodeLimit = LLONG_MAX;
    double deadline = 0;
    bool timedOut = false, limitHit = false;

    TreeSearch(const Torus& t, const Needles& f, const vector<string>& words, uint64_t seed)
        : n(t.n), N2(t.n * t.n), U(words.size()), P(8 * t.n * t.n), T(t), F(f), W(words),
          killed((size_t)words.size() * 8 * t.n * t.n, 0), filled((size_t)words.size() * 8 * t.n * t.n, 0),
          alive(words.size()), present(words.size(), 0), placed(words.size(), -1), grid(t.n * t.n, 0),
          cellUse(t.n * t.n, 0), activePos(words.size(), -1), xs(seed | 1) {
        for (int w = 0; w < U; ++w) { activePos[w] = w; activeList.push_back(w); }
        for (int w = 0; w < U; ++w) {
            R.push_back(reversed(W[w]));
            dmax.push_back(W[w].size() == 1 ? 1 : 4);
            orients.push_back(R[w] == W[w] ? 1 : 2);
            alive[w] = dmax[w] * orients[w] * N2;
        }
    }
    uint64_t fast() { xs ^= xs << 13; xs ^= xs >> 7; xs ^= xs << 17; return xs; }
    int encode(int d, int l, int s, int o) const { return (((d * n + l) * n + s) << 1) | o; }

    // Back to the empty grid (all counters zero, every placement alive).
    bool dirty = false;
    void reset() {
        if (!dirty) return;
        fill(killed.begin(), killed.end(), 0);
        fill(filled.begin(), filled.end(), 0);
        fill(grid.begin(), grid.end(), 0);
        fill(cellUse.begin(), cellUse.end(), 0);
        activeList.clear();
        for (int w = 0; w < U; ++w) {
            alive[w] = dmax[w] * orients[w] * N2; present[w] = 0; placed[w] = -1;
            activePos[w] = w; activeList.push_back(w);
        }
        dirty = false;
    }

    template <bool SET> void touch(int c, char x) {
        int lb[4], pp[4];
        for (int d = 0; d < 4; ++d) { lb[d] = T.cl[d][c] * n; pp[d] = T.cp[d][c]; }
        for (int w : activeList) {
            const int L = W[w].size();
            uint8_t* K = &killed[(size_t)w * P];
            uint8_t* Fl = &filled[(size_t)w * P];
            int sat = 0, revived = 0;
            for (int d = 0; d < dmax[w]; ++d) {
                const int base = (d * n) * n + lb[d];   // (d*n + l)*n
                const int p = pp[d];
                for (int o = 0; o < orients[w]; ++o) {
                    const char* s = o ? R[w].data() : W[w].data();
                    int st = p;
                    for (int k = 0; k < L; ++k) {
                        const int code = ((base + st) << 1) | o;
                        if (--st < 0) st += n;
                        if (s[k] == x) {
                            if (SET) sat += (++Fl[code] == L) & !K[code];
                            else sat += (Fl[code]-- == L) & !K[code];
                        } else {
                            if (SET) revived += K[code]++ == 0;
                            else revived += --K[code] == 0;
                        }
                    }
                }
            }
            if (SET) { present[w] += sat; alive[w] -= revived; }
            else { present[w] -= sat; alive[w] += revived; }
        }
    }

    void deactivate(int w) {
        int i = activePos[w];
        if (i < 0) return;
        int last = activeList.back();
        activeList[i] = last; activePos[last] = i;
        activeList.pop_back(); activePos[w] = -1;
    }
    // Re-activate without rebuilding: valid only when the grid is exactly as
    // it was at deactivation (true when backtracking, since an inactive
    // word's counters are never touched).
    void restore(int w) {
        if (activePos[w] >= 0) return;
        activePos[w] = activeList.size();
        activeList.push_back(w);
    }
    void deactivateAll() { for (int w : activeList) activePos[w] = -1; activeList.clear(); }
    void activate(int w) {
        if (activePos[w] >= 0) return;
        const int L = W[w].size();
        uint8_t* K = &killed[(size_t)w * P];
        uint8_t* Fl = &filled[(size_t)w * P];
        int al = 0, pr = 0;
        for (int d = 0; d < dmax[w]; ++d)
            for (int l = 0; l < n; ++l) {
                const int* line = &T.lc[d][l * n];
                for (int o = 0; o < orients[w]; ++o) {
                    const char* s = o ? R[w].data() : W[w].data();
                    for (int st = 0; st < n; ++st) {
                        int kk = 0, ff = 0, q = st;
                        for (int k = 0; k < L; ++k) {
                            char g = grid[line[q]];
                            if (g) { if (g == s[k]) ++ff; else ++kk; }
                            if (++q == n) q = 0;
                        }
                        int code = encode(d, l, st, o);
                        K[code] = kk; Fl[code] = ff;
                        al += kk == 0; pr += kk == 0 && ff == L;
                    }
                }
            }
        alive[w] = al; present[w] = pr;
        activePos[w] = activeList.size();
        activeList.push_back(w);
    }

    void place(int w, int code, vector<int>& newly) {
        int o = code & 1, r = code >> 1;
        int s = r % n; r /= n; int l = r % n; int d = r / n;
        const string& str = o ? R[w] : W[w];
        const int* line = &T.lc[d][l * n];
        int q = s;
        for (char ch : str) {
            int c = line[q];
            if (!cellUse[c]++) { grid[c] = ch; touch<true>(c, ch); newly.push_back(c); }
            if (++q == n) q = 0;
        }
        placed[w] = code;
    }
    // Cell counters are order-independent sums, so any placed word can be
    // removed at any time (needed by the large-neighbourhood search).
    template <class Fn> void forPath(int w, int code, Fn&& f) const {
        int r = code >> 1;
        int s = r % n; r /= n; int l = r % n; int d = r / n;
        const int* line = &T.lc[d][l * n];
        int q = s;
        for (size_t k = 0; k < W[w].size(); ++k) { f(line[q]); if (++q == n) q = 0; }
    }
    void unplace(int w) {
        forPath(w, placed[w], [&](int c) {
            if (--cellUse[c] == 0) { touch<false>(c, grid[c]); grid[c] = 0; }
        });
        placed[w] = -1;
    }

    bool partial = false;              // LNS repairs: skip words with no spot
    bool dfs() {
        if (++nodes > nodeLimit) { limitHit = true; return false; }
        if (now() > deadline) { timedOut = true; return false; }
        int bw = -1, unsatisfied = 0, satLetters = 0;
        for (int w = 0; w < U; ++w) {
            if (placed[w] < 0 && present[w] == 0) ++unsatisfied;
            else satLetters += W[w].size();
        }
        int score = satLetters * 4 + (U - unsatisfied);   // long words count more
        if (score > bestSat) { bestSat = score; bestPlaced = placed; bestWords = U - unsatisfied; }
        for (int w = 0; w < U; ++w) {
            if (placed[w] >= 0 || present[w] > 0) continue;
            if (alive[w] == 0) {
                if (partial) continue;   // maximise satisfied words instead
                return false;
            }
            if (bw < 0 || alive[w] < alive[bw] ||
                (alive[w] == alive[bw] && W[w].size() > W[bw].size()))
                bw = w;
        }
        if (bw < 0) return unsatisfied == 0;
        // Bucket the live placements by shared-letter count; draw from the
        // fullest bucket first, uniformly at random within a bucket (lazy).
        int L = W[bw].size();
        vector<vector<int>> bucket(L + 1);
        const uint8_t* K = &killed[(size_t)bw * P];
        const uint8_t* Fl = &filled[(size_t)bw * P];
        for (int d = 0; d < dmax[bw]; ++d)
            for (int l = 0; l < n; ++l)
                for (int st = 0; st < n; ++st)
                    for (int o = 0; o < orients[bw]; ++o) {
                        int code = encode(d, l, st, o);
                        if (!K[code]) bucket[Fl[code]].push_back(code);
                    }
        vector<int> newly;
        for (int ov = L; ov >= 0; --ov) {
            auto& bk = bucket[ov];
            for (size_t i = 0; i < bk.size(); ++i) {
                size_t j = i + fast() % (bk.size() - i);
                swap(bk[i], bk[j]);
                int code = bk[i];
                newly.clear();
                deactivate(bw);
                place(bw, code, newly);
                bool ok = true;
                if (!F.empty())
                    for (int c : newly) if (forbiddenAtGrid(T, F, grid, c)) { ok = false; break; }
                if (ok && dfs()) return true;
                // Abandoned searches are reset wholesale, which is far cheaper
                // than unwinding; LNS repairs unwind (they are shallow).
                if (timedOut || (limitHit && !partial)) return false;
                unplace(bw);
                restore(bw);
                if (limitHit) return false;
            }
        }
        return false;
    }

    // 1 = solved (grid holds the letters), 0 = proved impossible at this N,
    // -1 = gave up (time or node limit).
    int solve(double dl, long long limit) {
        reset();
        dirty = true;
        deadline = dl; nodeLimit = limit; nodes = 0; timedOut = limitHit = false;
        if (U == 0) return 1;
        int first = 0;
        for (int w = 1; w < U; ++w) if (W[w].size() > W[first].size()) first = w;
        // Symmetry: translations, rotations and reflections of the torus map
        // any occurrence of the first word to the origin heading E or SE.
        vector<int> codes = {encode(0, 0, 0, 0)};
        if (W[first].size() > 1 && n > 1) codes.push_back(encode(2, 0, 0, 0));
        if (fast() & 1) reverse(codes.begin(), codes.end());
        vector<int> newly;
        for (int code : codes) {
            newly.clear();
            deactivate(first);
            place(first, code, newly);
            bool ok = true;
            if (!F.empty())
                for (int c : newly) if (forbiddenAtGrid(T, F, grid, c)) { ok = false; break; }
            if (ok && dfs()) return 1;
            if (timedOut || limitHit) return -1;
            unplace(first);
            restore(first);
        }
        return 0;
    }

    // Large-neighbourhood search: keep the best partial packing, clear the
    // words in a random window (or a random subset) and let the tree search
    // repair the hole. Accept equal-or-better partial packings.
    bool lns(double dl) {
        if (bestSat < 0) return false;
        vector<int> cur = bestPlaced;
        int curSat = bestSat, curWords = bestWords;
        reset();
        dirty = true;
        deactivateAll();
        {
            vector<int> newly;
            for (int w = 0; w < U; ++w) if (cur[w] >= 0) { newly.clear(); place(w, cur[w], newly); }
        }
        while (now() < dl) {
            // Build the kept set.
            vector<char> drop(U, 0);
            int mode = fast() % 3;
            if (mode < 2) {
                // window side between 35% and 60% of N
                int h = max(2, int(n * (0.35 + 0.25 * (fast() % 1000) / 1000.0)));
                int r0 = fast() % n, c0 = fast() % n;
                for (int w = 0; w < U; ++w) {
                    if (cur[w] < 0) continue;
                    bool in = false;
                    forPath(w, cur[w], [&](int c) {
                        int dr = (c / n - r0 + n) % n, dc = (c % n - c0 + n) % n;
                        if (dr < h && dc < h) in = true;
                    });
                    drop[w] = in;
                }
            } else {
                for (int w = 0; w < U; ++w) drop[w] = cur[w] >= 0 && fast() % 100 < 25;
            }
            // State currently equals `cur`: lift the dropped words out.
            int dropped = 0;
            for (int w = 0; w < U; ++w) if (drop[w]) { unplace(w); ++dropped; }
            for (int w = 0; w < U; ++w) if (placed[w] < 0) activate(w);
            bestSat = -1;
            deadline = dl; nodeLimit = 60 + 8LL * (dropped + (U - curWords)); nodes = 0;
            timedOut = limitHit = false;
            partial = true;
            bool ok = dfs();
            partial = false;
            if (ok) return true;
            if (timedOut) break;
            // dfs unwound to the kept words; move to the accepted assignment.
            deactivateAll();
            vector<int> newly;
            if (bestSat >= curSat) { curSat = bestSat; cur = bestPlaced; curWords = bestWords; }
            for (int w = 0; w < U; ++w) if (cur[w] >= 0 && placed[w] < 0) { newly.clear(); place(w, cur[w], newly); }
        }
        return false;
    }

    // Randomized restarts with growing node limits until solved or deadline.
    bool restarts(double dl) {
        long long limit = max(64, 4 * U);
        double t0 = now();
        // Restarts for the first quarter (seeding a good partial packing),
        // then LNS for the rest.
        while (now() < t0 + (dl - t0) * 0.25) {
            int r = solve(dl, limit);
            if (r == 1) return true;
            if (r == 0) return false;   // exhausted: impossible at this N
            limit = limit * 3 / 2;
        }
        return lns(dl);
    }
};

// ------------------------------------------------------------- fallbacks
// First-fit decreasing row packing; separated rows give a safe fallback.
vector<string> shelfGrid(const vector<string>& words, int n, char filler, bool separated) {
    int stride = separated ? 2 : 1;
    vector<string> rows;
    vector<int> used;
    vector<string> sorted = words;
    stable_sort(sorted.begin(), sorted.end(), [](auto& a, auto& b) { return a.size() > b.size(); });
    for (const string& w : sorted) {
        int cost = w.size() + (separated ? 1 : 0);
        bool done = false;
        for (size_t i = 0; i < rows.size(); ++i)
            if (used[i] + cost <= n) {
                rows[i] += w; if (separated) rows[i] += filler;
                used[i] += cost; done = true; break;
            }
        if (!done) {
            if (cost > n || ((int)rows.size() + 1) * stride > n) return {};
            rows.push_back(w + (separated ? string(1, filler) : string()));
            used.push_back(cost);
        }
    }
    vector<string> grid(n, string(n, filler));
    for (size_t i = 0; i < rows.size(); ++i)
        grid[i * stride] = rows[i] + string(n - rows[i].size(), filler);
    return grid;
}


// Dense rows: chain words through suffix/prefix overlaps (either reading
// direction), then pack chains into consecutive rows. Must be validated:
// letters in adjacent rows can form forbidden words vertically/diagonally.
vector<string> chainRows(const vector<string>& words, int n, char filler) {
    int U = words.size();
    vector<int> order(U);
    iota(order.begin(), order.end(), 0);
    stable_sort(order.begin(), order.end(), [&](int a, int b) { return words[a].size() > words[b].size(); });
    unordered_map<string, vector<pair<int, int>>> pre;
    for (int w = 0; w < U; ++w)
        for (int o = 0; o < 2; ++o) {
            string s = o ? reversed(words[w]) : words[w];
            for (size_t k = 1; k < s.size() && k <= 8; ++k) pre[s.substr(0, k)].push_back({w, o});
        }
    vector<char> used(U, 0);
    vector<string> chains;
    for (int w : order) {
        if (used[w]) continue;
        if ((int)words[w].size() > n) return {};
        used[w] = 1;
        string ch = words[w];
        while (true) {
            bool found = false;
            for (int k = min<int>(ch.size() - 1, 8); k >= 1 && !found; --k) {
                auto it = pre.find(ch.substr(ch.size() - k));
                if (it == pre.end()) continue;
                auto& lst = it->second;
                for (size_t i = 0; i < lst.size(); ++i) {
                    auto [v, o] = lst[i];
                    if (used[v]) { lst[i] = lst.back(); lst.pop_back(); --i; continue; }
                    if ((int)(ch.size() + words[v].size()) - k > n) continue;
                    string s = o ? reversed(words[v]) : words[v];
                    ch += s.substr(k);
                    used[v] = 1;
                    found = true;
                    break;
                }
            }
            if (!found) break;
        }
        chains.push_back(ch);
    }
    stable_sort(chains.begin(), chains.end(), [](auto& a, auto& b) { return a.size() > b.size(); });
    vector<string> rows;
    for (const string& c : chains) {
        bool put = false;
        for (string& r : rows)
            if ((int)(r.size() + c.size()) <= n) { r += c; put = true; break; }
        if (!put) {
            if ((int)rows.size() == n) return {};
            rows.push_back(c);
        }
    }
    for (string& r : rows) r += string(n - r.size(), filler);
    return rows;
}

// Lay packed rows top to bottom. Each row may be rotated cyclically (its
// words wrap around the torus intact) to avoid forming a forbidden word with
// the rows above; failing that, a filler row is inserted as a separator.
// Requires a safe filler letter.
vector<string> layoutRows(const vector<string>& rows, int n, char filler, const vector<string>& forbidden) {
    Torus T(n);
    Needles F(forbidden, n);
    vector<char> g(n * n, filler);
    auto clean = [&](int r) {
        if (F.empty()) return true;
        for (int c = 0; c < n; ++c) if (forbiddenAtGrid(T, F, g, r * n + c)) return false;
        return true;
    };
    int at = 0;
    for (const string& row : rows) {
        bool ok = false;
        while (!ok && at < n) {
            for (int rot = 0; rot < n && !ok; ++rot) {
                for (int c = 0; c < n; ++c) g[at * n + (c + rot) % n] = row[c];
                ok = clean(at);
            }
            if (!ok) {
                for (int c = 0; c < n; ++c) g[at * n + c] = filler;
                if (at > 0 && g[(at - 1) * n] == filler && all_of(&g[(at - 1) * n], &g[at * n], [&](char x) { return x == filler; }))
                    return {};   // the row is bad even next to a separator
                ++at;            // leave a separator row
            }
        }
        if (!ok) return {};
        ++at;
    }
    vector<string> out(n);
    for (int r = 0; r < n; ++r) out[r] = string(&g[r * n], &g[r * n] + n);
    return out;
}

}  // namespace

// Returns a validated grid; minimum-sized whenever the search can prove it,
// otherwise the densest valid grid found within SEARCH_SECONDS.
vector<string> generate_grid(const vector<string>& required_words, const vector<string>& forbidden_words) {
    const double start = now();
    const double deadline = start + SEARCH_SECONDS;
    checkWords(required_words, "required_words");
    checkWords(forbidden_words, "forbidden_words");
    const vector<string>& origR = required_words;
    const vector<string>& origF = forbidden_words;

    vector<string> required = reduceWords(origR, true);
    vector<string> forbidden = reduceWords(origF, false);

    for (const string& r : required)
        for (const string& f : forbidden)
            if (r.find(f) != string::npos || r.find(reversed(f)) != string::npos)
                throw NoSolutionError("Required word " + r + " contains forbidden word " + f);

    set<char> allowed;
    for (char c = 'A'; c <= 'Z'; ++c) allowed.insert(c);
    for (const string& w : forbidden) if (w.size() == 1) allowed.erase(w[0]);
    if (allowed.empty()) throw NoSolutionError("All 26 letters are forbidden");
    {
        vector<string> kept;
        for (const string& w : forbidden) {
            if (w.size() < 2) continue;
            bool ok = true;
            for (char c : w) if (!allowed.count(c)) { ok = false; break; }
            if (ok) kept.push_back(w);
        }
        forbidden.swap(kept);
    }
    if (allowed.size() == 1 && !forbidden.empty())
        throw NoSolutionError("The only permitted letter necessarily creates a forbidden word");

    // Every 2x2 block is a 4-clique under the eight directions. If every
    // doubled letter is forbidden, some 4 allowed letters must be pairwise OK.
    {
        set<string> pairs;
        for (const string& w : forbidden) if (w.size() == 2) pairs.insert(w);
        bool allDoubled = true;
        for (char c : allowed) if (!pairs.count(string(2, c))) { allDoubled = false; break; }
        if (allDoubled) {
            vector<char> al(allowed.begin(), allowed.end());
            auto ok = [&](char a, char b) {
                string x{a, b}, y{b, a};
                return !pairs.count(min(x, y));
            };
            function<bool(vector<char>, int)> clique = [&](vector<char> cand, int need) {
                if (need == 0) return true;
                if ((int)cand.size() < need) return false;
                for (size_t i = 0; i < cand.size(); ++i) {
                    vector<char> rest;
                    for (size_t j = i + 1; j < cand.size(); ++j) if (ok(cand[i], cand[j])) rest.push_back(cand[j]);
                    if (clique(rest, need - 1)) return true;
                }
                return false;
            };
            if (!clique(al, 4)) throw NoSolutionError("Forbidden adjacent pairs make every 2x2 block impossible");
        }
    }

    set<char> forbLetters;
    for (const string& w : forbidden) for (char c : w) forbLetters.insert(c);
    set<char> safeSet;
    for (char c : allowed) if (!forbLetters.count(c)) safeSet.insert(c);
    const bool hasSafe = !safeSet.empty();
    const char safeCh = hasSafe ? *safeSet.begin() : 'A';
    string alphabet;
    if (hasSafe) {
        // Replacing every non-required letter by the safe letter preserves all
        // required words and cannot create a forbidden word.
        set<char> a;
        for (const string& w : required) for (char c : w) a.insert(c);
        a.insert(safeCh);
        alphabet.assign(a.begin(), a.end());
        vector<string> kept;
        for (const string& w : forbidden) {
            bool ok = true;
            for (char c : w) if (!a.count(c)) { ok = false; break; }
            if (ok) kept.push_back(w);
        }
        forbidden.swap(kept);
    } else {
        alphabet.assign(allowed.begin(), allowed.end());
    }

    if (required.empty()) {
        for (char ch : alphabet) {
            bool bad = false;
            for (const string& w : forbidden) {
                bool constant = true;
                for (char c : w) if (c != ch) { constant = false; break; }
                if (constant) { bad = true; break; }
            }
            if (!bad) return {string(1, ch)};
        }
    }

    size_t longest = 1;
    long long total = 0;
    for (const string& w : origR) { longest = max(longest, w.size()); total += w.size(); }
    int counts[26] = {0};
    for (const string& w : required) {
        int c[26] = {0};
        for (char ch : w) ++c[ch - 'A'];
        for (int i = 0; i < 26; ++i) counts[i] = max(counts[i], c[i]);
    }
    long long need = 0;
    for (int i = 0; i < 26; ++i) need += counts[i];
    const int lower = max<int>(longest, ceilSqrt(need));

    vector<string> best;
    auto offer = [&](const vector<string>& g) {
        if (g.empty()) return false;
        if (!best.empty() && g.size() >= best.size()) return false;
        if (!validate_grid(g, origR, origF)) return false;
        best = g;
        return true;
    };
    // Largest N that already earns the full 100 points.
    int fullN = (int)isqrtll(10 * total / 17);
    while (17LL * (fullN + 1) * (fullN + 1) <= 10 * total) ++fullN;
    while (fullN > 0 && 17LL * fullN * fullN > 10 * total) --fullN;
    auto finished = [&]() { return !best.empty() && ((int)best.size() <= lower || (int)best.size() <= fullN); };

    // Cheap candidate at the lower bound: one required word per row.
    {
        vector<string> rowWords;
        for (const string& w : origR) if (find(rowWords.begin(), rowWords.end(), w) == rowWords.end()) rowWords.push_back(w);
        int n = lower;
        if ((int)rowWords.size() <= n && !rowWords.empty()) {
            char filler = hasSafe ? safeCh : alphabet[0];
            vector<string> cand;
            for (const string& w : rowWords) cand.push_back(w + string(n - w.size(), filler));
            while ((int)cand.size() < n) cand.push_back(string(n, filler));
            offer(cand);
        }
    }
    if (finished()) return best;

    // Guaranteed-valid fallback.
    if (hasSafe) {
        bool sep = !forbidden.empty();
        long long load = 0;
        for (const string& w : required) load += w.size() + (sep ? 1 : 0);
        int n = max<int>(lower + (sep ? 1 : 0), (int)isqrtll(max(1LL, load) * (sep ? 2 : 1)));
        while (true) {
            vector<string> g = shelfGrid(required, n, safeCh, sep);
            if (!g.empty() && validate_grid(g, origR, origF)) { offer(g); break; }
            ++n;
        }
    }
    if (finished()) return best;

    // Dense chained rows: a much tighter quick upper bound on large inputs.
    {
        long long letters = 0;
        for (const string& w : required) letters += w.size();
        char filler = hasSafe ? safeCh : alphabet[0];
        int hi = best.empty() ? INT_MAX : (int)best.size() - 1;
        int fails = 0;
        for (int n = max(lower, ceilSqrt(letters * 7 / 10)); hasSafe && n <= hi && now() < start + SEARCH_SECONDS * 0.1; ++n) {
            vector<string> rows = chainRows(required, n, filler);
            vector<string> g = rows.empty() ? rows : layoutRows(rows, n, filler, forbidden);
            if (g.empty()) continue;
            if (offer(g)) break;
            if (++fails >= 3) break;   // forbidden words keep appearing across rows
        }
    }
    if (finished()) return best;

    mt19937_64 rng(0x5eed1234ULL);

    // Attempt one size with the local search; finish and validate the grid.
    // Attempt one size: greedy pass, then tree search (restarts + LNS);
    // finally letter the unused cells. The caller validates the grid.
    auto attempt = [&](int n, double dl) -> vector<string> {
        Torus T(n);
        Needles F(forbidden, n);
        vector<char> g;
        Greedy G(T, F, required, rng);
        if (G.run(dl)) g = G.grid;               // cheap; often enough when N is roomy
        // The tree search keeps 2 bytes per (word, placement); cap its memory.
        // Its 8-bit counters also need words of at most 255 letters.
        bool treeFits = (double)required.size() * 8.0 * n * n <= 48e6 && longest <= 255;
        if (g.empty() && treeFits && dl - now() > 0.01) {
            TreeSearch S(T, F, required, rng());
            if (S.restarts(dl)) g = S.grid;
        }
        if (g.empty()) return {};
        if (hasSafe) {
            for (auto& c : g) if (!c) c = safeCh;
            return toRows(g, n);
        }
        FreeFiller FF(T, F, rng, g);
        if (!FF.fill(alphabet, dl)) return {};
        return toRows(FF.grid, n);
    };

    // No safe letter: get a first valid grid from the local search, starting
    // at a size where plain row packing fits and growing until it succeeds.
    if (best.empty()) {
        int n = lower;
        while (shelfGrid(required, n, alphabet[0], false).empty()) ++n;
        while (best.empty() && now() < deadline) {
            offer(attempt(n, now() + min(0.3, (deadline - now()) / 3)));
            if (best.empty()) n += max(1, n / 8);
        }
    }

    // Exact phase: complete search from the lower bound upward. The first
    // size it solves is provably minimum; sizes it exhausts are infeasible.
    int provenLow = lower;
    if (hasSafe && !required.empty()) {
        // Proofs only pay off on small inputs, where the bound is often tight.
        double share = 0.2 * min(1.0, 30.0 / required.size());
        double exDl = min(deadline, start + SEARCH_SECONDS * share);
        int n0 = lower;
        for (int n = n0; (best.empty() || n < (int)best.size()) && now() < exDl; ++n) {
            Torus T(n);
            Needles F(forbidden, n);
            TreeSearch S(T, F, required, rng());
            int r = S.solve(exDl, LLONG_MAX);
            if (r == 1) {
                vector<char> g = S.grid;
                for (auto& c : g) if (!c) c = safeCh;
                vector<string> rows(n, string(n, 'A'));
                for (int c = 0; c < n * n; ++c) rows[c / n][c % n] = g[c];
                if (offer(rows) && n == provenLow) return best;   // provably minimum
            }
            if (r != 0) break;
            provenLow = n + 1;
        }
    }
    if (finished()) return best;

    // Local-search phase: binary search over N, then grind at best-1.
    double finalSlice = 0.3;
    const int floorT = max(provenLow, fullN);
    int softLo = floorT;
    while (!best.empty() ? (int)best.size() > floorT : true) {
        double rem = deadline - now();
        if (rem <= 0.002) break;
        int hiT = best.empty() ? max(floorT, lower) + 4 : (int)best.size() - 1;
        int t;
        double slice;
        if (softLo < hiT) {
            t = (softLo + hiT) / 2;
            slice = max(0.03, rem / 6);
        } else {
            // Several independent shorter runs beat one long run at the frontier.
            t = hiT;
            slice = min(rem, max(finalSlice, rem / 4));
            if (rem - slice < finalSlice * 0.5) slice = rem;
        }
        double t0 = now();
        vector<string> g = attempt(t, now() + slice);
        (void)t0;
        if (!g.empty() && offer(g)) continue;
        if (best.empty()) { softLo = t + 1; continue; }
        softLo = max(softLo, t + 1);
    }
    if (best.empty()) throw SearchLimitError("No valid grid found within the budget; increase SEARCH_SECONDS");
    return best;
}

#ifndef NO_MAIN
int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    vector<string> tokens;
    string tok;
    while (cin >> tok) tokens.push_back(tok);
    if (tokens.empty()) return 0;
    size_t pos = 0;
    auto readWords = [&](const char* label) {
        if (pos >= tokens.size()) throw invalid_argument(string("Missing ") + label + " word count");
        long long count = stoll(tokens[pos++]);
        if (count < 0 || pos + count > tokens.size())
            throw invalid_argument(string("Bad ") + label + " word count");
        vector<string> words(tokens.begin() + pos, tokens.begin() + pos + count);
        pos += count;
        return words;
    };
    try {
        vector<string> req = readWords("required");
        vector<string> forb = readWords("forbidden");
        vector<string> grid = generate_grid(req, forb);
        string out;
        for (const string& row : grid) { out += row; out += '\n'; }
        cout << out;
    } catch (const exception& e) {
        cerr << e.what() << '\n';
        return 1;
    }
    return 0;
}
#endif
