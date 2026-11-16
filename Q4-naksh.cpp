// Masyu shortest-loop solver
// Strategy: edge-based constraint propagation (degree, pearl rules, no premature sub-loop),
// DFS/branch-and-bound for an initial loop, then Large Neighbourhood Search:
// repeatedly free a rectangular window, keep everything outside fixed, and re-solve
// the window exactly (B&B with a lower bound) looking for a shorter loop.
#include <bits/stdc++.h>
using namespace std;
string ltrim(const string &);
string rtrim(const string &);
// Compact CDCL SAT solver (2-watched literals, 1UIP, VSIDS heap, phase saving, Luby restarts)



struct CDCL {
    int nv = 0;
    vector<vector<int>> cls;          // clause literal arrays (lit = 2*v + neg)
    vector<vector<int>> W;            // watches per literal
    vector<signed char> val;          // per var: -1 unassigned, 0 false, 1 true
    vector<int> lvl, rsn, trail, lim;
    size_t qhead = 0;
    vector<double> act; double inc = 1.0;
    vector<char> pol, seen; vector<int> toClear;
    vector<int> heap, hpos;
    bool unsat = false;
    long long conflicts = 0;
    // theory hooks: theory() returns 0 ok, 1 conflict (clause in thClause, all lits false), 2 done
    function<void(size_t)> onBT;
    function<int(vector<int>&)> theory;
    vector<int> thClause;

    void init(int n) {
        nv = n; W.assign(2 * n, {}); val.assign(n, -1); lvl.assign(n, 0); rsn.assign(n, -1);
        act.assign(n, 0); pol.assign(n, 0); seen.assign(n, 0); hpos.assign(n, -1); heap.clear();
        for (int v = 0; v < n; v++) hins(v);
    }
    // ---- heap (max activity) ----
    bool hless(int a, int b) { return act[a] > act[b]; }
    void hup(int i) { int v = heap[i]; while (i > 0) { int p = (i - 1) / 2; if (!hless(v, heap[p])) break; heap[i] = heap[p]; hpos[heap[i]] = i; i = p; } heap[i] = v; hpos[v] = i; }
    void hdown(int i) {
        int v = heap[i], n = heap.size();
        while (true) { int c = 2 * i + 1; if (c >= n) break; if (c + 1 < n && hless(heap[c + 1], heap[c])) c++; if (!hless(heap[c], v)) break; heap[i] = heap[c]; hpos[heap[i]] = i; i = c; }
        heap[i] = v; hpos[v] = i;
    }
    void hins(int v) { if (hpos[v] >= 0) return; heap.push_back(v); hpos[v] = heap.size() - 1; hup(hpos[v]); }
    int hpop() { int v = heap[0]; heap[0] = heap.back(); hpos[heap[0]] = 0; heap.pop_back(); hpos[v] = -1; if (!heap.empty()) hdown(0); return v; }
    void bump(int v) {
        act[v] += inc;
        if (act[v] > 1e100) { for (auto& a : act) a *= 1e-100; inc *= 1e-100; }
        if (hpos[v] >= 0) hup(hpos[v]);
    }

    inline int lv(int l) const { int v = val[l >> 1]; return v < 0 ? -1 : (v ^ (l & 1)); }
    int level() const { return lim.size(); }
    void assignLit(int l, int r) { int v = l >> 1; val[v] = !(l & 1); lvl[v] = level(); rsn[v] = r; trail.push_back(l); }
    void backtrack(int L) {
        if (level() <= L) return;
        for (int i = (int)trail.size() - 1; i >= lim[L]; i--) { int v = trail[i] >> 1; pol[v] = val[v]; val[v] = -1; rsn[v] = -1; hins(v); }
        trail.resize(lim[L]); lim.resize(L); qhead = trail.size();
        if (onBT) onBT(trail.size());
    }
    // add clause at level 0 (backtracks first)
    void addClause(vector<int> c) {
        if (unsat) return;
        backtrack(0);
        sort(c.begin(), c.end()); c.erase(unique(c.begin(), c.end()), c.end());
        vector<int> d;
        for (size_t i = 0; i < c.size(); i++) {
            if (i + 1 < c.size() && (c[i] ^ 1) == c[i + 1]) return; // tautology
            int x = lv(c[i]); if (x == 1) return; if (x == 0) continue; d.push_back(c[i]);
        }
        if (d.empty()) { unsat = true; return; }
        if (d.size() == 1) { assignLit(d[0], -1); if (propagate() >= 0) unsat = true; return; }
        int id = cls.size(); cls.push_back(d); W[d[0]].push_back(id); W[d[1]].push_back(id);
    }
    int propagate() { // returns conflict clause id or -1
        while (qhead < trail.size()) {
            int p = trail[qhead++]; int fl = p ^ 1;
            vector<int>& ws = W[fl];
            size_t i = 0, j = 0;
            while (i < ws.size()) {
                int ci = ws[i++]; vector<int>& c = cls[ci];
                if (c[0] == fl) swap(c[0], c[1]);
                if (lv(c[0]) == 1) { ws[j++] = ci; continue; }
                bool found = false;
                for (size_t k = 2; k < c.size(); k++) if (lv(c[k]) != 0) { swap(c[1], c[k]); W[c[1]].push_back(ci); found = true; break; }
                if (found) continue;
                ws[j++] = ci;
                if (lv(c[0]) == 0) { while (i < ws.size()) ws[j++] = ws[i++]; ws.resize(j); return ci; }
                assignLit(c[0], ci);
            }
            ws.resize(j);
        }
        return -1;
    }
    void analyze(int confl, vector<int>& out, int& btl) {
        out.clear(); out.push_back(-1); int pathC = 0, p = -1; int idx = trail.size() - 1;
        do {
            vector<int>& c = cls[confl];
            for (size_t k = (p == -1 ? 0 : 1); k < c.size(); k++) {
                int q = c[k]; int v = q >> 1;
                if (!seen[v] && lvl[v] > 0) {
                    seen[v] = 1; bump(v);
                    if (lvl[v] >= level()) pathC++; else out.push_back(q);
                }
            }
            while (!seen[trail[idx] >> 1]) idx--;
            p = trail[idx]; idx--; confl = rsn[p >> 1]; seen[p >> 1] = 0; pathC--;
            if (pathC > 0 && confl >= 0) { vector<int>& cc = cls[confl]; if (cc[0] != p) { for (size_t k = 1; k < cc.size(); k++) if (cc[k] == p) { swap(cc[0], cc[k]); break; } } }
        } while (pathC > 0);
        out[0] = p ^ 1;
        // simple minimisation: drop literals whose reason clause is fully covered
        size_t j = 1; toClear.assign(out.begin() + 1, out.end());
        for (size_t i = 1; i < out.size(); i++) {
            int v = out[i] >> 1; int r = rsn[v]; bool keep = true;
            if (r >= 0) { keep = false; for (size_t k = 1; k < cls[r].size(); k++) { int u = cls[r][k] >> 1; if (!seen[u] && lvl[u] > 0) { keep = true; break; } } }
            if (keep) out[j++] = out[i];
        }
        out.resize(j);
        for (int l : toClear) seen[l >> 1] = 0;
        btl = 0;
        if (out.size() > 1) { size_t mi = 1; for (size_t i = 2; i < out.size(); i++) if (lvl[out[i] >> 1] > lvl[out[mi] >> 1]) mi = i; swap(out[1], out[mi]); btl = lvl[out[1] >> 1]; }
        inc *= 1.0 / 0.95;
    }
    static double luby(double y, int x) {
        int size, seq; for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);
        while (size - 1 != x) { size = (size - 1) >> 1; seq--; x = x % size; }
        return pow(y, seq);
    }
    // returns 1 sat, 0 unsat, -1 timeout
    int solve(function<bool()> timeUp) {
        if (unsat) return 0;
        backtrack(0);
        if (propagate() >= 0) { unsat = true; return 0; }
        vector<int> learnt; int rest = 0;
        while (true) {
            long long budget = (long long)(luby(2, rest++) * 100); long long cc = 0;
            while (true) {
                int confl = propagate();
                if (confl >= 0) {
                    conflicts++; cc++;
                    if (level() == 0) { unsat = true; return 0; }
                    int btl; analyze(confl, learnt, btl);
                    backtrack(btl);
                    if (learnt.size() == 1) assignLit(learnt[0], -1);
                    else { int id = cls.size(); cls.push_back(learnt); W[learnt[0]].push_back(id); W[learnt[1]].push_back(id); assignLit(learnt[0], id); }
                    if ((conflicts & 127) == 0 && timeUp()) return -1;
                } else {
                    if (theory) {
                        int tr = theory(thClause);
                        if (tr == 2) return 1;
                        if (tr == 3) { // theory propagation: thClause[0] implied, others false
                            vector<int>& c = thClause;
                            size_t mi = 1; for (size_t i = 2; i < c.size(); i++) if (lvl[c[i] >> 1] > lvl[c[mi] >> 1]) mi = i; swap(c[1], c[mi]);
                            int id = cls.size(); cls.push_back(c); W[c[0]].push_back(id); W[c[1]].push_back(id);
                            assignLit(c[0], id);
                            continue;
                        }
                        if (tr == 1) {
                            conflicts++; cc++;
                            vector<int>& c = thClause;
                            int maxL = 0; for (int l : c) maxL = max(maxL, lvl[l >> 1]);
                            if (maxL == 0 || c.empty()) { unsat = true; return 0; }
                            backtrack(maxL);
                            // order: two highest levels first
                            for (int k = 0; k < 2 && k < (int)c.size(); k++) { size_t mi = k; for (size_t i = k + 1; i < c.size(); i++) if (lvl[c[i] >> 1] > lvl[c[mi] >> 1]) mi = i; swap(c[k], c[mi]); }
                            int confl;
                            if (c.size() == 1) { cls.push_back(c); confl = cls.size() - 1; }
                            else { int id = cls.size(); cls.push_back(c); W[c[0]].push_back(id); W[c[1]].push_back(id); confl = id; }
                            int btl; analyze(confl, learnt, btl);
                            backtrack(btl);
                            if (learnt.size() == 1) assignLit(learnt[0], -1);
                            else { int id = cls.size(); cls.push_back(learnt); W[learnt[0]].push_back(id); W[learnt[1]].push_back(id); assignLit(learnt[0], id); }
                            if ((conflicts & 127) == 0 && timeUp()) return -1;
                            continue;
                        }
                    }
                    if (cc >= budget) { backtrack(0); break; }
                    int v = -1;
                    while (!heap.empty()) { int x = hpop(); if (val[x] < 0) { v = x; break; } }
                    if (v < 0) return 1;
                    lim.push_back(trail.size());
                    assignLit(2 * v + (pol[v] ? 0 : 1), -1);
                }
            }
        }
    }
};

typedef chrono::steady_clock Clk;
static Clk::time_point T0;
static double elapsed() { return chrono::duration<double>(Clk::now() - T0).count(); }

int R, C, N, E;
vector<char> P;                 // pearl per cell: 0, 'W', 'B'
vector<int> EA, EB;             // edge endpoints
vector<array<int, 4>> CE, CN;   // cell -> edge / neighbour in dir (N,E,S,W), -1 if none
int totalP;

static uint64_t rngState = 88172645463325252ULL;
static inline uint64_t rnd() { rngState ^= rngState << 7; rngState ^= rngState >> 9; return rngState; }
static inline int rndInt(int lo, int hi) { return lo + (int)(rnd() % (uint64_t)(hi - lo + 1)); }

struct Solver {
    vector<signed char> st;
    vector<int> onC, unkC, endp, plen;
    int Eon = 0, deg1 = 0, touched = 0;
    bool solved = false; int solvedPos = -1;
    vector<int> trail, trailM;
    struct MT { int idx, oe, ol; };
    vector<MT> mtrail;
    vector<int> q; size_t qh = 0; vector<char> inq;

    void init() {
        st.assign(E, -1); onC.assign(N, 0); unkC.assign(N, 0);
        endp.resize(N); plen.assign(N, 0);
        for (int i = 0; i < N; i++) endp[i] = i;
        for (int e = 0; e < E; e++) { unkC[EA[e]]++; unkC[EB[e]]++; }
        Eon = deg1 = touched = 0; solved = false; solvedPos = -1;
        trail.clear(); trailM.clear(); mtrail.clear();
        q.clear(); qh = 0; inq.assign(N, 0);
    }
    // Build state directly: all edges = cur except 'freeE' edges (unknown). loopSeq: loop cells in order,
    // loopE[i] = edge between loopSeq[i] and loopSeq[i+1].
    bool loadWindow(const vector<signed char>& cur, const vector<char>& freeE, const vector<int>& loopSeq, const vector<int>& loopE) {
        trail.clear(); trailM.clear(); mtrail.clear(); q.clear(); qh = 0;
        solved = false; solvedPos = -1;
        for (int e = 0; e < E; e++) st[e] = freeE[e] ? -1 : cur[e];
        std::fill(onC.begin(), onC.end(), 0); std::fill(unkC.begin(), unkC.end(), 0);
        Eon = 0;
        for (int e = 0; e < E; e++) { if (st[e] == 1) { onC[EA[e]]++; onC[EB[e]]++; Eon++; } else if (st[e] == -1) { unkC[EA[e]]++; unkC[EB[e]]++; } }
        deg1 = 0; touched = 0;
        int L = loopSeq.size();
        for (int x = 0; x < N; x++) { endp[x] = x; plen[x] = 0; }
        for (int x : loopSeq) { if (onC[x] == 1) deg1++; if (P[x] && onC[x] > 0) touched++; }
        // find a removed edge to start the walk
        int s0 = -1; for (int i = 0; i < L; i++) if (freeE[loopE[i]]) { s0 = i; break; }
        if (s0 < 0) return false;
        // walk paths: starting after removed edge s0
        int i = (s0 + 1) % L; int cnt = 0;
        while (cnt < L) {
            // path starts at loopSeq[i]
            int a = loopSeq[i]; int len = 0;
            while (!freeE[loopE[i]]) { i = (i + 1) % L; len++; cnt++; }
            int b = loopSeq[i]; // edge loopE[i] is removed
            endp[a] = b; endp[b] = a; plen[a] = plen[b] = len;
            i = (i + 1) % L; cnt++;
        }
        // cells not on loop: endp self (set lazily: ensure)
        return true;
    }
    inline void enq(int x) { if (!inq[x]) { inq[x] = 1; q.push_back(x); } }
    inline void enqAround(int x) { enq(x); for (int d = 0; d < 4; d++) if (CN[x][d] >= 0) enq(CN[x][d]); }
    inline int val(int e) const { return e < 0 ? 0 : st[e]; }

    bool set(int e, int v) {
        if (e < 0) return v == 0;
        if (st[e] == v) return true;
        if (st[e] != -1) return false;
        if (v == 1 && solved) return false;
        st[e] = (signed char)v;
        int a = EA[e], b = EB[e];
        trail.push_back(e); trailM.push_back((int)mtrail.size());
        unkC[a]--; unkC[b]--;
        enqAround(a); enqAround(b);
        if (v == 1) {
            int xs[2] = {a, b};
            for (int x : xs) {
                if (onC[x] == 0) { deg1++; if (P[x]) touched++; }
                else if (onC[x] == 1) deg1--;
                onC[x]++;
            }
            Eon++;
            if (onC[a] > 2 || onC[b] > 2) return false;
            int A = endp[a], B = endp[b];
            if (A == b) { // closes a cycle
                if (plen[a] + 1 == Eon && touched == totalP) { solved = true; solvedPos = (int)trail.size() - 1; return true; }
                return false;
            }
            int nl = plen[a] + plen[b] + 1;
            mtrail.push_back({A, endp[A], plen[A]});
            mtrail.push_back({B, endp[B], plen[B]});
            endp[A] = B; endp[B] = A; plen[A] = plen[B] = nl;
            if (!(nl == Eon && touched == totalP)) {
                for (int d = 0; d < 4; d++) if (CN[A][d] == B) { int x = CE[A][d]; if (st[x] == -1) return set(x, 0); }
            }
        }
        return true;
    }
    void undo(size_t t) {
        while (trail.size() > t) {
            int e = trail.back(); int ms = trailM.back(); trail.pop_back(); trailM.pop_back();
            if (solvedPos == (int)trail.size()) { solved = false; solvedPos = -1; }
            while ((int)mtrail.size() > ms) { MT m = mtrail.back(); mtrail.pop_back(); endp[m.idx] = m.oe; plen[m.idx] = m.ol; }
            int v = st[e]; st[e] = -1; int a = EA[e], b = EB[e];
            unkC[a]++; unkC[b]++;
            if (v == 1) {
                int xs[2] = {a, b};
                for (int x : xs) {
                    onC[x]--;
                    if (onC[x] == 0) { deg1--; if (P[x]) touched--; }
                    else if (onC[x] == 1) deg1++;
                }
                Eon--;
            }
        }
    }
    bool prop(int x) {
        int on = onC[x], uk = unkC[x];
        if (on > 2) return false;
        if (on == 2) { if (uk > 0) for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e >= 0 && st[e] == -1 && !set(e, 0)) return false; } }
        else if (on == 1) {
            if (uk == 0) return false;
            if (uk == 1) for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e >= 0 && st[e] == -1) { if (!set(e, 1)) return false; break; } }
        } else {
            if (P[x]) {
                if (uk < 2) return false;
                if (uk == 2) for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e >= 0 && st[e] == -1 && !set(e, 1)) return false; }
            } else if (uk == 1) {
                for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e >= 0 && st[e] == -1) { if (!set(e, 0)) return false; break; } }
            }
        }
        if (P[x] == 'B') {
            for (int d = 0; d < 4; d++) {
                int e = CE[x][d], o = CE[x][(d + 2) & 3];
                int f = (e >= 0) ? CE[CN[x][d]][d] : -1;
                if (e >= 0 && val(f) == 0 && !set(e, 0)) return false;
                if (val(e) == 1) { if (!set(f, 1) || !set(o, 0)) return false; }
                else if (val(e) == 0) { if (!set(o, 1)) return false; }
            }
        } else if (P[x] == 'W') {
            int eN = CE[x][0], eE = CE[x][1], eS = CE[x][2], eW = CE[x][3];
            int hA = eW >= 0 ? CE[CN[x][3]][3] : -1, hB = eE >= 0 ? CE[CN[x][1]][1] : -1;
            int vA = eN >= 0 ? CE[CN[x][0]][0] : -1, vB = eS >= 0 ? CE[CN[x][2]][2] : -1;
            bool canH = eE >= 0 && eW >= 0 && val(eE) != 0 && val(eW) != 0 && val(eN) != 1 && val(eS) != 1;
            bool canV = eN >= 0 && eS >= 0 && val(eN) != 0 && val(eS) != 0 && val(eE) != 1 && val(eW) != 1;
            if (canH && val(hA) == 1 && val(hB) == 1) canH = false;
            if (canV && val(vA) == 1 && val(vB) == 1) canV = false;
            if (!canH && !canV) return false;
            if (!canV) {
                if (!set(eE, 1) || !set(eW, 1) || !set(eN, 0) || !set(eS, 0)) return false;
                if (val(hA) == 1 && !set(hB, 0)) return false;
                if (val(hB) == 1 && !set(hA, 0)) return false;
            }
            if (!canH) {
                if (!set(eN, 1) || !set(eS, 1) || !set(eE, 0) || !set(eW, 0)) return false;
                if (val(vA) == 1 && !set(vB, 0)) return false;
                if (val(vB) == 1 && !set(vA, 0)) return false;
            }
        }
        return true;
    }
    void clearQ() { for (size_t i = qh; i < q.size(); i++) inq[q[i]] = 0; q.clear(); qh = 0; }
    bool propagate() {
        while (qh < q.size()) {
            int x = q[qh++]; inq[x] = 0;
            if (!prop(x)) { for (size_t i = qh; i < q.size(); i++) inq[q[i]] = 0; q.clear(); qh = 0; return false; }
        }
        q.clear(); qh = 0; return true;
    }
};

// Full independent validity check of a complete edge assignment.
bool verify(const vector<signed char>& st, int& len) {
    vector<int> deg(N, 0); len = 0;
    for (int e = 0; e < E; e++) if (st[e] == 1) { deg[EA[e]]++; deg[EB[e]]++; len++; }
    int start = -1, cells = 0;
    for (int i = 0; i < N; i++) {
        if (deg[i] != 0 && deg[i] != 2) return false;
        if (deg[i] == 2) { cells++; start = i; }
        if (P[i] && deg[i] != 2) return false;
    }
    if (start < 0) return false;
    auto on = [&](int x, int d) { int e = CE[x][d]; return e >= 0 && st[e] == 1; };
    auto straight = [&](int x) { return (on(x, 0) && on(x, 2)) || (on(x, 1) && on(x, 3)); };
    int prev = -1, cur = start, cnt = 0;
    do {
        int nxt = -1;
        for (int d = 0; d < 4; d++) if (on(cur, d) && CN[cur][d] != prev) { nxt = CN[cur][d]; break; }
        if (nxt < 0) { // both neighbours equal prev can't happen; pick any
            for (int d = 0; d < 4; d++) if (on(cur, d)) { nxt = CN[cur][d]; break; }
        }
        prev = cur; cur = nxt; cnt++;
        if (cnt > N + 5) return false;
    } while (cur != start);
    if (cnt != cells) return false;
    for (int x = 0; x < N; x++) {
        if (P[x] == 'B') {
            if (straight(x)) return false;
            for (int d = 0; d < 4; d++) if (on(x, d) && !straight(CN[x][d])) return false;
        } else if (P[x] == 'W') {
            if (!straight(x)) return false;
            bool turn = false;
            for (int d = 0; d < 4; d++) if (on(x, d) && !straight(CN[x][d])) turn = true;
            if (!turn) return false;
        }
    }
    return true;
}


// ---- SAT-based initial loop with lazy sub-loop cuts ----
bool satInitial(vector<signed char>& outSt, double tl) {
    CDCL sv; sv.init(E);
    vector<signed char> dbgSol;
    if (const char* ff = getenv("SOLFILE")) {
        ifstream in(ff); vector<string> sol; string l; while (in >> l) sol.push_back(l);
        dbgSol.assign(E, 0);
        for (int x = 0; x < N; x++) for (int d = 1; d <= 2; d++) if (CE[x][d] >= 0) { char ch = sol[x / C][x % C]; string m = (d==1?"-LF":"|F7"); dbgSol[CE[x][d]] = m.find(ch) != string::npos; }
    }
    auto chk = [&](const vector<int>& c, const char* tag) {
        if (dbgSol.empty()) return; for (int l : c) if (dbgSol[l >> 1] == !(l & 1)) return;
        cerr << "VIOLATED clause " << tag << " size " << c.size() << "\n";
    };
    auto ADDC = [&](vector<int> c) { chk(c, "base"); sv.addClause(c); };
    auto pos = [](int e) { return 2 * e; };
    auto neg = [](int e) { return 2 * e + 1; };
    for (int x = 0; x < N; x++) {
        vector<int> I; for (int d = 0; d < 4; d++) if (CE[x][d] >= 0) I.push_back(CE[x][d]);
        for (size_t i = 0; i < I.size(); i++) { vector<int> c{neg(I[i])}; for (size_t j = 0; j < I.size(); j++) if (j != i) c.push_back(pos(I[j])); ADDC(c); }
        for (size_t a = 0; a < I.size(); a++) for (size_t b = a + 1; b < I.size(); b++) for (size_t c = b + 1; c < I.size(); c++) ADDC({neg(I[a]), neg(I[b]), neg(I[c])});
        if (P[x]) { vector<int> c; for (int e : I) c.push_back(pos(e)); ADDC(c); }
        if (P[x] == 'B') {
            for (int d = 0; d < 4; d++) {
                int e = CE[x][d]; if (e < 0) continue;
                int f = CE[CN[x][d]][d], o = CE[x][(d + 2) & 3];
                if (f < 0) ADDC({neg(e)}); else ADDC({neg(e), pos(f)});
                if (o >= 0) ADDC({neg(e), neg(o)});
            }
        } else if (P[x] == 'W') {
            for (int ax = 0; ax < 2; ax++) {
                int d1 = ax == 0 ? 1 : 0, d2 = d1 + 2; // E/W or N/S
                int e1 = CE[x][d1], e2 = CE[x][d2];
                if (e1 < 0 || e2 < 0) { if (e1 >= 0) ADDC({neg(e1)}); if (e2 >= 0) ADDC({neg(e2)}); continue; }
                ADDC({neg(e1), pos(e2)}); ADDC({neg(e2), pos(e1)});
                int f1 = CE[CN[x][d1]][d1], f2 = CE[CN[x][d2]][d2];
                if (f1 >= 0 && f2 >= 0) ADDC({neg(e1), neg(f1), neg(f2)});
            }
        }
    }
    vector<int> comp(N), deg(N), outside(N);
    for (int it = 0; it < 100000; it++) {
        int r = sv.solve([&]() { return elapsed() > tl; });
        if (r != 1) { if (getenv("MASYU_DEBUG")) cerr << "sat r=" << r << " it=" << it << "\n"; return false; }
        vector<signed char> st(E);
        for (int e = 0; e < E; e++) st[e] = sv.val[e] == 1;
        fill(comp.begin(), comp.end(), -1);
        int nc = 0; vector<vector<int>> cyc; vector<int> pc;
        for (int x = 0; x < N; x++) {
            if (comp[x] >= 0) continue;
            bool any = false; for (int d = 0; d < 4; d++) if (CE[x][d] >= 0 && st[CE[x][d]]) any = true;
            if (!any) continue;
            vector<int> cells; vector<int> stk{x}; comp[x] = nc;
            while (!stk.empty()) { int y = stk.back(); stk.pop_back(); cells.push_back(y);
                for (int d = 0; d < 4; d++) { int e = CE[y][d]; if (e >= 0 && st[e] && comp[CN[y][d]] < 0) { comp[CN[y][d]] = nc; stk.push_back(CN[y][d]); } } }
            int p = 0; for (int y : cells) if (P[y]) p++;
            cyc.push_back(cells); pc.push_back(p); nc++;
        }
        int full = -1; for (int i = 0; i < nc; i++) if (pc[i] == totalP) full = i;
        if (getenv("SATDBG")) cerr << "it " << it << " t=" << elapsed() << " comps=" << nc << " confl=" << sv.conflicts << " cls=" << sv.cls.size() << "\n";
        if (full >= 0) {
            for (int e = 0; e < E; e++) if (st[e] && comp[EA[e]] != full) st[e] = 0;
            int L; if (verify(st, L)) { outSt = st; return true; }
            if (getenv("MASYU_DEBUG")) cerr << "sat verify fail it=" << it << "\n"; return false;
        }
        for (int i = 0; i < nc; i++) {
            if (pc[i] == 0) continue;
            vector<int> c;
            for (int y : cyc[i]) for (int d = 0; d < 4; d++) { int e = CE[y][d]; if (e >= 0 && comp[CN[y][d]] != i) c.push_back(pos(e)); }
            chk(c, "cut"); sv.addClause(c);
            fill(outside.begin(), outside.end(), 0);
            vector<int> stk;
            for (int x = 0; x < N; x++) { int r = x / C, cc = x % C; if ((r == 0 || r == R - 1 || cc == 0 || cc == C - 1) && comp[x] != i) { outside[x] = 1; stk.push_back(x); } }
            while (!stk.empty()) { int y = stk.back(); stk.pop_back(); for (int d = 0; d < 4; d++) { int z = CN[y][d]; if (z >= 0 && !outside[z] && comp[z] != i) { outside[z] = 1; stk.push_back(z); } } }
            bool pearlOut = false; int inner = 0;
            for (int x = 0; x < N; x++) { if (P[x] && outside[x]) pearlOut = true; if (!outside[x] && comp[x] != i) inner++; }
            if (pearlOut && inner > 0) {
                vector<int> c2;
                for (int y : cyc[i]) for (int d = 0; d < 4; d++) { int e = CE[y][d]; if (e >= 0 && outside[CN[y][d]]) c2.push_back(pos(e)); }
                chk(c2, "regioncut"); sv.addClause(c2);
            }
        }
        if (sv.unsat) return false;
    }
    return false;
}


// ---- CDCL with lazy sub-loop / connectivity clauses generated during search ----
bool satLazy(vector<signed char>& outSt, double tl, int connThrArg, uint64_t seed) {
    CDCL sv; sv.init(E);
    if (seed) { uint64_t z = seed * 0x9E3779B97F4A7C15ULL + 12345; for (int v = 0; v < E; v++) { z ^= z << 7; z ^= z >> 9; sv.act[v] = (z % 1000) * 1e-4; } for (int i = E / 2; i >= 0; i--) if (i < (int)sv.heap.size()) sv.hdown(i); }
    auto pos = [](int e) { return 2 * e; };
    auto neg = [](int e) { return 2 * e + 1; };
    auto ADD = [&](vector<int> c) { sv.addClause(c); };
    for (int x = 0; x < N; x++) {
        vector<int> I; for (int d = 0; d < 4; d++) if (CE[x][d] >= 0) I.push_back(CE[x][d]);
        for (size_t i = 0; i < I.size(); i++) { vector<int> c{neg(I[i])}; for (size_t j = 0; j < I.size(); j++) if (j != i) c.push_back(pos(I[j])); ADD(c); }
        for (size_t a = 0; a < I.size(); a++) for (size_t b = a + 1; b < I.size(); b++) for (size_t c = b + 1; c < I.size(); c++) ADD({neg(I[a]), neg(I[b]), neg(I[c])});
        if (P[x]) { vector<int> c; for (int e : I) c.push_back(pos(e)); ADD(c); }
        if (P[x] == 'B') {
            for (int d = 0; d < 4; d++) {
                int e = CE[x][d]; if (e < 0) continue;
                int f = CE[CN[x][d]][d], o = CE[x][(d + 2) & 3];
                if (f < 0) ADD({neg(e)}); else ADD({neg(e), pos(f)});
                if (o >= 0) ADD({neg(e), neg(o)});
            }
        } else if (P[x] == 'W') {
            for (int ax = 0; ax < 2; ax++) {
                int d1 = ax == 0 ? 1 : 0, d2 = d1 + 2;
                int e1 = CE[x][d1], e2 = CE[x][d2];
                if (e1 < 0 || e2 < 0) { if (e1 >= 0) ADD({neg(e1)}); if (e2 >= 0) ADD({neg(e2)}); continue; }
                ADD({neg(e1), pos(e2)}); ADD({neg(e2), pos(e1)});
                int f1 = CE[CN[x][d1]][d1], f2 = CE[CN[x][d2]][d2];
                if (f1 >= 0 && f2 >= 0) ADD({neg(e1), neg(f1), neg(f2)});
            }
        }
    }
    if (sv.unsat) return false;
    // theory state
    vector<int> endp(N), pc(N);
    for (int x = 0; x < N; x++) { endp[x] = x; pc[x] = P[x] ? 1 : 0; }
    struct Log { int pos, idx, oe, op; };
    vector<Log> lg; size_t processed = 0;
    int firstPearl = -1; for (int x = 0; x < N; x++) if (P[x]) { firstPearl = x; break; }
    vector<int> mark(N, 0), bq, cl2; int stamp = 0;
    int doneCycleEdge = -1; int fcount = 0; bool firstDone = false; size_t checkedPos = 0; vector<int> lmark(N, 0), lq; int lstamp = 0; bool usePathProp = getenv("NOPATHPROP") == nullptr; int connMode = getenv("CONNMODE") ? atoi(getenv("CONNMODE")) : 0; int localK = getenv("LOCALK") ? atoi(getenv("LOCALK")) : 40; int connThr = connThrArg;
    sv.onBT = [&](size_t sz) {
        while (!lg.empty() && lg.back().pos >= (int)sz) { Log l = lg.back(); lg.pop_back(); endp[l.idx] = l.oe; pc[l.idx] = l.op; }
        if (processed > sz) processed = sz;
        if (checkedPos > sz) checkedPos = sz;
    };
    sv.theory = [&](vector<int>& cl) -> int {
        while (processed < sv.trail.size()) {
            int lit = sv.trail[processed];
            if (!(lit & 1)) {
                int e = lit >> 1, a = EA[e], b = EB[e];
                int A = endp[a], B = endp[b];
                if (A == b) {
                    // cycle closed: collect edges
                    int pearls = pc[a];
                    if (pearls == totalP) { doneCycleEdge = e; return 2; }
                    cl.clear(); cl.push_back(neg(e));
                    int prev = b, cur = a;
                    while (cur != b) {
                        int nx = -1;
                        for (int d = 0; d < 4; d++) { int f = CE[cur][d]; if (f >= 0 && f != e && sv.val[f] == 1 && CN[cur][d] != prev) { nx = CN[cur][d]; cl.push_back(neg(f)); break; } }
                        if (nx < 0) break;
                        prev = cur; cur = nx;
                    }
                    return 1;
                }
                int p = (int)processed;
                lg.push_back({p, A, endp[A], pc[A]}); lg.push_back({p, B, endp[B], pc[B]});
                int np = pc[A] + pc[B];
                endp[A] = B; endp[B] = A; pc[A] = pc[B] = np;
                if (np < totalP && usePathProp) {
                    int g = -1; for (int d = 0; d < 4; d++) if (CN[A][d] == B) g = CE[A][d];
                    if (g >= 0 && sv.val[g] < 0) {
                        processed++;
                        cl.clear(); cl.push_back(neg(g));
                        int prev = -1, cur = A;
                        while (cur != B) {
                            int nx = -1;
                            for (int d = 0; d < 4; d++) { int f = CE[cur][d]; if (f >= 0 && f != g && sv.val[f] == 1 && CN[cur][d] != prev) { nx = CN[cur][d]; cl.push_back(neg(f)); break; } }
                            if (nx < 0) break;
                            prev = cur; cur = nx;
                        }
                        if (cl.size() >= 2) return 3;
                        processed--;
                    }
                }
            }
            processed++;
        }
        // connectivity of pearls over non-false edges (throttled)
        bool need = !firstDone;
        if (connMode == 0) {
            int fc = 0; for (size_t i = checkedPos; i < sv.trail.size(); i++) if (sv.trail[i] & 1) fc++;
            if (fc >= connThr) need = true;
            if (!need) return 0; // keep checkedPos so false edges accumulate
        }
        for (size_t i = checkedPos; i < sv.trail.size() && !need; i++) {
            int lit = sv.trail[i]; if (!(lit & 1)) continue;
            int e = lit >> 1, a = EA[e], b = EB[e];
            int stp = ++lstamp; lq.clear(); lq.push_back(a); lmark[a] = stp; bool found = false;
            for (size_t h = 0; h < lq.size() && !found && (int)lq.size() < localK; h++) {
                int x = lq[h];
                for (int d = 0; d < 4; d++) { int f = CE[x][d]; if (f < 0 || sv.val[f] == 0) continue; int y = CN[x][d]; if (lmark[y] != stp) { if (y == b) { found = true; break; } lmark[y] = stp; lq.push_back(y); } }
            }
            if (!found) need = true;
        }
        if (!need) { checkedPos = sv.trail.size(); return 0; }
        firstDone = true;
        size_t trailNow = sv.trail.size();
        ++stamp; bq.clear(); bq.push_back(firstPearl); mark[firstPearl] = stamp; int got = 0;
        for (size_t h = 0; h < bq.size(); h++) {
            int x = bq[h]; if (P[x]) { if (++got == totalP) { checkedPos = trailNow; return 0; } }
            for (int d = 0; d < 4; d++) { int f = CE[x][d]; if (f < 0 || sv.val[f] == 0) continue; int y = CN[x][d]; if (mark[y] != stamp) { mark[y] = stamp; bq.push_back(y); } }
        }
        cl.clear();
        for (int x : bq) for (int d = 0; d < 4; d++) { int f = CE[x][d]; if (f >= 0 && mark[CN[x][d]] != stamp) cl.push_back(pos(f)); }
        // try the component of an unreached pearl; keep the smaller cut
        int up = -1; for (int x = 0; x < N; x++) if (P[x] && mark[x] != stamp) { up = x; break; }
        if (up >= 0) {
            int st2 = ++stamp; bq.clear(); bq.push_back(up); mark[up] = st2;
            for (size_t h = 0; h < bq.size(); h++) { int x = bq[h];
                for (int d = 0; d < 4; d++) { int f = CE[x][d]; if (f < 0 || sv.val[f] == 0) continue; int y = CN[x][d]; if (mark[y] != st2) { mark[y] = st2; bq.push_back(y); } } }
            cl2.clear();
            for (int x : bq) for (int d = 0; d < 4; d++) { int f = CE[x][d]; if (f >= 0 && mark[CN[x][d]] != st2) cl2.push_back(pos(f)); }
            if (cl2.size() < cl.size()) cl.swap(cl2);
        }
        return 1;
    };
    int r = sv.solve([&]() { return elapsed() > tl; });
    if (getenv("MASYU_DEBUG")) cerr << "satLazy r=" << r << " conflicts=" << sv.conflicts << " t=" << elapsed() << "\n";
    if (r != 1) return false;
    // extract the cycle through doneCycleEdge (or, if full assignment, the single cycle)
    vector<signed char> st(E, 0);
    int e0 = doneCycleEdge;
    if (e0 < 0) { for (int e = 0; e < E; e++) if (sv.val[e] == 1) { e0 = e; break; } }
    if (e0 < 0) return false;
    st[e0] = 1; int prev = EA[e0], cur = EB[e0];
    while (cur != EA[e0]) {
        int nx = -1;
        for (int d = 0; d < 4; d++) { int f = CE[cur][d]; if (f >= 0 && !st[f] && sv.val[f] == 1 && CN[cur][d] != prev) { nx = CN[cur][d]; st[f] = 1; break; } }
        if (nx < 0) return false;
        prev = cur; cur = nx;
    }
    int L; if (!verify(st, L)) { if (getenv("MASYU_DEBUG")) cerr << "satLazy verify FAIL\n"; return false; }
    outSt = st; return true;
}

// ---------------- search ----------------
Solver S;
vector<int> actCells, actEdges;
int bestLen; vector<signed char> bestSt;
long long nodes, nodeLimit; double timeLimit; bool aborted; bool stopFirst = false; bool headMode = false; int tailCell = -1; int noise = 0;
vector<int> goalBuf;
bool useConn = false; vector<int> cmark, bfsq; int cstamp = 0;
// all pearls and all cells with an on-edge must lie in one component of the non-off edge graph
bool connectedOK() {
    if (cmark.size() != (size_t)N) cmark.assign(N, 0);
    ++cstamp; int start = -1, need = 0;
    for (int x = 0; x < N; x++) if (S.onC[x] > 0 || P[x]) { need++; if (start < 0) start = x; }
    if (start < 0) return true;
    bfsq.clear(); bfsq.push_back(start); cmark[start] = cstamp; int got = 0;
    for (size_t h = 0; h < bfsq.size(); h++) {
        int x = bfsq[h]; if (S.onC[x] > 0 || P[x]) got++;
        for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e < 0 || S.st[e] == 0) continue; int y = CN[x][d]; if (cmark[y] != cstamp) { cmark[y] = cstamp; bfsq.push_back(y); } }
    }
    return got == need;
}

bool useProbe = false; vector<int> probeList;
// failed-literal probing over frontier edges; returns false on contradiction
bool probe() {
    for (int pass = 0; pass < 4; pass++) {
        bool changed = false;
        probeList.clear();
        for (int x : actCells) {
            if (S.onC[x] == 1 || (S.onC[x] == 0 && P[x]))
                for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e >= 0 && S.st[e] == -1) probeList.push_back(e); }
        }
        for (int e : probeList) {
            if (S.st[e] != -1) continue;
            for (int v = 1; v >= 0; v--) {
                size_t t = S.trail.size();
                bool ok = S.set(e, v) && S.propagate();
                if (!ok) S.clearQ();
                bool sol = S.solved;
                S.undo(t);
                if (sol) continue;
                if (!ok) {
                    if (!S.set(e, 1 - v) || !S.propagate()) { S.clearQ(); return false; }
                    changed = true; break;
                }
            }
        }
        if (!changed) break;
    }
    return true;
}

// full probing over all unknown edges in actEdges, including connectivity test
bool probeAll(int maxPass) {
    for (int pass = 0; pass < maxPass; pass++) {
        bool changed = false;
        for (int e : actEdges) {
            if (S.st[e] != -1) continue;
            for (int v = 1; v >= 0; v--) {
                size_t t = S.trail.size();
                bool ok = S.set(e, v) && S.propagate();
                if (!ok) S.clearQ();
                if (ok && !S.solved && !connectedOK()) ok = false;
                bool sol = S.solved;
                S.undo(t);
                if (sol) continue;
                if (!ok) {
                    if (!S.set(e, 1 - v) || !S.propagate()) { S.clearQ(); return false; }
                    if (!S.solved && !connectedOK()) return false;
                    changed = true; break;
                }
            }
        }
        if (!changed) break;
    }
    return true;
}

void dfs() {
    if (aborted) return;
    if (++nodes > nodeLimit || ((nodes & (useProbe ? 0 : useConn ? 15 : 255)) == 0 && elapsed() > timeLimit)) { aborted = true; return; }
    if (S.solved) {
        size_t t = S.trail.size(); bool ok = true;
        if (S.Eon < bestLen) {
            for (int e : actEdges) if (S.st[e] == -1 && !S.set(e, 0)) { ok = false; break; }
            if (ok) ok = S.propagate();
            int L;
            if (ok && verify(S.st, L) && L < bestLen) { bestLen = L; bestSt = S.st; if (stopFirst) aborted = true; }
        }
        S.undo(t); return;
    }
    int lb = S.Eon + (S.deg1 + 2 * (totalP - S.touched) + 1) / 2;
    if (lb >= bestLen) return;
    if (useConn && !connectedOK()) return;
    if (useProbe) {
        size_t t0 = S.trail.size();
        bool ok = probe();
        if (ok && !S.solved && useConn && !connectedOK()) ok = false;
        if (!ok) { S.undo(t0); return; }
        if (S.trail.size() != t0) { nodes--; dfs(); S.undo(t0); return; }
    }
    // pick endpoint with fewest options
    int bx = -1, bu = 9, px = -1, pu = 9;
    goalBuf.clear();
    int savedTail = tailCell;
    if (headMode) {
        if (tailCell < 0 || S.onC[tailCell] != 1) {
            tailCell = -1; int bl = -1;
            for (int x : actCells) if (S.onC[x] == 1 && S.plen[x] > bl) { bl = S.plen[x]; tailCell = x; }
        }
    }
    for (int x : actCells) {
        if (S.onC[x] == 1) {
            goalBuf.push_back(x);
            if (S.unkC[x] < bu) { bu = S.unkC[x]; bx = x; }
        } else if (S.onC[x] == 0 && P[x]) {
            goalBuf.push_back(x);
            if (S.unkC[x] < pu) { pu = S.unkC[x]; px = x; }
        }
    }
    if (!useConn && goalBuf.size() <= 40) {
        // distance lower bound: every endpoint must reach another endpoint/pearl (not its own mate unless alone)
        int sum = 0;
        for (int x : goalBuf) {
            if (S.onC[x] != 1) continue;
            int mate = S.endp[x], best = 1 << 20, bm = 1 << 20, xr = x / C, xc = x % C;
            for (int y : goalBuf) { if (y == x) continue; int dd = abs(y / C - xr) + abs(y % C - xc); if (y == mate) bm = dd; else best = min(best, dd); }
            if (best == (1 << 20)) best = bm;
            if (best < (1 << 20)) sum += best;
        }
        int lb2 = S.Eon + (sum + 1) / 2;
        if (lb2 >= bestLen) { tailCell = savedTail; return; }
    }
    if (headMode && tailCell >= 0) { bx = S.endp[tailCell]; }
    size_t t = S.trail.size();
    struct TR { int& r; int v; ~TR() { r = v; } } trest{tailCell, savedTail};
    if (bx >= 0) {
        int mate = S.endp[bx];
        int cand[4], sc[4], nc = 0;
        for (int d = 0; d < 4; d++) {
            int e = CE[bx][d]; if (e < 0 || S.st[e] != -1) continue;
            int y = CN[bx][d], yr = y / C, yc = y % C, best = 1 << 29, bestMate = 1 << 29;
            for (int g : goalBuf) {
                if (g == bx) continue;
                int dd = abs(g / C - yr) + abs(g % C - yc);
                if (g == mate) bestMate = dd; else best = min(best, dd);
            }
            if (best == (1 << 29)) best = bestMate;
            cand[nc] = e; sc[nc] = best * 8 + (int)(rnd() % (8 + noise)); nc++;
        }
        for (int i = 0; i < nc; i++) for (int j = i + 1; j < nc; j++) if (sc[j] < sc[i]) { swap(sc[i], sc[j]); swap(cand[i], cand[j]); }
        for (int i = 0; i < nc; i++) {
            if (S.set(cand[i], 1) && S.propagate()) dfs();
            else S.clearQ();
            S.undo(t);
            if (aborted) return;
            lb = S.Eon + (S.deg1 + 2 * (totalP - S.touched) + 1) / 2;
            if (lb >= bestLen) return;
        }
        return;
    }
    if (px >= 0) {
        int e = -1;
        for (int d = 0; d < 4; d++) { int f = CE[px][d]; if (f >= 0 && S.st[f] == -1) { e = f; break; } }
        if (e < 0) return;
        for (int v = 1; v >= 0; v--) {
            if (S.set(e, v) && S.propagate()) dfs();
            else S.clearQ();
            S.undo(t);
            if (aborted) return;
        }
    }
}

vector<string> solveImpl(vector<string> inRows) {
    T0 = Clk::now();
    // Robust parsing: tokens; first is R (optionally followed by C); grid rows are tokens of . W B
    vector<string> rows;
    for (auto& line : inRows) { string t; for (char ch : line) if (ch == '.' || ch == 'W' || ch == 'B' || ch == 'w' || ch == 'b') t += (char)toupper(ch); if (!t.empty()) rows.push_back(t); }
    if (rows.empty()) return {};
    R = rows.size(); C = 0; for (auto& r : rows) C = max(C, (int)r.size());
    for (auto& r : rows) while ((int)r.size() < C) r += '.';
    N = R * C;
    P.assign(N, 0); totalP = 0;
    for (int i = 0; i < R; i++) for (int j = 0; j < C; j++) { char ch = rows[i][j]; if (ch == 'W' || ch == 'B') { P[i * C + j] = ch; totalP++; } }
    CE.assign(N, {-1, -1, -1, -1}); CN.assign(N, {-1, -1, -1, -1});
    const int dr[4] = {-1, 0, 1, 0}, dc[4] = {0, 1, 0, -1};
    for (int i = 0; i < R; i++) for (int j = 0; j < C; j++) for (int d = 0; d < 4; d++) {
        int ni = i + dr[d], nj = j + dc[d];
        if (ni >= 0 && ni < R && nj >= 0 && nj < C) CN[i * C + j][d] = ni * C + nj;
    }
    E = 0;
    for (int x = 0; x < N; x++) for (int d = 1; d <= 2; d++) if (CN[x][d] >= 0) {
        int y = CN[x][d]; EA.push_back(x); EB.push_back(y); CE[x][d] = E; CE[y][(d + 2) & 3] = E; E++;
    }
    double budget = 0.88;
    if (const char* sd = getenv("SEED")) rngState ^= (uint64_t)atoll(sd) * 0x9E3779B97F4A7C15ULL;
    if (const char* bt = getenv("MASYU_BUDGET")) budget = atof(bt);

    // ---- initial solution: global search ----
    S.init();
    for (int x = 0; x < N; x++) S.enq(x);
    S.propagate();
    if (const char* ff = getenv("MASYU_FORCE")) {
        ifstream in(ff); vector<string> sol; string l; while (in >> l) sol.push_back(l);
        S.init(); for (int x = 0; x < N; x++) S.enq(x); bool ok = S.propagate(); cerr << "rootprop " << ok << "\n";
        auto has = [&](int x, int d) { char ch = sol[x / C][x % C]; string m = (d==0?"|LJ":d==1?"-LF":d==2?"|F7":"-J7"); return m.find(ch) != string::npos; };
        for (int x = 0; x < N && ok; x++) for (int d = 1; d <= 2; d++) if (CE[x][d] >= 0) {
            int e = CE[x][d]; int v = has(x, d) ? 1 : 0;
            if (!S.set(e, v)) { cerr << "set fail at cell " << x/C << "," << x%C << " d" << d << " v" << v << " st=" << (int)S.st[e] << "\n"; ok = false; break; }
            if (!S.propagate()) { cerr << "prop fail after cell " << x/C << "," << x%C << " d" << d << "\n"; ok = false; break; }
        }
        cerr << "force ok=" << ok << " solved=" << S.solved << "\n"; return {};
    }
    if (getenv("PROBETEST")) {
        auto cnt = [&]() { int u = 0; for (int e = 0; e < E; e++) if (S.st[e] == -1) u++; return u; };
        cerr << "E=" << E << " unknown after prop=" << cnt() << "\n";
        actCells.resize(N); iota(actCells.begin(), actCells.end(), 0); actEdges.resize(E); iota(actEdges.begin(), actEdges.end(), 0);
        bool ok = probeAll(20);
        cerr << "probe ok=" << ok << " unknown=" << cnt() << " t=" << elapsed() << "\n"; return {};
    }
    vector<signed char> base = S.st; // root-propagated state (forced edges)
    actCells.resize(N); iota(actCells.begin(), actCells.end(), 0);
    actEdges.resize(E); iota(actEdges.begin(), actEdges.end(), 0);
    bestLen = INT_MAX; nodes = 0; nodeLimit = LLONG_MAX; aborted = false;
    auto runDFS = [&](double until, bool head, bool probe) {
        useConn = true; stopFirst = true; headMode = head; tailCell = -1; useProbe = probe;
        long long lim = 2000; int restarts = 0;
        while (bestLen == INT_MAX && elapsed() < until) {
            S.undo(0); S.init(); for (int x = 0; x < N; x++) S.enq(x); S.propagate();
            aborted = false; nodes = 0; nodeLimit = lim; timeLimit = until; noise = restarts > 0 ? 40 : 0;
            dfs(); restarts++;
            if (!aborted && bestLen == INT_MAX) break;
            lim = lim * 3 / 2;
        }
        stopFirst = false; useConn = false; useProbe = false;
        if (getenv("MASYU_DEBUG")) cerr << "dfs-init restarts=" << restarts << " t=" << elapsed() << " len=" << bestLen << "\n";
    };
    // Phase A: quick DFS (good on small / easy grids, gives short loops)
    if (!getenv("NODFS")) runDFS(getenv("DFST") ? atof(getenv("DFST")) : 0.08, true, false);
    // Phase B: CDCL with lazy loop/connectivity clauses
    if (bestLen == INT_MAX && !getenv("NOSAT")) {
        vector<signed char> st0;
        const int thrs[5] = {500, 60, 150, 25, 2000};
        double sl = getenv("SLICE0") ? atof(getenv("SLICE0")) : 4.5;
        for (int k = 0; bestLen == INT_MAX && elapsed() < 8.6; k++) {
            double until = min(8.7, elapsed() + sl); sl *= 1.5;
            if (satLazy(st0, until, getenv("CONNTHR") ? atoi(getenv("CONNTHR")) : thrs[k % 5], k)) { int L; verify(st0, L); bestSt = st0; bestLen = L; }
        }
        if (getenv("MASYU_DEBUG")) cerr << "sat t=" << elapsed() << " len=" << bestLen << "\n";
    }
    // Phase C: fallback
    if (bestLen == INT_MAX) runDFS(9.2, false, true);
    if (bestLen == INT_MAX) { // should not happen; print empty grid
        return vector<string>(R, string(C, '.'));
    }
    if (getenv("MASYU_EXACT")) { // full branch & bound (testing only)
        timeLimit = atof(getenv("MASYU_EXACT")); aborted = false; nodes = 0; nodeLimit = LLONG_MAX;
        S.undo(0); S.init(); for (int x = 0; x < N; x++) S.enq(x); S.propagate();
        dfs(); cerr << (aborted ? "EXACT-ABORT " : "EXACT-OK ") << bestLen << "\n"; budget = 0;
    }
    vector<signed char> cur = bestSt; int curLen = bestLen;

    // ---- LNS improvement ----
    int maxW = min(R, 50), maxH = min(C, 50);
    vector<int> loopSeq, loopE; vector<char> freeE(E, 0);
    auto rebuildLoop = [&]() {
        loopSeq.clear(); loopE.clear();
        int start = -1; for (int e = 0; e < E; e++) if (cur[e] == 1) { start = EA[e]; break; }
        int prev = -1, x = start;
        do {
            int nx = -1, ne = -1;
            for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e >= 0 && cur[e] == 1 && CN[x][d] != prev) { nx = CN[x][d]; ne = e; break; } }
            if (nx < 0) for (int d = 0; d < 4; d++) { int e = CE[x][d]; if (e >= 0 && cur[e] == 1) { nx = CN[x][d]; ne = e; break; } }
            loopSeq.push_back(x); loopE.push_back(ne); prev = x; x = nx;
        } while (x != start);
    };
    rebuildLoop();
    S.undo(0); S.init();
    vector<int>& loopCells = loopSeq;
    long long iter = 0, statNodes = 0, statAb = 0, statCells = 0, statImp = 0;
    double slice = 0.25, thr = getenv("THR") ? atof(getenv("THR")) : 0.015, hardCap = 2.0;
    double sliceEnd = max(budget, elapsed() + 0.05); int markLen = curLen; bool marked = false;
    bool adaptive = getenv("NOADAPT") == nullptr && budget < 5;
    while (true) {
        double now = elapsed();
        if (!marked && now >= sliceEnd - slice) { marked = true; markLen = curLen; }
        if (now >= sliceEnd) {
            if (!adaptive) break;
            double rel = (markLen - curLen) / (double)curLen;
            if (rel < thr || now > hardCap) break;
            markLen = curLen; sliceEnd = now + slice;
        }
        iter++;
        int h = rndInt(3, min(R, 4 + (int)(iter % 9))), w = rndInt(3, min(C, 4 + (int)((iter / 3) % 9)));
        if (rnd() % 16 == 0) { h = min(R, rndInt(6, 16)); w = min(C, rndInt(6, 16)); }
        int center = loopCells[rnd() % loopCells.size()];
        int r0 = center / C - h / 2 + rndInt(-1, 1), c0 = center % C - w / 2 + rndInt(-1, 1);
        r0 = max(0, min(R - h, r0)); c0 = max(0, min(C - w, c0));
        int r1 = r0 + h - 1, c1 = c0 + w - 1;
        auto inW = [&](int x) { int r = x / C, c = x % C; return r >= r0 && r <= r1 && c >= c0 && c <= c1; };
        actCells.clear(); actEdges.clear();
        for (int r = r0; r <= r1; r++) for (int c = c0; c <= c1; c++) actCells.push_back(r * C + c);
        for (int x : actCells) for (int d = 1; d <= 2; d++) { int e = CE[x][d]; if (e >= 0 && inW(CN[x][d])) { actEdges.push_back(e); freeE[e] = 1; } }
        bool ok = S.loadWindow(cur, freeE, loopSeq, loopE);
        for (int e : actEdges) freeE[e] = 0;
        if (!ok) continue;
        for (int r = max(0, r0 - 2); r <= min(R - 1, r1 + 2); r++) for (int c = max(0, c0 - 2); c <= min(C - 1, c1 + 2); c++) S.enq(r * C + c);
        if (!S.propagate()) continue;
        bestLen = curLen; nodes = 0; nodeLimit = 4000 + (long long)actCells.size() * 60; aborted = false; timeLimit = sliceEnd;
        dfs();
        statNodes += nodes; statAb += aborted; statCells += actCells.size();
        if (bestLen < curLen) { cur = bestSt; curLen = bestLen; rebuildLoop(); statImp++; }
    }

    // output
    int L; if (!verify(cur, L)) { /* fallback shouldn't happen */ }
    auto on = [&](int x, int d) { int e = CE[x][d]; return e >= 0 && cur[e] == 1; };
    vector<string> out;
    for (int i = 0; i < R; i++) {
        string line;
        for (int j = 0; j < C; j++) {
            int x = i * C + j; bool n = on(x, 0), e = on(x, 1), s2 = on(x, 2), w = on(x, 3);
            char ch = '.';
            if (e && w) ch = '-'; else if (n && s2) ch = '|';
            else if (n && e) ch = 'L'; else if (n && w) ch = 'J';
            else if (s2 && e) ch = 'F'; else if (s2 && w) ch = '7';
            line += ch;
        }
        out.push_back(line);
    }
    if (getenv("MASYU_DEBUG")) cerr << "len=" << curLen << " nodes/it=" << statNodes / max(1LL, iter) << " aborted=" << statAb << " cells/it=" << statCells / max(1LL, iter) << " imp=" << statImp << " iters=" << iter << " time=" << elapsed() << "\n";
    return out;
}

vector<string> solve(vector<string> grid) {
    return solveImpl(grid);
}

int main()
{
    ofstream fout(getenv("OUTPUT_PATH"));

    string grid_count_temp;
    getline(cin, grid_count_temp);

    int grid_count = stoi(ltrim(rtrim(grid_count_temp)));

    vector<string> grid;
    string grid_item;
    while ((int)grid.size() < grid_count && getline(cin, grid_item)) {
        grid_item = rtrim(ltrim(grid_item));
        if (grid_item.empty()) continue;
        grid.push_back(grid_item);
    }

    vector<string> result = solve(grid);

    for (size_t i = 0; i < result.size(); i++) {
        fout << result[i];
        if (i != result.size() - 1) fout << "\n";
    }
    fout << "\n";
    fout.close();
    return 0;
}

string ltrim(const string &str) {
    string s(str);
    s.erase(s.begin(), find_if(s.begin(), s.end(), [](unsigned char c) { return !isspace(c); }));
    return s;
}

string rtrim(const string &str) {
    string s(str);
    s.erase(find_if(s.rbegin(), s.rend(), [](unsigned char c) { return !isspace(c); }).base(), s.end());
    return s;
}
