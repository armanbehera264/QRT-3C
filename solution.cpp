#include <bits/stdc++.h>

using namespace std;

string ltrim(const string &);
string rtrim(const string &);

// ---------------------------------------------------------------------------
// Square packing into a minimum-area bounding rectangle.
//  1. best-fit skyline greedy over all strip widths (always-valid baseline)
//  2. small inputs: branch & bound over candidate rectangles (often proves optimum)
//  3. randomized beam search over candidate rectangles, growing beam width
// ---------------------------------------------------------------------------
static double TIME_LIMIT = 1.6;      // seconds of search per test case
static double BEAM_K = 8.0;
static int BEAM_B0 = 8;

typedef long long ll;
typedef chrono::steady_clock Clock;
static Clock::time_point T0;
static inline double elapsed() { return chrono::duration<double>(Clock::now() - T0).count(); }

struct Seg { int x, w, h; };
typedef vector<Seg> Sky;
struct Placed { int s, r, c; };

static mt19937_64 RNG(12345);
static inline double rnd() { return (RNG() >> 11) * (1.0 / 9007199254740992.0); }

static inline int lowest(const Sky& s) {
    int bi = 0;
    for (int i = 1; i < (int)s.size(); i++) if (s[i].h < s[bi].h) bi = i;
    return bi;
}
static void placeSq(const Sky& sky, int bi, int s, Sky& out) {
    out.clear();
    int x = sky[bi].x, w = sky[bi].w, h = sky[bi].h, nh = h + s;
    for (int i = 0; i < bi; i++) out.push_back(sky[i]);
    Seg seg{x, s < w ? s : w, nh};
    if (!out.empty() && out.back().h == nh) { seg.x = out.back().x; seg.w += out.back().w; out.pop_back(); }
    size_t start = bi + 1;
    if (s == w && start < sky.size() && sky[start].h == nh) { seg.w += sky[start].w; start++; }
    out.push_back(seg);
    if (s < w) out.push_back(Seg{x + s, w - s, h});
    for (size_t i = start; i < sky.size(); i++) out.push_back(sky[i]);
}
static void raiseSeg(const Sky& sky, int bi, int target, Sky& out) {
    out.clear();
    for (int i = 0; i < (int)sky.size(); i++) {
        Seg g = sky[i];
        if (i == bi) g.h = target;
        if (!out.empty() && out.back().h == g.h) out.back().w += g.w;
        else out.push_back(g);
    }
}

struct Solver {
    vector<int> sizes, distinct, cnt0;   // distinct sorted descending
    int n, D, M;
    ll S;

    void init(const vector<int>& sz) {
        sizes = sz; n = sz.size(); S = 0;
        map<int, int, greater<int>> c;
        for (int s : sz) { c[s]++; S += (ll)s * s; }
        for (auto& p : c) { distinct.push_back(p.first); cnt0.push_back(p.second); }
        D = distinct.size(); M = distinct[0];
    }

    // ---------------- greedy: strip of width W, returns height
    ll greedy(int W, bool randomize, double noise, vector<Placed>& placed) {
        vector<int> cnt = cnt0;
        Sky sky{Seg{0, W, 0}}, tmp;
        placed.clear();
        int left = n; ll height = 0;
        while (left) {
            int bi = lowest(sky);
            int x = sky[bi].x, w = sky[bi].w, h = sky[bi].h;
            int lh = bi > 0 ? sky[bi - 1].h : -1;
            int rh = bi + 1 < (int)sky.size() ? sky[bi + 1].h : -1;
            int best = -1; double bs = -1e18;
            for (int i = 0; i < D; i++) {
                int s = distinct[i];
                if (!cnt[i] || s > w) continue;
                double sc = s;
                if (s == w) sc += 0.25 * M;
                if (h + s == lh || h + s == rh) sc += 0.1 * M;
                if (randomize) sc += rnd() * M * noise;
                if (sc > bs) { bs = sc; best = i; }
            }
            if (best < 0) {
                int t = INT_MAX;
                if (lh >= 0) t = min(t, lh);
                if (rh >= 0) t = min(t, rh);
                raiseSeg(sky, bi, t, tmp); sky.swap(tmp);
                continue;
            }
            int s = distinct[best];
            cnt[best]--; placed.push_back(Placed{s, h, x});
            height = max(height, (ll)h + s);
            placeSq(sky, bi, s, tmp); sky.swap(tmp);
            left--;
        }
        return height;
    }

    // ---------------- branch & bound
    int W_, H_; ll nodes, nodeCap; double bbDeadline; vector<int> cnt; vector<Placed> stk;
    int smallestExcept(int skip) {
        for (int i = D - 1; i >= 0; i--) { int c = cnt[i] - (i == skip ? 1 : 0); if (c > 0) return distinct[i]; }
        return INT_MAX;
    }
    // returns 1 solved, 0 exhausted, throws -1 on budget
    bool bb(const Sky& sky, ll waste, int remaining) {
        nodes++;
        if (nodes > nodeCap) throw 1;
        if ((nodes & 2047) == 0 && elapsed() > bbDeadline) throw 1;
        if (remaining == 0) return true;
        int bi = lowest(sky);
        int x = sky[bi].x, w = sky[bi].w, h = sky[bi].h, room = H_ - h;
        int lh = bi > 0 ? sky[bi - 1].h : -1;
        int rh = bi + 1 < (int)sky.size() ? sky[bi + 1].h : -1;
        vector<pair<double, int>> moves;
        for (int i = 0; i < D; i++) {
            int s = distinct[i];
            if (!cnt[i] || s > w || s > room) continue;
            if (s < w) {
                int rest = w - s;
                if (rest < smallestExcept(i)) {
                    int top = rh < 0 ? h + s : min(h + s, rh);
                    if ((ll)rest * (top - h) > waste) continue;
                }
            }
            double sc = s;
            if (s == w) sc += 0.25 * M;
            if (h + s == lh || h + s == rh) sc += 0.1 * M;
            if (s == room) sc += 0.1 * M;
            sc += rnd() * 3.0;
            moves.push_back({sc, i});
        }
        sort(moves.begin(), moves.end(), greater<pair<double, int>>());
        Sky nsky;
        for (auto& mv : moves) {
            int i = mv.second, s = distinct[i];
            cnt[i]--; stk.push_back(Placed{s, h, x});
            placeSq(sky, bi, s, nsky);
            if (bb(nsky, waste, remaining - 1)) return true;
            stk.pop_back(); cnt[i]++;
        }
        int target = H_;
        if (lh >= 0) target = min(target, lh);
        if (rh >= 0) target = min(target, rh);
        ll cost = (ll)(target - h) * w;
        if (cost <= 0 || cost > waste) return false;
        raiseSeg(sky, bi, target, nsky);
        return bb(nsky, waste - cost, remaining);
    }
    // 1 = found, 0 = proven impossible, -1 = budget exhausted
    int search(int W, int H, double deadline, ll cap, vector<Placed>& out) {
        ll slack = (ll)W * H - S;
        if (slack < 0) return 0;
        W_ = W; H_ = H; nodes = 0; nodeCap = cap; bbDeadline = deadline; cnt = cnt0; stk.clear();
        Sky sky{Seg{0, W, 0}};
        try {
            if (bb(sky, slack, n)) { out = stk; return 1; }
            return 0;
        } catch (int) { return -1; }
    }

    // ---------------- beam search
    struct State { double key; ll waste, area; Sky sky; vector<int> cnt; int trail; };
    struct Tr { int parent, s, r, c; };
    bool beam(int W, int H, int B, double deadline, double K, vector<Placed>& out) {
        ll slack = (ll)W * H - S;
        if (slack < 0) return false;
        vector<Tr> arena;
        vector<State> states(1), next;
        states[0] = State{0, 0, 0, Sky{Seg{0, W, 0}}, cnt0, -1};
        unordered_map<unsigned long long, int> seen;
        Sky sky, tmp, nsky; vector<int> fits;
        for (int depth = 0; depth < n; depth++) {
            if (elapsed() > deadline) return false;
            next.clear(); seen.clear();
            for (State& st : states) {
                sky = st.sky; ll waste = st.waste; bool ok = true; int bi, x, w, h;
                const vector<int>& c = st.cnt;
                while (true) {
                    bi = lowest(sky); x = sky[bi].x; w = sky[bi].w; h = sky[bi].h;
                    int room = H - h, lim = w < room ? w : room;
                    fits.clear();
                    for (int i = 0; i < D; i++) if (c[i] && distinct[i] <= lim) fits.push_back(i);
                    if (!fits.empty()) break;
                    int tgt = H;
                    if (bi > 0) tgt = min(tgt, sky[bi - 1].h);
                    if (bi + 1 < (int)sky.size()) tgt = min(tgt, sky[bi + 1].h);
                    ll cost = (ll)(tgt - h) * w;
                    if (cost <= 0 || waste + cost > slack) { ok = false; break; }
                    waste += cost;
                    raiseSeg(sky, bi, tgt, tmp); sky.swap(tmp);
                }
                if (!ok) continue;
                int sminIdx = -1;
                for (int i = D - 1; i >= 0; i--) if (c[i]) { sminIdx = i; break; }
                for (int i : fits) {
                    int s = distinct[i];
                    placeSq(sky, bi, s, nsky);
                    int sm = distinct[sminIdx];
                    if (c[i] == 1 && i == sminIdx) {
                        sm = 0;
                        for (int j = i - 1; j >= 0; j--) if (c[j]) { sm = distinct[j]; break; }
                    }
                    ll dead = 0; int k = nsky.size();
                    for (int j = 0; j < k; j++) {
                        int gh = nsky[j].h, gw = nsky[j].w;
                        if (H - gh < sm) dead += (ll)gw * (H - gh);
                        else if (gw < sm) {
                            int a = j > 0 ? nsky[j - 1].h : H, b = j + 1 < k ? nsky[j + 1].h : H;
                            if (a > gh && b > gh) dead += (ll)gw * (min(a, b) - gh);
                        }
                    }
                    if (depth + 1 < n && waste + dead > slack) continue;
                    unsigned long long hsh = 1469598103934665603ULL;
                    for (int j = 0; j < k; j++) {
                        hsh = (hsh ^ (unsigned)nsky[j].h) * 1099511628211ULL;
                        hsh = (hsh ^ (unsigned)nsky[j].w) * 1099511628211ULL;
                    }
                    for (int j = 0; j < D; j++) hsh = (hsh ^ (unsigned)(c[j] - (j == i))) * 1099511628211ULL;
                    double key = (waste + dead) * K - (double)(st.area + (ll)s * s) + k * 0.5 * K + rnd() * K;
                    auto it = seen.find(hsh);
                    if (it != seen.end()) {
                        State& o = next[it->second];
                        if (key < o.key) {
                            o.key = key; o.waste = waste;
                            arena.push_back(Tr{st.trail, s, h, x}); o.trail = arena.size() - 1;
                        }
                        continue;
                    }
                    arena.push_back(Tr{st.trail, s, h, x});
                    seen[hsh] = next.size();
                    next.push_back(State{key, waste, st.area + (ll)s * s, nsky, c, (int)arena.size() - 1});
                    next.back().cnt[i]--;
                }
            }
            if (next.empty()) return false;
            if ((int)next.size() > B) {
                nth_element(next.begin(), next.begin() + B, next.end(), [](const State& a, const State& b) { return a.key < b.key; });
                next.resize(B);
            }
            states.swap(next);
        }
        int best = 0;
        for (int i = 1; i < (int)states.size(); i++) if (states[i].key < states[best].key) best = i;
        out.clear();
        for (int t = states[best].trail; t >= 0; t = arena[t].parent) out.push_back(Placed{arena[t].s, arena[t].r, arena[t].c});
        return true;
    }

    // ---------------- driver
    vector<pair<int, int>> candidates(ll limit) {
        vector<array<ll, 4>> v;
        for (ll W = M; W * W < limit; W++) {
            ll H = max(W, (S + W - 1) / W);
            for (; W * H < limit; H++) v.push_back({W * H, H - W, W, H});
        }
        sort(v.begin(), v.end());
        vector<pair<int, int>> r;
        for (auto& a : v) r.push_back({(int)a[2], (int)a[3]});
        return r;
    }

    vector<pair<int, int>> solve() {
        T0 = Clock::now();
        double deadline = TIME_LIMIT;
        ll bestArea = LLONG_MAX; vector<Placed> best, cur;
        ll root = (ll)sqrtl((long double)S);
        for (ll W = M; W <= max((ll)M, 2 * root); W++) {
            ll H = greedy((int)W, false, 0, cur);
            if (W * H < bestArea) { bestArea = W * H; best = cur; }
            if (elapsed() > 0.15 * TIME_LIMIT) break;
        }
        ll LB = LLONG_MAX;
        for (ll W = M; W <= S / M + M; W++) LB = min(LB, W * max((ll)M, (S + W - 1) / W));

        bool proven = false;
        if (n <= 22) {
            double bbd = (n > 12 ? 0.5 : 0.9) * TIME_LIMIT;
            ll budget = 300 + 20 * n;
            set<pair<int, int>> deadSet;
            while (elapsed() < bbd && bestArea > LB) {
                auto cands = candidates(bestArea);
                bool any = false, progressed = false;
                for (auto& c : cands) {
                    if (deadSet.count(c)) continue;
                    any = true;
                    if (elapsed() > bbd) break;
                    int r = search(c.first, c.second, bbd, budget, cur);
                    if (r == 0) { deadSet.insert(c); continue; }
                    if (r == 1) { bestArea = (ll)c.first * c.second; best = cur; progressed = true; break; }
                }
                if (!any) { proven = true; break; }
                if (!progressed) budget = min((ll)(budget * 1.6), (ll)4e18 / 2);
            }
        }
        int B = BEAM_B0;
        while (!proven && elapsed() < deadline && bestArea > LB) {
            auto cands = candidates(bestArea);
            if (cands.empty()) break;
            bool progressed = false;
            for (auto& c : cands) {
                if (elapsed() > deadline) break;
                if (beam(c.first, c.second, B, deadline, BEAM_K, cur)) {
                    bestArea = (ll)c.first * c.second; best = cur; progressed = true; break;
                }
            }
            if (!progressed && B < (1 << 20)) B *= 2;
        }
        // back to input order
        map<int, vector<pair<int, int>>> pools;
        for (auto& p : best) pools[p.s].push_back({p.r, p.c});
        vector<pair<int, int>> res;
        for (int s : sizes) { res.push_back(pools[s].back()); pools[s].pop_back(); }
        return res;
    }
};


/*
 * Complete the 'pack_squares' function below.
 *
 * The function is expected to return a 2D_INTEGER_ARRAY.
 * The function accepts INTEGER_ARRAY squares as parameter.
 */

vector<vector<int>> pack_squares(vector<int> squares) {
    vector<vector<int>> result;
    if (squares.empty()) return result;
    Solver solver;
    solver.init(squares);
    for (auto &p : solver.solve()) result.push_back({p.first, p.second});
    return result;
}

int main()
{
    const char *out_path = getenv("OUTPUT_PATH");
    ofstream fout_file;
    if (out_path) fout_file.open(out_path);
    ostream &fout = out_path ? (ostream &)fout_file : (ostream &)cout;
    if (getenv("PACK_TL")) TIME_LIMIT = atof(getenv("PACK_TL"));
    if (getenv("PACK_K")) BEAM_K = atof(getenv("PACK_K"));
    if (getenv("PACK_B")) BEAM_B0 = atoi(getenv("PACK_B"));

    string squares_count_temp;
    getline(cin, squares_count_temp);

    int squares_count = stoi(ltrim(rtrim(squares_count_temp)));

    vector<int> squares(squares_count);

    for (int i = 0; i < squares_count; i++) {
        string squares_item_temp;
        getline(cin, squares_item_temp);

        int squares_item = stoi(ltrim(rtrim(squares_item_temp)));

        squares[i] = squares_item;
    }

    vector<vector<int>> result = pack_squares(squares);

    for (size_t i = 0; i < result.size(); i++) {
        for (size_t j = 0; j < result[i].size(); j++) {
            fout << result[i][j];

            if (j != result[i].size() - 1) {
                fout << " ";
            }
        }

        if (i != result.size() - 1) {
            fout << "\n";
        }
    }

    fout << "\n";

    if (out_path) fout_file.close();

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
