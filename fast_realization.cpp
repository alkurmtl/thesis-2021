#include <iostream>
#include <vector>
#include <queue>
#include <cassert>
#include <list>
#include <unordered_set>
#include <cstdlib>
#include <ctime>

using namespace std;

double gr_mult = 0.4;

class HeightsList {
public:
    explicit HeightsList(int n) {
        hs.resize(2 * n + 1);
        in.assign(n, -1);
    }

    void add(int v, int h) {
        hs[h].push_back(v);
        in[v] = hs[h].size() - 1;
    }

    void erase(int v, int h) {
        swap(hs[h][in[v]], hs[h].back());
        in[hs[h][in[v]]] = in[v];
        hs[h].pop_back();
        in[v] = -1;
    }

    void move(int v, int from, int to) {
        erase(v, from);
        add(v, to);
    }

    void clear() {
        hs.assign(hs.size(), {});
        in.assign(in.size(), -1);
    }

    vector<int>& operator[](int h) {
        return hs[h];
    }

    vector<vector<int>> hs;
    vector<int> in;
};

int n, c;
int s = 0;
int t = 1;
vector<vector<int>> f;
vector<int> c_s;
vector<int> c_t;

vector<int> h;
HeightsList hs(1);
vector<long long> excess;
vector<int> p;
queue<int> q;
vector<char> active;
unordered_set<int> alive;

int gap_relabels = 0;
int global_relabels = 0;
int discharges = 0;
int pushes = 0;
int relabels = 0;
int scans = 0;
int activating_pushes = 0;
int total_scans = 0;

inline int get_f(int u, int v) { // relies on s = 0, t = 1
    ++scans;
    ++total_scans;
    if (v == t) {
        return f[u][t];
    } else if (u < v) {
        return f[u][!(u == s) + v - u];
    } else if (v == s) {
        return -f[s][u] + c_s[u];
    } else if (u > v) {
        return -f[v][1 + u - v] + c;
    }
    assert(false);
}

inline void add_f(int u, int v, int df) {
    if (v == t) {
        f[u][t] -= df;
    } else if (u < v) {
        f[u][!(u == s) + v - u] -= df;
    } else if (v == s) {
        f[s][u] += df;
    } else if (u > v) {
        f[v][1 + u - v] += df;
    }
    assert(u != v);
}

void push(int u, int v) {
    ++pushes;
    int kek_f = get_f(u, v);
    int df = min(excess[u], (long long) kek_f);
    excess[u] -= df;
    add_f(u, v, df);
    if (v != t && v != s) {
        excess[v] += df;
        if (!active[v]) {
            ++activating_pushes;
            active[v] = true;
            q.push(v);
        }
    }
}

void gap_relabeling(int k);

void relabel(int u) {
    ++relabels;
    int to_h = n + 2 + 1;
    for (int k = h[u]; k < n + 2 + 1; ++k) {
        bool found = false;
        for (int v : hs[k]) {
            if (u == v) continue;
            if (get_f(u, v) > 0) {
                found = true;
                to_h = k;
                break;
            }
        }
        if (found) break;
    }
    int old_h = h[u];
    h[u] = to_h + 1;
    if (h[u] == n + 2 + 1) {
        alive.erase(u);
    }
    hs.move(u, old_h, h[u]);
    if (hs[old_h].empty() && !hs[old_h - 1].empty() && !hs[old_h + 1].empty()) {
        ++gap_relabels;
        gap_relabeling(old_h);
        h[u] = n + 2 + 1;
        return;
    }
}

void discharge(int u) {
    ++discharges;
    while (true) {
        for (int v : hs[h[u] - 1]) {
            assert(h[u] == h[v] + 1);
            if (get_f(u, v) > 0) {
                push(u, v);
                --scans;
                --total_scans;
                if (excess[u] == 0) return;
            }
        }
        relabel(u);
        if (h[u] >= n + 2) break;
    }
}

void gap_relabeling(int k) {
    for (int i = k + 1; i < n + 2; ++i) {
        if (hs[i].empty()) break;
        vector<int> vs(hs[i].begin(), hs[i].end());
        for (int v : vs) {
            h[v] = n + 2 + 1;
            hs.move(v, i, h[v]);
            alive.erase(v);
        }
    }
}

void global_relabeling() {
    ++global_relabels;
    unordered_set<int> alive_bfs(alive.begin(), alive.end());
    hs.clear();
    h.assign(n + 2, n + 2 + 1);
    vector<int> q_bfs;
    q_bfs.reserve(n);
    h[t] = 0;
    q_bfs.push_back(t);
    alive_bfs.erase(t);
    for (int i = 0; i < q_bfs.size(); ++i) {
        int u = q_bfs[i];
        vector<int> to_erase;
        for (int v : alive_bfs) {
            if (h[v] > h[u] + 1 && get_f(v, u) > 0) {
                h[v] = h[u] + 1;
                q_bfs.push_back(v);
                to_erase.push_back(v);
            }
        }
        for (int v : to_erase) {
            alive_bfs.erase(v);
        }
    }
    h[s] = n + 2;
    for (int v = 0; v < n + 2; ++v) {
        if (h[v] == n + 2 + 1) {
            alive.erase(v);
        }
        hs.add(v, h[v]);
    }
}

int main(int argc, char** argv) {
#ifdef LOCAL
    cerr << "LOCAL" << endl;
    if (argc > 1) {
        gr_mult = strtod(argv[1], nullptr);
    }
#endif
    ios_base::sync_with_stdio(false);
    cin.tie(0);
    cin >> n >> c;
    f.assign(n + 2, vector<int>());
    for (int i = 2; i < n + 2; ++i) {
        f[i].assign(2 + n - (i - 2) - 1, c);
    }
    f[s].assign(n + 2, 0);
    c_s.assign(n + 2, 0);
    for (int i = 2; i < n + 2; ++i) {
        cin >> c_s[i];
        f[s][i] = c_s[i];
    }
    f[t].assign(n + 2, 0);
    c_t.assign(n + 2, 0);
    for (int i = 2; i < n + 2; ++i) {
        cin >> c_t[i];
        f[i][t] = c_t[i];
    }

    hs = HeightsList(n + 2);
    h.assign(n + 2, 1);
    h[s] = n + 2;
    h[t] = 0;
    for (int i = 0; i < n + 2; ++i) {
        hs.add(i, h[i]);
        alive.insert(i);
    }
    excess.assign(n + 2, 0);
    p.assign(n + 2, 0);
    active.assign(n + 2, false);
    for (int i = 2; i < n + 2; ++i) {
        if (c_s[i] == 0) continue;
        excess[s] += c_s[i];
        push(s, i);
    }

    while (!q.empty()) {
        if (scans >= alive.size() * alive.size() * gr_mult) {
            global_relabeling();
            scans = 0;
        }
        int u = q.front();
        q.pop();
        active[u] = false;
        if (h[u] >= n + 2) continue;
        discharge(u);
    }

    long long ans = 0;
    for (int v = 2; v < n + 2; ++v) {
        ans += c_t[v] - get_f(v, t);
    }
    cout << ans << endl;
    cerr << "Gap relabeling has occured " << gap_relabels << " times" << endl;
    cerr << "Global relabeling has occured " << global_relabels << " times" << endl;
    cerr << "Done " << discharges << " discharges" << endl;
    cerr << "Done " << pushes << " pushes" << endl;
    cerr << "Done " << activating_pushes << " activating pushes" << endl;
    cerr << "Done " << relabels << " relabels" << endl;
    cerr << "Done " << total_scans << " scans" << endl;
    cerr << "Time: " << clock() * 1.0 / CLOCKS_PER_SEC << endl;
}

