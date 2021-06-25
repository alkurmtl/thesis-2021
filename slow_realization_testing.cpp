#include <iostream>
#include <vector>
#include <queue>
#include <cassert>
#include <list>
#include <unordered_set>
#include <cstdlib>
#include <ctime>
#include <random>

using namespace std;

int n, c;
int s = 0;
int t = 1;
vector<vector<int>> f;
vector<vector<int>> cap;
vector<int> c_s;
vector<int> c_t;

vector<int> h;
vector<int> cnt_h;
vector<long long> excess;
vector<int> p;
queue<int> q;
vector<char> active;

int gap_relabels = 0;
int global_relabels = 0;
int discharges = 0;
int pushes = 0;
int relabels = 0;
int scans = 0;
int total_scans = 0;

int get_f(int u, int v) { // relies on s = 0, t = 1
    ++scans;
    ++total_scans;
    if (v == t) {
        return f[u][t];
    } else if (u < v) {
        return f[u][!(u == s) + v - u];
    } else if (v == s) {
        return -f[s][u] + 2 * c_s[u];
    } else if (u > v) {
        return -f[v][1 + u - v] + 2 * cap[v][1 + u - v];
    }
    assert(false);
}

void add_f(int u, int v, int df) {
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
    if (v == 4) {
        int kek = 9;
    }
    int kek_f = get_f(u, v);
    int df = min(excess[u], (long long) kek_f);
    excess[u] -= df;
    add_f(u, v, df);
    if (v != t && v != s) {
        excess[v] += df;
        if (!active[v]) {
            active[v] = true;
            q.push(v);
        }
    }
}

void gap_relabeling(int k) {
    for (int i = 0; i < n + 2; ++i) {
        if (h[i] > k) {
            h[i] = n + 2 + 1;
        }
    }
}

void global_relabeling() {
    ++global_relabels;
    h.assign(n + 2, n + 2 + 1);
    queue<int> q_bfs;
    h[t] = 0;
    q_bfs.push(t);
    while (!q_bfs.empty()) {
        int u = q_bfs.front();
        q_bfs.pop();
        for (int v = 0; v < n + 2; ++v) {
            if (u == v) continue;
            if (get_f(v, u) > 0 && h[v] > h[u] + 1) {
                h[v] = h[u] + 1;
                q_bfs.push(v);
            }
        }
    }
    h[s] = n + 2;
    cnt_h.assign(n + 2, 0);
    for (int i = 0; i < n + 2; ++i) {
        ++cnt_h[h[i]];
    }
}

void relabel(int u) {
    ++relabels;
    int min_h = 1e9;
    for (int v = 0; v < n + 2; ++v) {
        if (u == v) continue;
        if (get_f(u, v) > 0) {
            min_h = min(min_h, h[v]);
            if (min_h == h[u]) break;
        }
    }
    --cnt_h[h[u]];
    if (cnt_h[h[u]] == 0 && cnt_h[h[u] - 1] > 0 && cnt_h[h[u] + 1] > 0) {
        ++gap_relabels;
        gap_relabeling(h[u]);
        h[u] = n + 2 + 1;
    }
    h[u] = min_h + 1;
    ++cnt_h[h[u]];
}

void discharge(int u) {
    ++discharges;
    while (excess[u] > 0) {
        if (p[u] == n + 2) {
            relabel(u);
            p[u] = 0;
            if (h[u] >= n + 2) break;
        }
        int v = p[u];
        if (u == v) {
            ++p[u];
            continue;
        }
        if (get_f(u, v) > 0 && h[u] == h[v] + 1) {
            push(u, v);
            --total_scans;
        } else {
            ++p[u];
        }
    }
}

double gr_mult = 0.7;
int main(int argc, char** argv) {
    ios_base::sync_with_stdio(false);
    cin.tie(0);
    int N = 9998;
    int MAX_C = 1e9;
    mt19937 rnd;
    vector<double> times_tests;
    vector<long long> scans_tests;
    for (int test_num = 0; test_num < 10; ++test_num) {
        gap_relabels = 0;
        global_relabels = 0;
        discharges = 0;
        pushes = 0;
        relabels = 0;
        scans = 0;
        total_scans = 0;
        n = N;
        f.assign(n + 2, vector<int>());
        cap.assign(n + 2, vector<int>());
        for (int i = 2; i < n + 2; ++i) {
            cap[i].assign(2 + n - (i - 2) - 1, 0);
            for (int& j : cap[i]) {
                j = rnd() % MAX_C;
            }
            f[i] = cap[i];
        }
        f[s].assign(n + 2, 0);
        c_s.assign(n + 2, 0);
        for (int i = 2; i < n + 2; ++i) {
            c_s[i] = rnd() % MAX_C;
            f[s][i] = c_s[i];
        }
        f[t].assign(n + 2, 0);
        c_t.assign(n + 2, 0);
        for (int i = 2; i < n + 2; ++i) {
            c_t[i] = rnd() % MAX_C;
            f[i][t] = c_t[i];
        }

        double start_time = clock() * 1.0 / CLOCKS_PER_SEC;
        h.assign(n + 2, 1);
        h[s] = n + 2;
        h[t] = 0;
        cnt_h.assign(2 * (n + 2), 0);
        cnt_h[1] = n;
        cnt_h[n + 2] = 1;
        cnt_h[0] = 1;
        excess.assign(n + 2, 0);
        p.assign(n + 2, 0);
        active.assign(n + 2, false);
        for (int i = 2; i < n + 2; ++i) {
            if (c_s[i] == 0) continue;
            excess[s] += c_s[i];
            push(s, i);
        }

        while (!q.empty()) {
            if (scans >= n * n * gr_mult) {
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
        double end_time = clock() * 1.0 / CLOCKS_PER_SEC;
        cout << ans << endl;
        cerr << "Gap relabeling has occured " << gap_relabels << " times" << endl;
        cerr << "Global relabeling has occured " << global_relabels << " times" << endl;
        cerr << "Done " << discharges << " discharges" << endl;
        cerr << "Done " << pushes << " pushes" << endl;
        cerr << "Done " << relabels << " relabels" << endl;
        cerr << "Done " << total_scans << " scans" << endl;
        cerr << "Time: " << end_time - start_time << endl;
        times_tests.push_back(end_time - start_time);
        scans_tests.push_back(total_scans);
    }

    double sum_times_tests = 0;
    for (double x : times_tests) {
        sum_times_tests += x;
    }
    cerr << "Average time is " << sum_times_tests / times_tests.size() << endl;

    long long sum_scans_tests = 0;
    for (long long x : scans_tests) {
        sum_scans_tests += x;
    }
    cerr << "Average scans is " << sum_scans_tests / scans_tests.size() << endl;
}

