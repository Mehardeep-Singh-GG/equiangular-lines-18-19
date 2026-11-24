
#include <iostream>
#include <vector>
using namespace std;
int main() {
    int nf = 9;
    int npiv = 5;
    int max_fsum = 43;
    int lo[9] = {0,0,0,0,0,0,0,0,0};
    int hi[9] = {2,3,3,4,7,9,11,12,14};
    long long den[5] = {1,1,1,1,1};
    long long num0[5] = {19,38,-27,1,28};
    long long lop[5] = {1,0,0,15,0};
    long long hip[5] = {25,24,18,29,14};
    long long cf[5][9] = {{5,5,5,4,2,1,-1,0,1},{10,7,7,6,3,1,1,3,1},{-15,-12,-11,-9,-5,-1,0,-2,-2},{-9,-7,-8,-6,-3,-2,0,-1,-1},{10,8,8,6,4,2,1,1,2}};

    // Suffix sum of min/max for each pivot equation? Even simpler: 9 nested loops with max_fsum pruning!
    int x[9];
    long long cnt = 0;
    auto dfs = [&](auto& self, int i, int csum) -> void {
        if (i == nf) {
            long long pv[5];
            for (int r = 0; r < npiv; ++r) {
                long long num = num0[r];
                for (int k = 0; k < nf; ++k) num -= cf[r][k] * x[k];
                if (num < lop[r] * den[r] || num > hip[r] * den[r] || (num % den[r]) != 0) return;
                pv[r] = num / den[r];
            }
            for (int k = 0; k < nf; ++k) cout << x[k] << " ";
            for (int r = 0; r < npiv; ++r) cout << pv[r] << (r+1==npiv ? "\n" : " ");
            cnt++;
            return;
        }
        int u = min(hi[i], max_fsum - csum);
        for (int v = lo[i]; v <= u; ++v) {
            x[i] = v;
            self(self, i + 1, csum + v);
        }
    };
    dfs(dfs, 0, 0);
    cerr << "Total exact sols: " << cnt << "\n";
    return 0;
}
