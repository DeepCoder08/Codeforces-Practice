/*DEEPANSHU_KHASA*/
/*JandeCoder_8*/
/*2023MT10689*/
#include <iostream>
#include <vector>
#include <algorithm>
#include <map>
#include <set>
#include <queue>
#include <stack>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <cmath>
#include <cstring>
#include <limits>
#include <numeric>
#include <functional>
#include <bitset>
#include <deque>
#include <list>
#include <iterator>
#include<chrono>
#include<random>
 
using namespace std;
 
#define ll long long
#define ull unsigned long long
typedef pair<int, int> pii;
#define pyes cout<<"YES"<<"\n";
#define pno cout<<"NO"<<"\n";
#define br cout<<"\n";
#define mod 998244353
#define MOD 1000000007
#define inf 9223372036854775807
 
 
#define          all(v)              v.begin(), v.end()
#define         rall(v)              v.rbegin(),v.rend()
 
#define            pb                push_back
#define          sz(a)               ((long long)a.size())
 
// GCD function
ll gcd(ll a, ll b) {
    return b == 0 ? a : gcd(b, a % b);
}
 
// LCM function
ll lcm(ll a, ll b) {
    return (a / gcd(a, b)) * b;
}
 
int msb(int n){
    for(int i=32; i>=0; i--){
        if(n & (1LL<<i)){
            
            return i;
        }
    }
 
    return 0;
}
 
int nCr(int n, int r)  {
        // Choose the smaller value for lesser iterations
        if(r > n-r) r = n-r;
        
        // base case
        if(r == 1) return n;
        
        int res = 1; // to store the result 
        
        // Calculate nCr using iterative method avoiding overflow 
        for (int i = 0; i < r; i++) {
            res = res * (n-i);
            res = res / (i+1);
        }
        
        return res; // return the result
         
}
 
//combinations: a_choose_b
ll choose(int a, int b, ll M, vector<ll>&fact, vector<ll>& inv_fact){
    ll x= (((fact[a]*(inv_fact[b]))%M)*(inv_fact[a-b]))%M;
    return x;
 
}
 
//binary exponentiation
ll bin_pow(ll a, ll b, ll M){
    ll res=1;
    while(b){
        if(b&1) res= (res*a)%M;
        a= (a*a)%M;
        b= b>>1;
    }
    return res%M;
}
 
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
//ALLINONE
//ll gcd(ll a, ll b) {if (b > a) {return gcd(b, a);} if (b == 0) {return a;} return gcd(b, a % b);}
ll expo(ll a, ll b, ll m ) {ll res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
void extendgcd(ll a, ll b, ll*v) {if (b == 0) {v[0] = 1; v[1] = 0; v[2] = a; return ;} extendgcd(b, a % b, v); ll x = v[1]; v[1] = v[0] - v[1] * (a / b); v[0] = x; return;} //pass an arry of size1 3
ll mminv(ll a, ll b) {ll arr[3]; extendgcd(a, b, arr); return arr[0];} //for non prime b
ll mminvprime(ll a, ll b) {return expo(a, b - 2, b);}
bool revsort(ll a, ll b) {return a > b;}
ll combination(ll n, ll r, ll m, ll *fact, ll *ifact) {ll val1 = fact[n]; ll val2 = ifact[n - r]; ll val3 = ifact[r]; return (((val1 * val2) % m) * val3) % m;}
void google(int t) {cout << "Case #" << t << ": ";}
vector<ll> sieve(int n) {int*arr = new int[n + 1](); vector<ll> vect; for (int i = 2; i <= n; i++)if (arr[i] == 0) {vect.push_back(i); for (int j = 2 * i; j <= n; j += i)arr[j] = 1;} return vect;}
ll mod_add(ll a, ll b, ll m) {a = a % m; b = b % m; return (((a + b) % m) + m) % m;}
ll mod_mul(ll a, ll b, ll m) {a = a % m; b = b % m; return (((a * b) % m) + m) % m;}
ll mod_sub(ll a, ll b, ll m) {a = a % m; b = b % m; return (((a - b) % m) + m) % m;}
ll mod_div(ll a, ll b, ll m) {a = a % m; b = b % m; return (mod_mul(a, mminvprime(b, m), m) + m) % m;}  //only for prime m
ll phin(ll n) {ll number = n; if (n % 2 == 0) {number /= 2; while (n % 2 == 0) n /= 2;} for (ll i = 3; i <= sqrt(n); i += 2) {if (n % i == 0) {while (n % i == 0)n /= i; number = (number / i * (i - 1));}} if (n > 1)number = (number / n * (n - 1)) ; return number;} //O(sqrt(N))
ll getRandomNumber(ll l, ll r) {return uniform_int_distribution<ll>(l, r)(rng);} 
 
/* ---------- pre-compute SPF up to MAXN ---------- */
const int MAXN = 300000;                   // raise if constraints allow
vector<int> spf(MAXN + 1);
 
void build_spf() {
    iota(spf.begin(), spf.end(), 0);      // spf[i] = i for all i
    spf[0] = 0;                           // 0 unused
    spf[1] = 1;                           // by convention
    for (int i = 2; i * 1LL * i <= MAXN; ++i) {
        if (spf[i] == i) {                // i is prime
            for (int j = i * i; j <= MAXN; j += i)
                if (spf[j] == j) spf[j] = i;
        }
    }
}
 
void DFS(int node, vector<vector<int>>&adj, vector<int>&vis, vector<pair<int, int>>&roads){
    vis[node]=1;
    //cout<<node<<" ";
    for(auto& neighbour: adj[node]){
        if(!vis[neighbour]){
            roads.push_back({node, neighbour});
            DFS(neighbour, adj, vis, roads);
        }
    }
}
 
void solve() {
    
    int n;
    cin>>n;
    vector<ll>A(n);
    for(auto&i: A)cin>>i;
 
    vector<int>bit(31, 0);
    for(int i=0; i<n; i++){
        for(int j=30; j>=0; j--){
            if(A[i]&(1<<j)){
                bit[j]++;
                break;
            }
        }
    }
    ll cnt=0;
    for(int i=0; i<31; i++){
        int x= bit[i];
        cnt+= (x*(1LL)*(x-1))/2;
 
    }
    cout<<cnt<<endl;
}
 
int32_t main() {
    ios_base::sync_with_stdio(0);cin.tie(0);cout.tie(0);
 
    int t;
    cin>>t;
    
    while(t--) {
        solve();
    }
}