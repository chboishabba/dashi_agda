// Predictive prime valuation port of PR1529 check_pi_prime_valuation.py.
// Exact witness divisibility is checked before each reduced join.
// Optional postorder trace records the existing Paper9GmpTraceChecker fields.
#define main original_quotient_main
#include "check_pi_gmp_quotient_residual.cpp"
#undef main
#include <map>
#include <fstream>
#include <cstdint>
using Ledger=map<unsigned,unsigned long>;
struct Node {Triple v;Ledger p,q;};
static vector<unsigned> spf;
static ofstream trace;
static void factor(Ledger& x,unsigned n,unsigned mult=1){
 while(n>1){unsigned p=spf.at(n);x[p]+=mult;n/=p;}
}
static void add(Ledger& x,const Ledger& y){for(auto [p,e]:y)x[p]+=e;}
static void sub(Ledger& x,unsigned p,unsigned long e){
 auto it=x.find(p);if(it==x.end()||it->second<e)throw runtime_error("ledger underflow");
 it->second-=e;if(!it->second)x.erase(it);
}
static Node predicted(unsigned a,unsigned b){
 if(a==b){if(trace.is_open())trace<<"empty\n";return {{1,1,0},{},{}};}
 if(b-a==1){
  Node z{split(a,b,1000000000),{},{}};
  if(a){factor(z.p,24);factor(z.p,2*a-1);factor(z.p,6*a-5);factor(z.p,6*a-1);
    factor(z.q,640320,3);factor(z.q,a,3);}
  if(trace.is_open())trace<<"leaf "<<a<<"\n";
  return z;
 }
 unsigned m=a+(b-a)/2;auto l=predicted(a,m),r=predicted(m,b);
 Z g=1;
 for(auto it=l.p.begin();it!=l.p.end();){
  unsigned p=it->first;auto e=it->second;++it;
  auto j=r.q.find(p);if(j==r.q.end())continue;
  e=min(e,j->second);Z power;mpz_ui_pow_ui(power.get_mpz_t(),p,e);g*=power;
  sub(l.p,p,e);sub(r.q,p,e);
 }
 if(!mpz_divisible_p(l.v.p.get_mpz_t(),g.get_mpz_t()) ||
    !mpz_divisible_p(r.v.q.get_mpz_t(),g.get_mpz_t()))throw runtime_error("invalid cancellation witness");
 mpz_divexact(l.v.p.get_mpz_t(),l.v.p.get_mpz_t(),g.get_mpz_t());
 mpz_divexact(r.v.q.get_mpz_t(),r.v.q.get_mpz_t(),g.get_mpz_t());
 if(trace.is_open())trace<<"merge "<<g<<" "<<r.v.q<<" "<<l.v.p<<"\n";
 mpz_mul(l.v.t.get_mpz_t(),l.v.t.get_mpz_t(),r.v.q.get_mpz_t());
 mpz_addmul(l.v.t.get_mpz_t(),l.v.p.get_mpz_t(),r.v.t.get_mpz_t());
 mpz_mul(l.v.p.get_mpz_t(),l.v.p.get_mpz_t(),r.v.p.get_mpz_t());
 mpz_mul(l.v.q.get_mpz_t(),l.v.q.get_mpz_t(),r.v.q.get_mpz_t());
 add(l.p,r.p);add(l.q,r.q);return l;
}
static Z read(const Ledger& a){Z x=1;for(auto [p,e]:a){Z z;mpz_ui_pow_ui(z.get_mpz_t(),p,e);x*=z;}return x;}
int main(int argc,char**argv){
 if(argc<2||argc>3)return 2;
 unsigned d=stoul(argv[1]);if(!d||d>10000000)return 2;
 unsigned n=d/14+2,bits=unsigned(ceil(d*log2(10.0)))+64;
 Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),10,d);
 auto start=Clock::now();
 for(unsigned attempt=1;attempt<=12;++attempt){
  unsigned limit=max(640320u,6*n);
  spf.resize(limit+1);for(unsigned i=0;i<=limit;++i)spf[i]=i;
  for(unsigned i=2;i<=limit/i;++i)if(spf[i]==i)
    for(unsigned j=i*i;j<=limit;j+=i)if(spf[j]==j)spf[j]=i;
  if(argc==3){trace.open(argv[2],ios::trunc);if(!trace)throw runtime_error("trace open failed");}
  auto node=predicted(0,n);auto& s=node.v;
  if(trace.is_open()&&(read(node.p)!=abs(s.p)||read(node.q)!=s.q))throw runtime_error("ledger readback");
  Z pn=Z(-24)*(2*n-1)*(6*n-5)*(6*n-1),qn=C*Z(n)*n*n;
  Z lo=s.t,loD=s.q,hi=s.t*qn+s.p*pn*(A+B*n),hiD=s.q*qn;
  if(lo<=0||hi<=0)throw runtime_error("series sign");
  if(hi*loD<lo*hiD){swap(lo,hi);swap(loD,hiD);}
  Z scale=Z(1)<<bits,rad=10005*scale*scale,r;
  mpz_sqrt(r.get_mpz_t(),rad.get_mpz_t());
  if(!(r*r<=rad&&rad<(r+1)*(r+1)))throw runtime_error("root witness");
  Z L=426880*r*decimal*hiD,LD=scale*hi,U=426880*(r+1)*decimal*loD,UD=scale*lo;
  Z x=floor_div(L,LD);
  if(x*LD<=L&&U<(x+1)*UD){
   if(trace.is_open()){trace<<"receipt "<<d<<" "<<n<<" "<<r<<" "<<scale<<" "<<x<<"\n";trace.close();}
   cout<<"PASS digits="<<d<<" attempts="<<attempt<<" ms="<<elapsed(start)
    <<" bits="<<mpz_sizeinbase(s.p.get_mpz_t(),2)+mpz_sizeinbase(s.q.get_mpz_t(),2)+mpz_sizeinbase(s.t.get_mpz_t(),2)
    <<" sha="<<sha(x.get_str())<<"\n";return 0;
  }
  if(trace.is_open())trace.close();n+=max(1u,n/16);bits+=max(32u,bits/16);
 }
 return 1;
}
