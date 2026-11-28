// Exact Chudnovsky P/Q/T binary splitting, GMP reference and certified decimal floor.
// The classical Chudnovsky identity is an external premise.
// Compile: g++ -O3 -std=c++17 check_pi_native_gmp.cpp -lgmpxx -lgmp -o check_pi_native_gmp
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using I=mpz_class;
using R=mpq_class;
struct Triple {I p,q,t;};
static const I C=I(640320)*640320*640320;
static const I A=13591409, B=545140134;
Triple split(unsigned a,unsigned b,bool cross){
  if(a==b)return {1,1,0};
  if(b-a==1){
    I p= a==0 ? I(1):I(-24)*(2*a-1)*(6*a-5)*(6*a-1);
    I q= a==0 ? I(1): C*I(a)*a*a;
    I t=(A+B*a)*p;
    return {p,q,t};
  }
  unsigned m=(a+b)/2;
  auto left=split(a,m,cross),right=split(m,b,cross);
  if(cross){
    I g;
    mpz_gcd(g.get_mpz_t(),left.p.get_mpz_t(),right.q.get_mpz_t());
    left.p/=g;right.q/=g;
  }
  return {left.p*right.p,left.q*right.q,left.t*right.q+left.p*right.t};
}
I floor_q(const R &q){
  I result;
  mpz_fdiv_q(result.get_mpz_t(),q.get_num().get_mpz_t(),q.get_den().get_mpz_t());
  return result;
}
string certify(unsigned digits,bool cross,Triple* result=nullptr){
  unsigned n=digits/14+2;
  unsigned bits=4*digits+32;
  I decimal;
  mpz_ui_pow_ui(decimal.get_mpz_t(),10,digits);
  while(true){
    Triple z=split(0,n,cross);
    R v(z.t,z.q);
    I pnext=I(-24)*(2*n-1)*(6*n-5)*(6*n-1);
    I qnext=C*I(n)*n*n;
    R nxt=R(z.p,z.q)*R(pnext,qnext)*R(A+B*n);
    R lo=v,hi=v+nxt;
    if(lo>hi)std::swap(lo,hi);
    if(lo<=0)throw runtime_error("negative series lower endpoint");
    I scale=I(1)<<bits;
    I root;I val=10005*scale*scale;
    mpz_sqrt(root.get_mpz_t(),val.get_mpz_t());
    R lower=R(426880*root,scale)/hi;
    R upper=R(426880*(root+1),scale)/lo;
    I x=floor_q(lower*decimal),y=floor_q(upper*decimal);
    if(x==y){if(result)*result=std::move(z);return x.get_str();}
    n+=std::max(1u,n/16);bits+=std::max(32u,bits/16);
  }
}
int main(int argc,char**argv){
  if(argc<3){cerr<<"usage: check_pi_native_gmp digits plain|cross [reps]\n";return 2;}
  unsigned digits=stoul(argv[1]);bool cross=string(argv[2])=="cross";
  unsigned reps=argc>=4?stoul(argv[3]):3;
  vector<double> times;string first;
  for(unsigned j=0;j<reps;j++){
    auto start=chrono::steady_clock::now();
    Triple z;string result=certify(digits,cross,&z);
    auto stop=chrono::steady_clock::now();
    if(j && result!=first)throw runtime_error("inconsistent repetition");
    first=std::move(result);
    times.push_back(chrono::duration<double,milli>(stop-start).count());
    if(j==0)cout<<"BITS "<<mpz_sizeinbase(z.p.get_mpz_t(),2)+mpz_sizeinbase(z.q.get_mpz_t(),2)+mpz_sizeinbase(z.t.get_mpz_t(),2)<<"\n";
  }
  sort(times.begin(),times.end());
  cout<<"RESULT "<<digits<<" "<< (cross?"cross":"plain") <<" median_ms "<<times[reps/2]<<" digits_len "<<first.size()<<"\n";
  cout<<"DECIMAL "<<first<<"\n";
}
