// COMP5: exact GMP Chudnovsky, compare mpq enclosure against fused mpz floors.
// External mathematical premise: classical Chudnovsky identity and alternating tail.
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using Z=mpz_class; using Q=mpq_class;
static const Z C=Z(640320)*640320*640320;
static const Z A=13591409,B=545140134;
struct State {Z p,q,t;};
State split(unsigned a,unsigned b,bool cross){
 if(a==b)return {1,1,0};
 if(b-a==1){Z p=a?Z(-24)*(2*a-1)*(6*a-5)*(6*a-1):Z(1);Z q=a?C*Z(a)*a*a:Z(1);return {p,q,(A+B*a)*p};}
 unsigned m=(a+b)/2; auto l=split(a,m,cross),r=split(m,b,cross);
 if(cross){Z g;mpz_gcd(g.get_mpz_t(),l.p.get_mpz_t(),r.q.get_mpz_t());l.p/=g;r.q/=g;}
 return {l.p*r.p,l.q*r.q,l.t*r.q+l.p*r.t};
}
Z qfloor(const Z &a,const Z &b){if(b<=0)throw runtime_error("bad denominator");Z q;mpz_fdiv_q(q.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return q;}
Z qfloor(const Q &r){return qfloor(r.get_num(),r.get_den());}
string certify(unsigned d,bool cross,bool fused,State* result=nullptr){
 unsigned n=d/14+2,bits=4*d+32; Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),10,d);
 while(true){
  State s=split(0,n,cross); Z nextP=Z(-24)*(2*n-1)*(6*n-5)*(6*n-1),nextQ=C*Z(n)*n*n;
  Z scale=Z(1)<<bits,z,radicand=10005*scale*scale;mpz_sqrt(z.get_mpz_t(),radicand.get_mpz_t());
  Z x,y;
  if(fused){
   // Series endpoints: T/Q and (T*nextQ + P*nextP*(A+B*n))/(Q*nextQ).
   Z num1=s.t,den1=s.q;
   Z num2=s.t*nextQ+s.p*nextP*(A+B*n),den2=s.q*nextQ;
   if(num1<=0 || num2<=0)throw runtime_error("series endpoint nonpositive");
   // next term is negative for n>=1 with this Chudnovsky convention.
   if(num2*den1>num1*den2){swap(num1,num2);swap(den1,den2);}
   x=qfloor(Z(426880)*z*decimal*den2,scale*num2);
   y=qfloor(Z(426880)*(z+1)*decimal*den1,scale*num1);
  }else{
   Q v(s.t,s.q), nxt=Q(s.p,s.q)*Q(nextP,nextQ)*Q(A+B*n);
   Q lo=v,hi=v+nxt;if(lo>hi)swap(lo,hi);if(lo<=0)throw runtime_error("series interval nonpositive");
   Q L=Q(426880*z,scale)/hi,U=Q(426880*(z+1),scale)/lo;
   x=qfloor(L*decimal);y=qfloor(U*decimal);
  }
  if(x==y){if(result)*result=std::move(s);return x.get_str();}
  n+=max(1u,n/16);bits+=max(32u,bits/16);
 }
}
int main(int argc,char**argv){
 if(argc<2){cerr<<"usage: binary decimal-digits [runs]"<<endl;return 2;}
 unsigned d=stoul(argv[1]),runs=argc>2?stoul(argv[2]):7;
 struct Mode{bool cross,fused;const char*name;};
 const vector<Mode> modes={{false,false,"plain_mpq"},{true,false,"cross_mpq"},{false,true,"plain_fused"},{true,true,"cross_fused"}};
 string ref;
 for(auto mode:modes){
  vector<double> timing;State s;string output;
  for(unsigned k=0;k<runs;k++){
   auto start=chrono::steady_clock::now();output=certify(d,mode.cross,mode.fused,&s);
   auto end=chrono::steady_clock::now();timing.push_back(chrono::duration<double,milli>(end-start).count());
   if(!ref.empty()&&ref!=output)throw runtime_error("certified decimal mismatch");
   if(ref.empty())ref=output;
  }
  sort(timing.begin(),timing.end());
  cout<<"BENCH "<<d<<" "<<mode.name<<" "<<timing[runs/2]<<" bits "<<(mpz_sizeinbase(s.p.get_mpz_t(),2)+mpz_sizeinbase(s.q.get_mpz_t(),2)+mpz_sizeinbase(s.t.get_mpz_t(),2))<<" len "<<output.size()<<"\n";
 }
 cout<<"DIGITS "<<ref<<"\n";
}
