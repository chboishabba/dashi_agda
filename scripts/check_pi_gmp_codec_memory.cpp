// Codec-inspired exact ordered carrier: support, sign and residual must survive.
// Compare expression-temporary binary splitting versus GMP alias-safe in-place mul/addmul.
// Exact decimal-floor admission is conditional on the classical Chudnovsky identity/tail.
#include <gmpxx.h>
#include <openssl/sha.h>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <sys/resource.h>
#include <vector>
using namespace std;
using Z=mpz_class;
using Clock=chrono::steady_clock;
const Z C=Z(640320)*640320*640320,A=13591409,B=545140134;
struct Triple{Z p,q,t;};
Triple split(unsigned a,unsigned b,bool inplace){
 if(a==b)return {1,1,0};
 if(b-a==1){Z p=a?Z(-24)*(2*a-1)*(6*a-5)*(6*a-1):Z(1);Z q=a?C*Z(a)*a*a:Z(1);return {p,q,(A+B*a)*p};}
 unsigned m=(a+b)/2;auto l=split(a,m,inplace),r=split(m,b,inplace);
 if(inplace){
   // Do T before modifying P or Q. mpz_addmul is alias-safe here.
   mpz_mul(l.t.get_mpz_t(),l.t.get_mpz_t(),r.q.get_mpz_t());
   mpz_addmul(l.t.get_mpz_t(),l.p.get_mpz_t(),r.t.get_mpz_t());
   mpz_mul(l.p.get_mpz_t(),l.p.get_mpz_t(),r.p.get_mpz_t());
   mpz_mul(l.q.get_mpz_t(),l.q.get_mpz_t(),r.q.get_mpz_t());
   return l;
 }
 return {l.p*r.p,l.q*r.q,l.t*r.q+l.p*r.t};
}
Z floor_div(const Z&n,const Z&d){if(d<=0)throw runtime_error("bad denominator");Z q;mpz_fdiv_q(q.get_mpz_t(),n.get_mpz_t(),d.get_mpz_t());return q;}
string sha(const string&s){unsigned char hash[32];SHA256((const unsigned char*)s.data(),s.size(),hash);ostringstream o;o<<hex<<setfill('0');for(unsigned char x:hash)o<<setw(2)<<unsigned(x);return o.str();}
struct Receipt{string hash;double ms;unsigned n;size_t bits;};
Receipt compute(unsigned digits,bool inplace){
 auto start=Clock::now();unsigned n=digits/14+2,bits=unsigned(ceil(digits*log2(10.0)))+64;
 Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),10,digits);
 for(;;){
  Triple s=split(0,n,inplace);
  Z pn=Z(-24)*(2*n-1)*(6*n-5)*(6*n-1),qn=C*Z(n)*n*n;
  Z num1=s.t,den1=s.q,num2=s.t*qn+s.p*pn*(A+B*n),den2=s.q*qn;
  if(num1<=0||num2<=0)throw runtime_error("negative series endpoint");
  if(num2*den1<num1*den2){swap(num1,num2);swap(den1,den2);}
  Z scale=Z(1)<<bits,rad=10005*scale*scale,root;mpz_sqrt(root.get_mpz_t(),rad.get_mpz_t());
  Z numerator=Z(426880)*root*decimal*den2,denominator=scale*num2;
  Z floor=floor_div(numerator,denominator);
  Z top=Z(426880)*(root+1)*decimal*den1,topden=scale*num1;
  if(top<(floor+1)*topden){string output=floor.get_str();return {sha(output),chrono::duration<double,milli>(Clock::now()-start).count(),n,size_t(mpz_sizeinbase(s.p.get_mpz_t(),2))+mpz_sizeinbase(s.q.get_mpz_t(),2)+mpz_sizeinbase(s.t.get_mpz_t(),2)};}
  n+=max(1u,n/16);bits+=max(32u,bits/16);
 }
}
int main(int argc,char**argv){
 if(argc<3){cerr<<"usage: pi_codec_memory decimal_digits baseline|inplace [repetitions]\n";return 2;}
 unsigned digits=stoul(argv[1]);string mode=argv[2];bool inplace=mode=="inplace";if(!inplace&&mode!="baseline")return 2;
 unsigned reps=argc>3?stoul(argv[3]):3;vector<double> runs;string expected;
 for(unsigned i=0;i<reps;i++){auto result=compute(digits,inplace);if(expected.empty())expected=result.hash;else if(expected!=result.hash)throw runtime_error("nonrepeatable output");runs.push_back(result.ms);cout<<"RUN "<<mode<<" "<<digits<<" "<<i<<" "<<fixed<<setprecision(4)<<result.ms<<" bits="<<result.bits<<" hash="<<result.hash<<"\n";}
 sort(runs.begin(),runs.end());struct rusage usage{};getrusage(RUSAGE_SELF,&usage);
 cout<<"SUMMARY mode="<<mode<<" digits="<<digits<<" median_ms="<<runs[runs.size()/2]<<" peak_rss_kib="<<usage.ru_maxrss<<" hash="<<expected<<"\n";
}
