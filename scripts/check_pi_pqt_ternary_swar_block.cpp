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
#include <cstdint>
using namespace std;
using Z=mpz_class;
using Clock=chrono::steady_clock;
const Z C=Z(640320)*640320*640320,A=13591409,B=545140134;
struct Triple{Z p,q,t;};
// Bounded P/Q/T leaf codec. Signed trit per 8-bit SWAR lane:
// 00=zero, 01=positive, 10=negative, 11=invalid (fail closed).
// Upper 6 bits/lane stay zero; the original integer index is the residual.
static unsigned BLOCK=1;
static uint64_t pack_trit_lanes(unsigned a,unsigned b){
 uint64_t word=0;
 for(unsigned i=0;i<8 && a+i<b;++i)
   word|=uint64_t(a+i==0?0:2)<<(8*i);
 return word;
}
static int trit_at(uint64_t word,unsigned lane){
 unsigned code=unsigned((word>>(8*lane))&3ULL);
 if(code==3)throw runtime_error("invalid ternary-in-binary lane");
 return code==2?-1:int(code);
}
static void codec_exhaustive(){
 for(unsigned code=0;code<6561;++code){
   unsigned x=code;uint64_t w=0;
   for(unsigned i=0;i<8;++i){unsigned digit=x%3;x/=3;w|=uint64_t(digit)<<(8*i);}
   x=code;
   for(unsigned i=0;i<8;++i){unsigned digit=x%3;x/=3;
     if(trit_at(w,i)!=(digit==2?-1:int(digit)))throw runtime_error("trit round-trip");
   }
 }
 // A missing sign or illicit state 3 must never be treated as a valid trit.
 try{(void)trit_at(3,0);throw runtime_error("bad lane accepted");}
 catch(const runtime_error&err){if(string(err.what())!="invalid ternary-in-binary lane")throw;}
}
Triple split(unsigned a,unsigned b,bool inplace){
 if(a==b)return {1,1,0};
 if(b-a<=BLOCK){
   uint64_t lanes[4]={0,0,0,0};
   for(unsigned j=a;j<b;j+=8)lanes[(j-a)/8]=pack_trit_lanes(j,min(j+8,b));
   Triple l{1,1,0};
   for(unsigned k=a;k<b;++k){
     unsigned delta=k-a;
     int sign=trit_at(lanes[delta/8],delta%8);
     if(sign!=(k==0?0:-1))throw runtime_error("lost original leaf sign");
     Z p=sign==0?Z(1):Z(sign)*24*(2*k-1)*(6*k-5)*(6*k-1);
     Z q=sign==0?Z(1):C*Z(k)*k*k;
     Z t=(A+B*k)*p;
     mpz_mul(l.t.get_mpz_t(),l.t.get_mpz_t(),q.get_mpz_t());
     mpz_addmul(l.t.get_mpz_t(),l.p.get_mpz_t(),t.get_mpz_t());
     mpz_mul(l.p.get_mpz_t(),l.p.get_mpz_t(),p.get_mpz_t());
     mpz_mul(l.q.get_mpz_t(),l.q.get_mpz_t(),q.get_mpz_t());
   }
   return l;
 }
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
 if(argc<3){cerr<<"usage: pi_pqt_ternary_swar decimal_digits block_size [repetitions]\n";return 2;}
 codec_exhaustive();
 unsigned digits=stoul(argv[1]);BLOCK=stoul(argv[2]);
 if(BLOCK<1||BLOCK>32)return 2;
 const bool inplace=true;string mode="block_"+to_string(BLOCK);
 // Contract: regrouping uses ordered contiguous leaves only.
 for(unsigned n=1;n<33;++n){
   BLOCK=1;Triple ref=split(0,n,true);
   for(unsigned b: {4u,8u,16u}){BLOCK=b;Triple candidate=split(0,n,true);
     if(ref.p!=candidate.p||ref.q!=candidate.q||ref.t!=candidate.t)
       throw runtime_error("PQT leaf block parity");}
 }
 BLOCK=stoul(argv[2]);
 unsigned reps=argc>3?stoul(argv[3]):3;vector<double> runs;string expected;
 for(unsigned i=0;i<reps;i++){auto result=compute(digits,inplace);if(expected.empty())expected=result.hash;else if(expected!=result.hash)throw runtime_error("nonrepeatable output");runs.push_back(result.ms);cout<<"RUN "<<mode<<" "<<digits<<" "<<i<<" "<<fixed<<setprecision(4)<<result.ms<<" bits="<<result.bits<<" hash="<<result.hash<<"\n";}
 sort(runs.begin(),runs.end());struct rusage usage{};getrusage(RUSAGE_SELF,&usage);
 cout<<"SUMMARY mode="<<mode<<" digits="<<digits<<" median_ms="<<runs[runs.size()/2]<<" peak_rss_kib="<<usage.ru_maxrss<<" hash="<<expected<<"\n";
}
