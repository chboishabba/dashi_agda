// Paper 9 COMP5c. Source arithmetic: classical Chudnovsky series (analytic identity external).
// The integer certificate is exact conditional on the classical identity and tail bound.
// Compile: g++ -O3 -std=c++17 scripts/check_pi_gmp_stage_profile.cpp -lgmpxx -lgmp -lcrypto -o /tmp/pi_stage
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
#include <vector>
using namespace std;
using Z=mpz_class;
using Clock=chrono::steady_clock;
static const Z C=Z(640320)*640320*640320;
static const Z A=13591409,B=545140134;
struct Triple {Z p,q,t;};
struct Profile {double split=0,decimal=0,sqrt=0,endpoints=0,divisions=0,serialize=0,total=0;unsigned tries=0;size_t bits=0;};
static double elapsed(Clock::time_point t){return chrono::duration<double,milli>(Clock::now()-t).count();}
Triple split(unsigned a,unsigned b,unsigned threshold){
 if(a==b)return {1,1,0};
 if(b-a==1){Z p=a?Z(-24)*(2*a-1)*(6*a-5)*(6*a-1):Z(1);Z q=a?C*Z(a)*a*a:Z(1);return {p,q,(A+B*a)*p};}
 unsigned m=(a+b)/2;auto l=split(a,m,threshold),r=split(m,b,threshold);
 if(b-a>=threshold){Z g;mpz_gcd(g.get_mpz_t(),l.p.get_mpz_t(),r.q.get_mpz_t());l.p/=g;r.q/=g;}
 return {l.p*r.p,l.q*r.q,l.t*r.q+l.p*r.t};
}
static Z floor_div(const Z&n,const Z&d){if(d<=0)throw runtime_error("denominator nonpositive");Z q;mpz_fdiv_q(q.get_mpz_t(),n.get_mpz_t(),d.get_mpz_t());return q;}
static string sha(const string&s){unsigned char hash[SHA256_DIGEST_LENGTH];SHA256((const unsigned char*)s.data(),s.size(),hash);ostringstream out;out<<hex<<setfill('0');for(unsigned char b:hash)out<<setw(2)<<(unsigned)b;return out.str();}
struct Receipt {string digest;Profile profile;size_t length=0;unsigned n=0;};
Receipt certify(unsigned digits,unsigned threshold,bool tight){
 auto start=Clock::now();Profile prof;unsigned n=digits/14+2;
 // Wide reproduces the prior 4*d+32 rule. Tight is a conservative near-minimum:
 // ceil(d*log2(10)) + 64 bits; if floors disagree increase n and bits.
 unsigned bits=tight?(unsigned)ceil(digits*log2(10.0))+64:4*digits+32;
 Z decimal;auto tm=Clock::now();mpz_ui_pow_ui(decimal.get_mpz_t(),10,digits);prof.decimal+=elapsed(tm);
 while(true){
   ++prof.tries;
   tm=Clock::now();Triple s=split(0,n,threshold);prof.split+=elapsed(tm);
   tm=Clock::now();Z scale=Z(1)<<bits,z,radicand=10005*scale*scale;
   mpz_sqrt(z.get_mpz_t(),radicand.get_mpz_t());prof.sqrt+=elapsed(tm);
   tm=Clock::now();Z pn=Z(-24)*(2*n-1)*(6*n-5)*(6*n-1),qn=C*Z(n)*n*n;
   Z lo=s.t,loD=s.q,hi=s.t*qn+s.p*pn*(A+B*n),hiD=s.q*qn;
   if(lo<=0||hi<=0)throw runtime_error("series lower endpoint nonpositive");
   if(hi*loD<lo*hiD){swap(lo,hi);swap(loD,hiD);} // lo <= hi
   Z numLow=Z(426880)*z*decimal*hiD,denLow=scale*hi;
   Z numHigh=Z(426880)*(z+1)*decimal*loD,denHigh=scale*lo;
   prof.endpoints+=elapsed(tm);
   tm=Clock::now();Z x=floor_div(numLow,denLow),y=floor_div(numHigh,denHigh);prof.divisions+=elapsed(tm);
   if(x==y){tm=Clock::now();string output=x.get_str();auto digest=sha(output);prof.serialize+=elapsed(tm);prof.total=elapsed(start);prof.bits=mpz_sizeinbase(s.q.get_mpz_t(),2)+mpz_sizeinbase(s.p.get_mpz_t(),2)+mpz_sizeinbase(s.t.get_mpz_t(),2);return {digest,prof,output.size(),n};}
   n+=max(1u,n/16);bits+=max(32u,bits/16);
 }
}
int main(int argc,char**argv){
 if(argc<2){cerr<<"usage: pi_stage decimal_digits [reps] (outputs 4 configurations)\n";return 2;}
 unsigned digits=stoul(argv[1]),reps=argc>2?stoul(argv[2]):5;
 if(reps<1||reps%2==0)throw runtime_error("reps must be odd positive");
 struct Mode {unsigned threshold;string name;};
 vector<Mode> modes={{1000000000,"plain"},{2,"full_cross"},{8,"threshold8"},{32,"threshold32"},{128,"threshold128"},{512,"threshold512"},{2048,"threshold2048"}};
 vector<vector<Profile>> recordings(modes.size());string expected;
 // Rotate order across passes, with a deterministic cyclic schedule.
 for(unsigned i=0;i<reps;i++)for(unsigned j=0;j<modes.size();j++){
   unsigned k=(j+i)%modes.size();auto r=certify(digits,modes[k].threshold,true);
   if(expected.empty())expected=r.digest;
   if(r.digest!=expected)throw runtime_error("digest mismatch across arithmetic/certification modes");
   recordings[k].push_back(r.profile);
 }
 auto med=[](vector<double>&v){sort(v.begin(),v.end());return v[v.size()/2];};
 for(unsigned k=0;k<modes.size();k++){
   auto extract=[&](double Profile::*field){vector<double> values;for(auto&r:recordings[k])values.push_back(r.*field);return med(values);};
   auto&mode=modes[k];auto p=recordings[k].back();
   cout<<fixed<<setprecision(3)<<"BENCH digits="<<digits<<" mode="<<mode.name
   <<" total="<<extract(&Profile::total)<<" split="<<extract(&Profile::split)
   <<" sqrt="<<extract(&Profile::sqrt)<<" power10="<<extract(&Profile::decimal)
   <<" endpoints="<<extract(&Profile::endpoints)<<" div="<<extract(&Profile::divisions)
   <<" serialize_and_hash="<<extract(&Profile::serialize)
   <<" attempts="<<p.tries<<" triple_bits="<<p.bits<<" sha="<<expected<<"\n";
 }
}
