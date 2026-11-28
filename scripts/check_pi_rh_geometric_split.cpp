// COMP5d: RH-style weighted-coordinate dyadic split, retaining original order.
// Exact output certificate is conditional on classical Chudnovsky identity.
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
#include <openssl/sha.h>
using namespace std;using Z=mpz_class;using Clock=chrono::steady_clock;
const Z C=Z(640320)*640320*640320,A=13591409,B=545140134;
struct Trip{Z p,q,t;};
static vector<uint64_t> mass;
static uint64_t weight(unsigned k,int scheme){
  if(k==0)return 1;
  Z p=Z(24)*(2*k-1)*(6*k-5)*(6*k-1),q=C*Z(k)*k*k;
  unsigned pb=mpz_sizeinbase(p.get_mpz_t(),2),qb=mpz_sizeinbase(q.get_mpz_t(),2);
  if(scheme==1)return qb; // denominator load coordinate
  if(scheme==2)return qb+pb; // full leaf bit-density
  return 1;
}
static void init(unsigned n,int scheme){mass.assign(n+1,0);for(unsigned k=0;k<n;k++)mass[k+1]=mass[k]+weight(k,scheme);}
unsigned split_at(unsigned a,unsigned b,int scheme){
 if(scheme==0)return (a+b)/2;
 uint64_t target=mass[a]+(mass[b]-mass[a])/2;
 auto it=lower_bound(mass.begin()+a+1,mass.begin()+b,target);
 unsigned m=unsigned(it-mass.begin());return max(a+1,min(b-1,m));
}
Trip split(unsigned a,unsigned b,int scheme){
 if(a==b)return {1,1,0};
 if(b-a==1){Z p=a?Z(-24)*(2*a-1)*(6*a-5)*(6*a-1):Z(1);Z q=a?C*Z(a)*a*a:Z(1);return {p,q,(A+B*a)*p};}
 unsigned m=split_at(a,b,scheme);auto l=split(a,m,scheme),r=split(m,b,scheme);
 return {l.p*r.p,l.q*r.q,l.t*r.q+l.p*r.t};
}
Z divfloor(const Z& n,const Z& d){Z q;mpz_fdiv_q(q.get_mpz_t(),n.get_mpz_t(),d.get_mpz_t());return q;}
string digest(const string&s){unsigned char d[32];SHA256((const unsigned char*)s.data(),s.size(),d);ostringstream os;os<<hex<<setfill('0');for(int i=0;i<32;i++)os<<setw(2)<<int(d[i]);return os.str();}
struct Result{string hash;double msInit,msSplit,msEnd,msRoot,msFloor,msString,msTotal;unsigned n;size_t sizeBits;};
Result run(unsigned digits,int scheme){
 auto begin=Clock::now();auto last=begin;auto duration=[](Clock::time_point t){return chrono::duration<double,milli>(Clock::now()-t).count();};
 unsigned n=digits/14+2,bits=(unsigned)ceil(digits*log2(10.0))+64;
 Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),10,digits);
 if(scheme!=0)init(n,scheme);double tInit=duration(last);last=Clock::now();
 Trip s=split(0,n,scheme);double tSplit=duration(last);last=Clock::now();
 Z pn=Z(-24)*(2*n-1)*(6*n-5)*(6*n-1),qn=C*Z(n)*n*n;
 Z num1=s.t,den1=s.q,num2=s.t*qn+s.p*pn*(A+B*n),den2=s.q*qn;
 if(num1<=0||num2<=0)throw runtime_error("nonpositive series endpoints");
 if(num2*den1<num1*den2){swap(num1,num2);swap(den1,den2);}
 double tEnd=duration(last);last=Clock::now();
 Z sc=Z(1)<<bits,z,v=10005*sc*sc;mpz_sqrt(z.get_mpz_t(),v.get_mpz_t());double tRoot=duration(last);last=Clock::now();
 Z x=divfloor(Z(426880)*z*decimal*den2,sc*num2),y=divfloor(Z(426880)*(z+1)*decimal*den1,sc*num1);
 if(x!=y)throw runtime_error("certificate floor mismatch");
 double tFloor=duration(last);last=Clock::now();string d=x.get_str();string h=digest(d);double tString=duration(last);
 return {h,tInit,tSplit,tEnd,tRoot,tFloor,tString,duration(begin),n,
 (size_t)mpz_sizeinbase(s.p.get_mpz_t(),2)+mpz_sizeinbase(s.q.get_mpz_t(),2)+mpz_sizeinbase(s.t.get_mpz_t(),2)};
}
int main(int argc,char**argv){if(argc<2)return 2;unsigned digits=stoul(argv[1]),reps=argc>2?stoul(argv[2]):5;
 vector<vector<Result>> samples(3);string hash;
 for(unsigned i=0;i<reps;i++)for(unsigned j=0;j<3;j++){
  int mode=(j+i)%3;Result r=run(digits,mode);if(hash.empty())hash=r.hash;else if(hash!=r.hash)throw runtime_error("hash mismatch");samples[mode].push_back(r);
 }
 const char *names[]={"midpoint","rh_q_bits","rh_pq_bits"};
 for(int mode=0;mode<3;mode++){
  vector<double> tot,init,split,end,root,floor,serial;for(auto &r:samples[mode]){tot.push_back(r.msTotal);init.push_back(r.msInit);split.push_back(r.msSplit);end.push_back(r.msEnd);root.push_back(r.msRoot);floor.push_back(r.msFloor);serial.push_back(r.msString);}
  auto med=[](vector<double>&v){sort(v.begin(),v.end());return v[v.size()/2];};
  cout<<fixed<<setprecision(3)<<"BENCH "<<digits<<" "<<names[mode]<<" total="<<med(tot)<<" coordinate_init="<<med(init)<<" split="<<med(split)<<" endpoint="<<med(end)<<" sqrt="<<med(root)<<" floors="<<med(floor)<<" serialize_hash="<<med(serial)<<" bits="<<samples[mode][0].sizeBits<<" hash="<<hash<<"\n";
 }
}
