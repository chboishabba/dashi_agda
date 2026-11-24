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
#include <cstdlib>
#include <fstream>
#include <limits>
using namespace std;
using Z=mpz_class;
using Clock=chrono::steady_clock;
// Lazy GMP constants guarantee memory hooks are installed before GMP allocates.
// Call mp_set_memory_functions in main before any Z has been constructed.
static const Z& getC(){static const Z z=Z(640320)*640320*640320;return z;}
static const Z& getA(){static const Z z=13591409;return z;}
static const Z& getB(){static const Z z=545140134;return z;}
#define C getC()
#define A getA()
#define B getB()
struct GMPAllocation{
 size_t live=0,peak=0,allocCalls=0,reallocCalls=0,freeCalls=0;
 size_t requestedBytes=0,reallocatedOldBytes=0;
};
static GMPAllocation GA;
static void* allocHook(size_t n){
 void*p=std::malloc(n);if(!p)std::abort();
 GA.live+=n;GA.peak=max(GA.peak,GA.live);
 ++GA.allocCalls;GA.requestedBytes+=n;return p;
}
static void* reallocHook(void*p,size_t oldN,size_t n){
 void*q=std::realloc(p,n);if(!q&&n)std::abort();
 if(n>=oldN)GA.live+=n-oldN;else GA.live-=oldN-n;
 GA.peak=max(GA.peak,GA.live);++GA.reallocCalls;
 GA.requestedBytes+=n;GA.reallocatedOldBytes+=oldN;
 return q;
}
static void freeHook(void*p,size_t n){
 if(n>GA.live)std::abort();
 GA.live-=n;++GA.freeCalls;std::free(p);
}

struct Triple{Z p,q,t;};
// Explicit carrier-residency model, not measured GMP heap high-water.
// mpz allocated limb capacity is read as a count, not a promise of RSS parity.
static size_t wordBits(const Z& z){return z==0?0:mpz_sizeinbase(z.get_mpz_t(),2);}
static size_t capBytes(const Z& z){return size_t(z.get_mpz_t()->_mp_alloc)*sizeof(mp_limb_t);}
static size_t liveCarrier(const Triple& x){return capBytes(x.p)+capBytes(x.q)+capBytes(x.t);}
struct FibreCost{
 uint64_t leaves=0, merges=0, orderedProducts=0, orderedAdds=0;
 long double schoolbookProductBitPairs=0;
 size_t maxOperandBits=0, maxResultBits=0, maxFrontierCapacityBytes=0;
 size_t maxSplitLeafDepth=0, terminalCarrierBytes=0, endpointCapacityBytes=0;
};
static FibreCost FC;
static void observeProduct(const Z& x,const Z& y){
 size_t a=wordBits(x),b=wordBits(y);
 FC.maxOperandBits=max(FC.maxOperandBits,max(a,b));
 FC.schoolbookProductBitPairs+=(long double)a*(long double)b;
 ++FC.orderedProducts;
}
static void observeTriple(const Triple& x,size_t resident,size_t depth){
 FC.maxFrontierCapacityBytes=max(FC.maxFrontierCapacityBytes,resident+liveCarrier(x));
 FC.maxResultBits=max(FC.maxResultBits,max({wordBits(x.p),wordBits(x.q),wordBits(x.t)}));
 FC.maxSplitLeafDepth=max(FC.maxSplitLeafDepth,depth);
}
Triple split(unsigned a,unsigned b,bool inplace,size_t resident=0,size_t depth=0){
 if(a==b){Triple x{1,1,0};observeTriple(x,resident,depth);return x;}
 if(b-a==1){Z p=a?Z(-24)*(2*a-1)*(6*a-5)*(6*a-1):Z(1);Z q=a?C*Z(a)*a*a:Z(1);Triple x{p,q,(A+B*a)*p};++FC.leaves;observeTriple(x,resident,depth);return x;}
 unsigned m=(a+b)/2;
 auto l=split(a,m,inplace,resident,depth+1);
 auto r=split(m,b,inplace,resident+liveCarrier(l),depth+1);
 ++FC.merges;
 FC.maxFrontierCapacityBytes=max(FC.maxFrontierCapacityBytes,resident+liveCarrier(l)+liveCarrier(r));
 observeProduct(l.t,r.q);observeProduct(l.p,r.t);
 observeProduct(l.p,r.p);observeProduct(l.q,r.q);
 ++FC.orderedAdds;
 if(inplace){
   // Do T before modifying P or Q. mpz_addmul is alias-safe here.
   mpz_mul(l.t.get_mpz_t(),l.t.get_mpz_t(),r.q.get_mpz_t());
   mpz_addmul(l.t.get_mpz_t(),l.p.get_mpz_t(),r.t.get_mpz_t());
   mpz_mul(l.p.get_mpz_t(),l.p.get_mpz_t(),r.p.get_mpz_t());
   mpz_mul(l.q.get_mpz_t(),l.q.get_mpz_t(),r.q.get_mpz_t());
   observeTriple(l,resident,depth);return l;
 }
 Triple out{l.p*r.p,l.q*r.q,l.t*r.q+l.p*r.t};
 FC.maxFrontierCapacityBytes=max(FC.maxFrontierCapacityBytes,resident+liveCarrier(l)+liveCarrier(r)+liveCarrier(out));
 observeTriple(out,resident,depth);return out;
}
Z floor_div(const Z&n,const Z&d){if(d<=0)throw runtime_error("bad denominator");Z q;mpz_fdiv_q(q.get_mpz_t(),n.get_mpz_t(),d.get_mpz_t());return q;}
string sha(const string&s){unsigned char hash[32];SHA256((const unsigned char*)s.data(),s.size(),hash);ostringstream o;o<<hex<<setfill('0');for(unsigned char x:hash)o<<setw(2)<<unsigned(x);return o.str();}
struct Receipt{string hash;double ms;unsigned n;size_t bits;};
Receipt compute(unsigned digits,bool inplace){
 FC=FibreCost{};
 auto start=Clock::now();unsigned n=digits/14+2,bits=unsigned(ceil(digits*log2(10.0)))+64;
 // Source sign cone: even n guarantees positive exact next-term delta.
 // We require n>=2; rounding up n is a stronger alternating tail truncation.
 if(n&1u)++n;
 // 10^digits = 2^digits * 5^digits exactly.
 // Cancel the 2^digits factor from both dyadic denominators before
 // constructing either terminal numerator. The working shift remains positive.
 if(bits<digits)throw runtime_error("invalid precision shift");
 Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),5,digits);
 for(;;){
  Triple s=split(0,n,inplace);
  FC.terminalCarrierBytes=liveCarrier(s);
  const size_t originalTerminalTripleBits=wordBits(s.p)+wordBits(s.q)+wordBits(s.t);
  Z pn=Z(-24)*(2*n-1)*(6*n-5)*(6*n-1),qn=C*Z(n)*n*n;
  // Source-typed signed residual geometry. Even n, P(0,n)<0, pn<0.
  // The signed next-term residual is positive without cross multiplication.
  const bool originalPIsNegative=(s.p<0);
  if((n&1u)!=0 || n<2 || !originalPIsNegative || pn>=0 || qn<=0)
    throw runtime_error("original signed Chudnovsky cone not certified");

  Z tailResidual=s.p*pn*(A+B*n);
  Z Tqn=s.t*qn;
  Z upperSeriesNumerator=Tqn+tailResidual;
  Z upperSeriesDenominator=s.q*qn;
  if(tailResidual<=0 || Tqn<=0 || upperSeriesNumerator<=0 ||
     upperSeriesDenominator<=0)
    throw runtime_error("invalid original positive-series endpoint");
  // The source P/Q/T carrier is now dead: these four exact integers
  // are its consumer-sufficient adjacent-interval observations.
  {Z dead;s.p.swap(dead);}
  {Z dead;s.t.swap(dead);}
  {Z dead;s.q.swap(dead);}

  Z root;
  {Z rad=Z(10005)<<(2*bits);
   mpz_sqrt(root.get_mpz_t(),rad.get_mpz_t());}
  const unsigned k=bits-digits; // 10^d=2^d 5^d, source guard above.

  // Let F=426880*5^d, A=F*root*(Q*q), B=T*q+delta.
  // Write A=2^k*a+ell, a=x*B+r, with 0<=ell<2^k and 0<=r<B.
  // This is the exact SAME lower floor as COMP5j, now retaining the
  // two remainder fibres needed to certify the upper endpoint.
  Z floor,lowerRemainder,lowShiftRemainder;
  {
    Z packed=Z(426880)*root*decimal*upperSeriesDenominator;
    Z shifted;
    mpz_fdiv_qr_2exp(shifted.get_mpz_t(),
                     lowShiftRemainder.get_mpz_t(),
                     packed.get_mpz_t(),k);
    mpz_fdiv_qr(floor.get_mpz_t(),lowerRemainder.get_mpz_t(),
                shifted.get_mpz_t(),upperSeriesNumerator.get_mpz_t());
  }
  {Z dead;upperSeriesNumerator.swap(dead);}

  // Original upper-side certificate, multiplied by q>0:
  // F*(root+1)*Q*q < (x+1)*2^k*T*q.
  // Substitute A=x*2^k*(T*q+delta)+2^k*r+ell.
  // The exact equivalent becomes
  //   x*delta + r + floor((ell+F*Q*q)/2^k) < T*q.
  // The upper witness no longer multiplies the huge root.
  Z upperCorrection;
  {
    Z increment=Z(426880)*decimal*upperSeriesDenominator;
    mpz_add(increment.get_mpz_t(),increment.get_mpz_t(),
            lowShiftRemainder.get_mpz_t());
    mpz_fdiv_q_2exp(upperCorrection.get_mpz_t(),
                    increment.get_mpz_t(),k);
  }
  {Z dead;upperSeriesDenominator.swap(dead);}
  {Z dead;lowShiftRemainder.swap(dead);}
  FC.endpointCapacityBytes=capBytes(Tqn)+capBytes(tailResidual)
    +capBytes(lowerRemainder)+capBytes(upperCorrection)
    +capBytes(root)+capBytes(decimal)+capBytes(floor);
  Z upperWitness=floor*tailResidual+lowerRemainder+upperCorrection;
  if(upperWitness<Tqn){
    string output=floor.get_str();
    return {sha(output),chrono::duration<double,milli>(Clock::now()-start).count(),
            n,originalTerminalTripleBits};
  }
  n+=max(1u,n/16);if(n&1u)++n;bits+=max(32u,bits/16);
 }
}
int main(int argc,char**argv){
 mp_set_memory_functions(allocHook,reallocHook,freeHook);
 if(argc<3){cerr<<"usage: pi_codec_memory decimal_digits baseline|inplace [repetitions]\n";return 2;}
 unsigned digits=stoul(argv[1]);string mode=argv[2];bool inplace=mode=="inplace";if(!inplace&&mode!="baseline")return 2;
 unsigned reps=argc>3?stoul(argv[3]):3;vector<double> runs;string expected;
 for(unsigned i=0;i<reps;i++){auto result=compute(digits,inplace);if(expected.empty())expected=result.hash;else if(expected!=result.hash)throw runtime_error("nonrepeatable output");runs.push_back(result.ms);
 cout<<"FIBRE schema=pi-p0-ordered-pqt-model-v1"<<" mode="<<mode<<" digits="<<digits
   <<" leaf_count="<<FC.leaves<<" merge_count="<<FC.merges
   <<" ordered_products="<<FC.orderedProducts<<" ordered_adds="<<FC.orderedAdds
   <<" schoolbook_bitpair_proxy="<<setprecision(0)<<fixed<<FC.schoolbookProductBitPairs
   <<" max_operand_bits="<<FC.maxOperandBits<<" max_result_bits="<<FC.maxResultBits
   <<" max_depth="<<FC.maxSplitLeafDepth<<" peak_explicit_carrier_capacity_bytes="<<FC.maxFrontierCapacityBytes
   <<" final_carrier_capacity_bytes="<<FC.terminalCarrierBytes
   <<" endpoint_explicit_capacity_bytes="<<FC.endpointCapacityBytes
   <<" gmp_peak_live_bytes="<<GA.peak<<" gmp_live_bytes_after_compute="<<GA.live
   <<" gmp_alloc_calls="<<GA.allocCalls<<" gmp_realloc_calls="<<GA.reallocCalls
   <<" gmp_free_calls="<<GA.freeCalls<<" gmp_total_requested_bytes="<<GA.requestedBytes
   <<" gmp_reallocated_old_bytes="<<GA.reallocatedOldBytes
   <<" output_hash="<<result.hash
   <<" measured_GMP_total_live_heap=true model_is_upper_bound=false"<<"\n";
 cout<<"RUN "<<mode<<" "<<digits<<" "<<i<<" "<<fixed<<setprecision(4)<<result.ms<<" bits="<<result.bits<<" hash="<<result.hash<<"\n";}
 sort(runs.begin(),runs.end());struct rusage usage{};getrusage(RUSAGE_SELF,&usage);
 // ru_maxrss may inherit a Python parent's historical high-water mark on
 // fork/exec. Linux /proc/self/status VmHWM measures THIS process image.
 size_t procHwmKiB=0;std::ifstream status("/proc/self/status");string statusLine;
 while(getline(status,statusLine))if(statusLine.rfind("VmHWM:",0)==0){
   istringstream stream(statusLine.substr(6));stream>>procHwmKiB;break;
 }
 cout<<"SUMMARY mode="<<mode<<" digits="<<digits<<" median_ms="<<runs[runs.size()/2]<<" peak_rss_kib="<<usage.ru_maxrss<<" proc_vmhwm_kib="<<procHwmKiB<<" hash="<<expected<<"\n";
}
