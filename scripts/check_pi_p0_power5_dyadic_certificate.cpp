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
 // 10^digits = 2^digits * 5^digits exactly.
 // Cancel the 2^digits factor from both dyadic denominators before
 // constructing either terminal numerator. The working shift remains positive.
 if(bits<digits)throw runtime_error("invalid precision shift");
 Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),5,digits);
 for(;;){
  Triple s=split(0,n,inplace);
  FC.terminalCarrierBytes=liveCarrier(s);
  Z pn=Z(-24)*(2*n-1)*(6*n-5)*(6*n-1),qn=C*Z(n)*n*n;
  // Compute the next-term endpoint using the original ordered P/Q/T first.
  Z num2=s.t*qn+s.p*pn*(A+B*n),den2=s.q*qn;
  // Then transfer the old terminal P/Q/T payload into the consumer and
  // destroy the now-dead P carrier before large endpoint products allocate.
  Z num1=std::move(s.t),den1=std::move(s.q);
  {Z dead;s.p.swap(dead);}
  if(num1<=0||num2<=0)throw runtime_error("negative series endpoint");
  if(num2*den1<num1*den2){swap(num1,num2);swap(den1,den2);}
  // Exact dyadic sqrt enclosure: floor(sqrt(10005 * 2^(2*bits))).
  // The radicand is dead immediately after the square-root call.
  Z root;{Z rad=Z(10005)<<(2*bits);mpz_sqrt(root.get_mpz_t(),rad.get_mpz_t());}
  // Lower-side products are only needed to compute the exact quotient.
  // Release them before constructing the independent upper-side witness.
  Z floor;
  {
    Z numerator=Z(426880)*root*decimal*den2;
    // For N>=0, D>0, k=bits-digits:
    // floor(N / (D*2^k)) = floor((N >> k)/D).
    // This eliminates the oversized dyadic denominator without rounding loss.
    mpz_fdiv_q_2exp(numerator.get_mpz_t(),numerator.get_mpz_t(),bits-digits);
    floor=floor_div(numerator,num2);
  }
  // Lower series endpoint is dead once the quotient has been computed.
  // The upper certificate only uses num1, den1, scale and root.
  {Z dead;num2.swap(dead);}
  {Z dead;den2.swap(dead);}
  Z top=Z(426880)*(root+1)*decimal*den1;
  // Integer U>0, k=bits-digits: top < U*2^k iff (top >> k) < U.
  mpz_fdiv_q_2exp(top.get_mpz_t(),top.get_mpz_t(),bits-digits);
  FC.endpointCapacityBytes=capBytes(num1)+capBytes(den1)+capBytes(num2)+capBytes(den2)
    +capBytes(top)
    +capBytes(root)+capBytes(decimal);
  if(top<(floor+1)*num1){string output=floor.get_str();return {sha(output),chrono::duration<double,milli>(Clock::now()-start).count(),n,size_t(mpz_sizeinbase(s.p.get_mpz_t(),2))+mpz_sizeinbase(s.q.get_mpz_t(),2)+mpz_sizeinbase(s.t.get_mpz_t(),2)};}
  n+=max(1u,n/16);bits+=max(32u,bits/16);
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
