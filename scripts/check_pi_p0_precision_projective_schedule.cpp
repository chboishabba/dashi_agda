// COMP5s UNTESTED: output-precision-indexed projective prime-content schedule.
// Complete integer source retained: NO P/Q/T truncation or lossy precision lift.
// COMP5r UNTESTED: source-indexed exact local gcd via supported-prime valuations.
// COMP5p UNTESTED: normalize the original Chudnovsky nonzero leaves by 24.
// Preserve the projective scale exponent and original signed residual cone.
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
#include <memory>
#include "pi_p0_projective_precision_schedule.hpp"
using namespace std;
using Z=mpz_class;
using Clock=chrono::steady_clock;
// Native source-work count, distinct from floating cost estimates and
// from actual GMP allocator or elapsed-time measurements.
struct LeafCostCounters {
 uint64_t primeContentCalls=0,smallModChecks=0,smallDivSteps=0;
 uint64_t exactGmpLeafDivisions=0;
};
static LeafCostCounters LeafWork;
static unsigned valuation64(uint64_t x,unsigned prime){
 unsigned v=0;
 while(x!=0){
   ++LeafWork.smallModChecks;
   if(x%prime)break;
   x/=prime;++v;++LeafWork.smallDivSteps;
 }
 return v;
}
// 640320=2^6*3*5*23*29.
// After universal /24, q'_j=(640320^3/24)*j^3.
// For any prime outside {2,3,5,23,29}, it cannot divide both
// (2j-1)(6j-5)(6j-1) and j^3:
// gcd(j,2j-1)=gcd(j,6j-1)=1, gcd(j,6j-5)=gcd(j,5).
// Every further common prime is therefore among 3,5,23,29.
// This computes the exact h_j=gcd(p'_j,q'_j) without a GMP gcd.
static Z leafExtraContent(unsigned index){
 ++LeafWork.primeContentCalls;
 if(index==0)return Z(1);
 const uint64_t j=index;
 const uint64_t f1=2*j-1,f2=6*j-5,f3=6*j-1;
 Z h=1;
 for(unsigned prime:{3u,5u,23u,29u}){
   const unsigned vp=valuation64(f1,prime)+valuation64(f2,prime)
                    +valuation64(f3,prime);
   // C^3/24 has v_3=2, v_5=v_23=v_29=3.
   const unsigned vc=(prime==3u)?2u:3u;
   const unsigned vq=vc+3*valuation64(j,prime);
   const unsigned count=min(vp,vq);
   for(unsigned i=0;i<count;++i)mpz_mul_ui(h.get_mpz_t(),h.get_mpz_t(),prime);
 }
 return h;
}
// Lazy GMP constants guarantee memory hooks are installed before GMP allocates.
// Call mp_set_memory_functions in main before any Z has been constructed.
static const Z& getC(){static const Z z=Z(640320)*640320*640320;return z;}
static const Z& getA(){static const Z z=13591409;return z;}
static const Z& getB(){static const Z z=545140134;return z;}
#define C getC()
#define A getA()
#define B getB()
// 640320 = 24 * 26680, so 640320^3 / 24 is integral.
// Construct the per-leaf normalized q DIRECTLY, never the unneeded /24.
static const Z& getC24(){static const Z z=(Z(640320)/24)*640320*640320;return z;}
#define C24 getC24()
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
// Reversible original-source scale receipt. It is NOT proof that an arbitrary
// supplied normalized triple is authentic; verifying the original ordered
// leaf product is a separate producer/consumer obligation.
struct ProjectiveSourceReceipt {
 unsigned begin=0,end=0;
 // Full source gauge for this interval:
 // product_(j in [begin,end), j>=1)(24*leafExtraContent(j)).
};
[[maybe_unused]] static Z buildOriginalSourceScale(ProjectiveSourceReceipt receipt){
 if(receipt.end<receipt.begin) throw runtime_error("invalid source interval");
 Z scale=1;
 for(uint64_t j=max(uint64_t(1),uint64_t(receipt.begin));j<receipt.end;++j){
   Z factor=24*leafExtraContent(static_cast<unsigned>(j));
   mpz_mul(scale.get_mpz_t(),scale.get_mpz_t(),factor.get_mpz_t());
 }
 return scale;
}
[[maybe_unused]] static Triple reopenOriginalRawSource(
    const Triple& normalized,ProjectiveSourceReceipt receipt){
 const Z scale=buildOriginalSourceScale(receipt);
 return {normalized.p*scale,normalized.q*scale,normalized.t*scale};
}
// Source equivalence: for a genuine original P/Q/T split and its
// normalized version, reopenOriginalRawSource(normalized,{a,b})=(P,Q,T).
// Opening is O(number of included leaves) + big-integer multiplications;
// never charged as constant time and never called by the fast π consumer.
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
static paper9_projective_schedule::PlanningLedger currentPlanLedger;
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
Triple split(unsigned a,unsigned b,bool inplace,size_t resident=0,size_t depth=0,
             const paper9_projective_schedule::Plan* plan=nullptr){
 if(a==b){Triple x{1,1,0};observeTriple(x,resident,depth);return x;}
 if(b-a==1){
   // Original j=0 (identity prefix) is unscaled.
   // For every j>=1, original p_j, q_j and t_j share 24 exactly
   // as a guaranteed leaf factor: M'_j=M_j/24.
   // No gcd or leaf-wise division occurs in this execution path.
   const Z j(a); // GMP arithmetic prevents unsigned intermediate overflow.
   Z p=a?Z(-1)*(2*j-1)*(6*j-5)*(6*j-1):Z(1);
   Z q=a?C24*j*j*j:Z(1);
   if(a){
     // The normalized 24-leaf may have further exact common content.
     // Both exact divisions are backed by the index-specific valuations.
     const Z extra=leafExtraContent(a);
     mpz_divexact(p.get_mpz_t(),p.get_mpz_t(),extra.get_mpz_t());
     mpz_divexact(q.get_mpz_t(),q.get_mpz_t(),extra.get_mpz_t());
     LeafWork.exactGmpLeafDivisions+=2;
   }
   Triple x{p,q,(A+B*a)*p};
   ++FC.leaves;observeTriple(x,resident,depth);return x;
 }
 const unsigned m=a+(b-a)/2;
 // Plan chooses evaluation order only; left/right algebra remains unchanged.
 Triple l,r;
 if(plan && plan->left && plan->right && plan->rightFirst){
   r=split(m,b,inplace,resident,depth+1,plan->right.get());
   l=split(a,m,inplace,resident+liveCarrier(r),depth+1,plan->left.get());
 }else{
   const auto* leftPlan=plan && plan->left?plan->left.get():nullptr;
   const auto* rightPlan=plan && plan->right?plan->right.get():nullptr;
   l=split(a,m,inplace,resident,depth+1,leftPlan);
   r=split(m,b,inplace,resident+liveCarrier(l),depth+1,rightPlan);
 }
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
 LeafWork=LeafCostCounters{};
 auto start=Clock::now();
 unsigned n=digits/14+2;
 const long double wantedBits=std::ceil(static_cast<long double>(digits)
                                  *std::log2(10.0L))+64.0L;
 if(!std::isfinite(wantedBits) ||
    wantedBits>static_cast<long double>(std::numeric_limits<unsigned>::max()))
   throw overflow_error("requested output precision cannot fit unsigned root index");
 unsigned bits=static_cast<unsigned>(wantedBits);
 // Original signed tail determines the order for every n>=2:
 // sign(delta_n)=(-1)^n; do not spend an extra series term to fix parity.
 // 10^digits = 2^digits * 5^digits exactly.
 // Cancel the 2^digits factor from both dyadic denominators before
 // constructing either terminal numerator. The working shift remains positive.
 if(bits<digits)throw runtime_error("invalid precision shift");
 Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),5,digits);
 for(;;){
  Triple s;
  {
    // The planner lives only during P/Q/T construction; the terminal
    // certificate must not inherit its ordinary C++ heap allocation.
    auto plan=paper9_projective_schedule::makePlan(n,digits,bits,currentPlanLedger);
    s=split(0,n,inplace,0,0,plan.get());
  }
  FC.terminalCarrierBytes=liveCarrier(s);
  const size_t originalTerminalTripleBits=wordBits(s.p)+wordBits(s.q)+wordBits(s.t);
  const Z nextIndex(n);
  Z pn=Z(-24)*(2*nextIndex-1)*(6*nextIndex-5)*(6*nextIndex-1);
  Z qn=C*nextIndex*nextIndex*nextIndex;
  // Compute the next-term endpoint using the original ordered P/Q/T first.
  const bool originalPIsNegative=(s.p<0);
  Z num2=s.t*qn+s.p*pn*(A+B*n),den2=s.q*qn;
  // Then transfer the old terminal P/Q/T payload into the consumer and
  // destroy the now-dead P carrier before large endpoint products allocate.
  Z num1=std::move(s.t),den1=std::move(s.q);
  {Z dead;s.p.swap(dead);}
  if(num1<=0||num2<=0)throw runtime_error("negative series endpoint");
  // Original source: P(0,n)=product_{j=1}^{n-1} p_j has sign (-1)^(n-1).
  // Since p_n<0, q_n>0 and A+B*n>0, delta has sign (-1)^n.
  // For even n S_n<S_(n+1); for odd n S_(n+1)<S_n.
  // The ordered endpoints are selected by a GMP allocation-swap ONLY,
  // without either of the former full-width cross-products.
  if(n<2 || (originalPIsNegative!=((n&1u)==0)) || pn>=0 || qn<=0)
    throw runtime_error("source signed next-term orientation not certified");
  if(n&1u){swap(num1,num2);swap(den1,den2);}
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
  if(top<(floor+1)*num1){string output=floor.get_str();return {sha(output),chrono::duration<double,milli>(Clock::now()-start).count(),n,originalTerminalTripleBits};}
  const unsigned growN=max(1u,n/16),growBits=max(32u,bits/16);
  if(n>std::numeric_limits<unsigned>::max()-growN ||
     bits>std::numeric_limits<unsigned>::max()-growBits)
    throw overflow_error("retry precision/index exhausted");
  n+=growN;bits+=growBits;
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
   <<" source_gauge=indexed_prime_content"
   <<" source_scale_24_exponent="<<(result.n-1)
   <<" source_scale_recipe=product_local_extra_content_j_1_to_n_minus_1"
   <<" source_prime_support=2-3-5-23-29"
   <<" source_reopen_requires_scale=true"
   <<" source_zero_mode=empty_interval_P1_Q1_T0"
   <<" source_tail_sign="<<((result.n&1u)?"negative":"positive")
   <<" leaf_prime_content_calls="<<LeafWork.primeContentCalls
   <<" leaf_small_mod_checks="<<LeafWork.smallModChecks
   <<" leaf_small_div_steps="<<LeafWork.smallDivSteps
   <<" leaf_exact_gmp_division_calls="<<LeafWork.exactGmpLeafDivisions
   <<" source_reopening_executed_in_fast_path=false"
   <<" schedule_model=precision_indexed_projective_peak"
   <<" schedule_precision_bits="<<currentPlanLedger.precisionBits
   <<" schedule_digits="<<currentPlanLedger.digits
   <<" schedule_plan_nodes="<<currentPlanLedger.planNodes
   <<" schedule_merges="<<currentPlanLedger.scheduledMerges
   <<" schedule_right_first="<<currentPlanLedger.rightFirstMerges
   <<" schedule_predicted_peak_bytes="<<setprecision(1)<<currentPlanLedger.modelPeakBytes
   <<" schedule_cpp_plan_object_payload_bytes="<<currentPlanLedger.planningObjectPayloadBytes
   <<" schedule_cpp_allocator_overhead_measured=false"
   <<" schedule_model_is_measured_or_certified=false"
   <<" source_full_integer_exact=true"
   <<" source_truncation_performed=false"
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
