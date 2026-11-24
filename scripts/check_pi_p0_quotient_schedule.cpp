// COMP6e UNTESTED: direct even common quotient, all signed correction sectors.
// COMP6d UNTESTED: producer-retained signed defect; COMP6c retained.
// COMP6c UNTESTED: exact local tail budgets, sufficient admission, exact fallback.
// COMP6b UNTESTED: both-parity shared quotient/slack fibre; COMP6a retained.
// COMP6a UNTESTED: bounded prefix observer with exact COMP5z fallback.
// COMP5z UNTESTED: fused affine parity comparison; preserves COMP5y.
// COMP5y UNTESTED: streamed parity product comparison; preserves COMP5x.
// COMP5x UNTESTED: four-corner virtual shifted comparisons; COMP5w preserved.
// COMP5w UNTESTED: quotient-only lower floor, no rho or ell; use the
// already computed upper W to recover opposite-endpoint upper-root
// decision with a source q_n multiplication or exact division on failure.
// COMP5v UNTESTED: share a single H*Q*R radical product across both
// source-adjacent endpoints, with lazy eta only on failed admission.
// COMP5u UNTESTED: small exact dyadic decision sectors over affine edge.
// No full 10005*(426880*10^d)^2 radical square on failed admission.
// COMP5t UNTESTED: affine endpoint edge + adaptive root/series retry.
// No prior prefix P/Q/T rebuild after a failed certificate; P is recovered
// from the signed next-term residual when a genuine suffix is needed.
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
#include "pi_p0_affine_edge_retry.hpp"
#include "pi_p0_dyadic_sector_contraction.hpp"
#include "pi_p0_quotient_sector.hpp"
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
// Native counters: arithmetic re-use and refinement paths are distinct.
// A modelled saved build is not actual saved time until native acceptance.
struct AffineRetryCounts {
 uint64_t initialTreeBuilds=0, suffixTreeBuilds=0;
 uint64_t signedPReopenDivisions=0;
 uint64_t rootBuilds=0, guardOnlyRefinements=0;
 uint64_t seriesOnlyRefinements=0, exactSquareClassifications=0;
 uint64_t squareSlackAdmissions=0, certificateAttempts=0;
 uint64_t scheduleNodesTotal=0, scheduleRightFirstTotal=0;
};
static AffineRetryCounts RetryWork;
static paper9_lazy_lower_sector::Counts LazyWork;
static paper9_quotient_sector::BoundaryCounts BoundaryWork;
static paper9_defect_source::SourceCounts SourceWork;
static Triple composeOrderedSource(Triple&& left,Triple&& right,
                                    bool inplace,size_t depth=0) {
 // This is the SAME noncommutative source merge used in split().
 // It is performed only when appending the newly computed suffix.
 ++FC.merges;
 FC.maxFrontierCapacityBytes=max(FC.maxFrontierCapacityBytes,
                                liveCarrier(left)+liveCarrier(right));
 observeProduct(left.t,right.q);observeProduct(left.p,right.t);
 observeProduct(left.p,right.p);observeProduct(left.q,right.q);
 ++FC.orderedAdds;
 if(inplace){
   mpz_mul(left.t.get_mpz_t(),left.t.get_mpz_t(),right.q.get_mpz_t());
   mpz_addmul(left.t.get_mpz_t(),left.p.get_mpz_t(),right.t.get_mpz_t());
   mpz_mul(left.p.get_mpz_t(),left.p.get_mpz_t(),right.p.get_mpz_t());
   mpz_mul(left.q.get_mpz_t(),left.q.get_mpz_t(),right.q.get_mpz_t());
   observeTriple(left,0,depth);return std::move(left);
 }
 Triple result{left.p*right.p,left.q*right.q,
               left.t*right.q+left.p*right.t};
 FC.maxFrontierCapacityBytes=max(FC.maxFrontierCapacityBytes,
   liveCarrier(left)+liveCarrier(right)+liveCarrier(result));
 observeTriple(result,0,depth);return result;
}

Receipt compute(unsigned digits,bool inplace){
 FC=FibreCost{};
 LeafWork=LeafCostCounters{};
 RetryWork=AffineRetryCounts{};
 LazyWork=paper9_lazy_lower_sector::Counts{};
 BoundaryWork=paper9_quotient_sector::BoundaryCounts{};
 SourceWork=paper9_defect_source::SourceCounts{};
 auto start=Clock::now();
 if(digits==0)throw runtime_error("positive decimal places required");
 unsigned n=digits/14+2;
 const long double requested=std::ceil(
   static_cast<long double>(digits)*std::log2(10.0L))+64.0L;
 if(!std::isfinite(requested) ||
    requested>static_cast<long double>(std::numeric_limits<unsigned>::max()/2))
   throw overflow_error("root precision cannot fit doubled shift");
 unsigned bits=static_cast<unsigned>(requested);
 if(bits<digits)throw runtime_error("bad dyadic precision index");
 Z decimal5;mpz_ui_pow_ui(decimal5.get_mpz_t(),5,digits);

 // The signed affine edge is the consumer-indexed representation.
 // It retains T,Q,delta=P*p_n*A_n; no stored V.
 auto planSource=[&](unsigned begin,unsigned finish,
                     size_t resident=0)->Triple{
   paper9_projective_schedule::PlanningLedger ledger;
   // Build a plan for the true interval, not a relabelled [0,length).
   // See makePlanInterval in the COMP5t planner extension.
   auto plan=paper9_projective_schedule::makePlanInterval(
       begin,finish,digits,bits,ledger);
   currentPlanLedger=ledger;
   RetryWork.scheduleNodesTotal+=ledger.planNodes;
   RetryWork.scheduleRightFirstTotal+=ledger.rightFirstMerges;
   return split(begin,finish,inplace,resident,0,plan.get());
 };
 Triple initial=planSource(0,n);
 ++RetryWork.initialTreeBuilds;
 FC.terminalCarrierBytes=liveCarrier(initial);
 size_t originalTerminalTripleBits=
    wordBits(initial.p)+wordBits(initial.q)+wordBits(initial.t);
 auto edge=paper9_defect_source::Edge::fromNormalizedTriple(
      n,std::move(initial.p),std::move(initial.q),std::move(initial.t),SourceWork);

 Z root;
 unsigned rootAtBits=0;
 auto refreshRoot=[&](){
   if(rootAtBits==bits)return;
   if(bits>std::numeric_limits<unsigned>::max()/2)
      throw overflow_error("root radicand shift exceeds unsigned");
   Z rad=Z(10005)<<(2*bits);
   mpz_sqrt(root.get_mpz_t(),rad.get_mpz_t());
   rootAtBits=bits;
   ++RetryWork.rootBuilds;
 };
 refreshRoot();
 for(;;){
   ++RetryWork.certificateAttempts;
   // Producer-retained signed defect: validate shape inside the classifier.
   auto decision=paper9_quotient_sector::classify(
       digits,bits,root,decimal5,edge,LazyWork,BoundaryWork,SourceWork);
   Z floor=std::move(decision.x);
   FC.endpointCapacityBytes=max(FC.endpointCapacityBytes,
     capBytes(root)+capBytes(decimal5)+
     capBytes(edge.t())+capBytes(edge.q())+capBytes(edge.delta()));
   if(decision.sector==paper9_dyadic_sector::Sector::AdmitFloor){
     string output=floor.get_str();
     return {sha(output),
        chrono::duration<double,milli>(Clock::now()-start).count(),
        n,originalTerminalTripleBits};
   }
   if(decision.sector==paper9_dyadic_sector::Sector::RefineRadical){
     const unsigned grow=max(32u,bits/16);
     if(bits>std::numeric_limits<unsigned>::max()/2-grow)
       throw overflow_error("root guard refinement exhausted");
     bits+=grow;
     ++RetryWork.guardOnlyRefinements;
     refreshRoot();
     continue; // old authenticated E_n, original n unchanged.
   }
   if(decision.sector!=paper9_dyadic_sector::Sector::ExtendSeries)
     throw runtime_error("unrecognized exact dyadic decision sector");
   // Series interval is genuinely too wide for the exact candidate.
   const unsigned grow=max(1u,n/16);
   if(n>std::numeric_limits<unsigned>::max()-grow)
     throw overflow_error("source cutoff extension exhausted");
   const unsigned nextN=n+grow;
   // Exact signed-defect reopening; original suffix composition unchanged.
   auto reopened=std::move(edge).releasePrefix();
   ++RetryWork.signedPReopenDivisions;
   Triple prefix{std::move(reopened.p),std::move(reopened.q),std::move(reopened.t)};
   Triple suffix=planSource(n,nextN,liveCarrier(prefix));
   ++RetryWork.suffixTreeBuilds;
   Triple joined=composeOrderedSource(std::move(prefix),
                                      std::move(suffix),inplace);
   n=nextN;
   FC.terminalCarrierBytes=liveCarrier(joined);
   originalTerminalTripleBits=
       wordBits(joined.p)+wordBits(joined.q)+wordBits(joined.t);
   edge=paper9_defect_source::Edge::fromNormalizedTriple(
      n,std::move(joined.p),std::move(joined.q),std::move(joined.t),SourceWork);
   ++RetryWork.seriesOnlyRefinements;
   // Guard precision and cached root are valid for this new n,
   // since the same 10005 radical does not depend on series cutoff.
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
   <<" retry_classifier=common_unscaled_quotient_signed_correction"
   <<" slack_lower_dyadic_divmods="<<BoundaryWork.lowerDyadicDivmods
   <<" slack_lower_integer_divmods="<<BoundaryWork.lowerIntegerDivmods
   <<" source_defect_builds="<<SourceWork.defectBuilds
   <<" source_odd_positive_bit_proofs="<<SourceWork.oddPositiveBitProofs
   <<" source_odd_positive_exact_checks="<<SourceWork.oddPositiveExactChecks
   <<" source_even_endpoint_products="<<SourceWork.evenEndpointProducts
   <<" source_odd_magnitude_copies="<<SourceWork.oddMagnitudeCopies
   <<" slack_source_defect_products="<<BoundaryWork.sourceDefectProducts
   <<" slack_slack_parity_products="<<BoundaryWork.slackParityProducts
   <<" slack_slack_tail_products="<<BoundaryWork.slackTailProducts
   <<" slack_correction_parity_products="<<BoundaryWork.correctionParityProducts
   <<" slack_upper_correction_products="<<BoundaryWork.upperCorrectionProducts
   <<" slack_middle_parity_products="<<BoundaryWork.middleParityProducts
   <<" slack_nonpositive_slack="<<BoundaryWork.nonpositiveSlack
   <<" tail_budget_shifts="<<BoundaryWork.budgetShifts
   <<" tail_nonpositive_budgets="<<BoundaryWork.nonpositiveBudgets
   <<" tail_bit_bound_admissions="<<BoundaryWork.bitBoundAdmissions
   <<" tail_prefix_bound_admissions="<<BoundaryWork.prefixBoundAdmissions
   <<" tail_prefix_attempts="<<BoundaryWork.prefixAttempts
   <<" tail_exact_tail_fallbacks="<<BoundaryWork.exactTailFallbacks
   <<" tail_budget_ties="<<BoundaryWork.budgetTies
   <<" quotient_common_even_quotients="<<BoundaryWork.commonEvenQuotients
   <<" quotient_zero_product_proofs="<<BoundaryWork.zeroProductProofs
   <<" quotient_bit_product_proofs="<<BoundaryWork.bitProductProofs
   <<" quotient_signed_residual_products="<<BoundaryWork.signedResidualProducts
   <<" quotient_signed_tail_submul="<<BoundaryWork.signedTailSubmul
   <<" quotient_dyadic_carry_products="<<BoundaryWork.dyadicCarryProducts
   <<" quotient_zero_correction_before_carry="<<BoundaryWork.zeroCorrectionBeforeCarry
   <<" quotient_zero_correction_after_carry="<<BoundaryWork.zeroCorrectionAfterCarry
   <<" quotient_corrected_floors="<<BoundaryWork.correctedFloors
   <<" quotient_single_correction_bit_proofs="<<BoundaryWork.singleCorrectionBitProofs
   <<" quotient_single_correction_exact_checks="<<BoundaryWork.singleCorrectionExactChecks
   <<" quotient_correction_divmods="<<BoundaryWork.correctionDivmods
   <<" quotient_multi_integer_corrections="<<BoundaryWork.multiIntegerCorrections
   <<" quotient_common_slack_checks="<<BoundaryWork.commonSlackChecks
   <<" quotient_corrected_slack_checks="<<BoundaryWork.correctedSlackChecks
   <<" quotient_corrected_radical_products="<<BoundaryWork.correctedRadicalProducts
   <<" quotient_observed_f_zeros="<<BoundaryWork.observedFZeros
   <<" slack_comparisons="<<BoundaryWork.comparisons
   <<" slack_exact_zeros="<<BoundaryWork.exactZeros
   <<" retry_lazy_classifications="<<LazyWork.classifierCalls
   <<" retry_lazy_decimalQ_products="<<LazyWork.baseDecimalQProducts
   <<" retry_lazy_shared_radical_products="<<LazyWork.sharedRadicalProducts
   <<" retry_lazy_initial_lower_q_products="<<LazyWork.initialLowerParityQProducts
   <<" retry_lazy_lower_remainders="<<LazyWork.lowerRemaindersConstructed
   <<" retry_lazy_upper_dyadic_quotients="<<LazyWork.upperDyadicQuotients
   <<" retry_lazy_upper_eta_failure_only="<<LazyWork.upperRemaindersOnFailure
   <<" retry_lazy_upper_signed_correction="<<LazyWork.upperSignedCorrectionsOnFailure
   <<" retry_lazy_upper_q_products="<<LazyWork.upperParityQProducts
   <<" retry_lazy_late_other_endpoint_q_products="<<LazyWork.lateSourceUpperQProductsEven
   <<" retry_lazy_late_other_endpoint_exact_divisions="<<LazyWork.lateSourceUpperDivisionsOdd
   <<" retry_lazy_late_other_endpoint_dyadic_shifts="<<LazyWork.lateSourceUpperDyadicShifts
   <<" retry_lazy_late_source_checks="<<LazyWork.lowerSourceBoundChecks
   <<" retry_lazy_upper_witness_failures="<<LazyWork.witnessFailures
   <<" retry_lazy_root_ambiguous_upper="<<LazyWork.ambiguousUpperSource
   <<" retry_lazy_root_ambiguous_lower="<<LazyWork.ambiguousLowerSource
   <<" retry_lazy_source_blocked="<<LazyWork.sourceBlocked
   <<" retry_lazy_admitted="<<LazyWork.admitted
   <<" retry_lazy_GMP_hooks_cover_temporaries=true"
   <<" retry_lazy_cost_optimality_proved=false"
   <<" retry_initial_tree_builds="<<RetryWork.initialTreeBuilds
   <<" retry_suffix_tree_builds="<<RetryWork.suffixTreeBuilds
   <<" retry_signed_P_reopening_divisions="<<RetryWork.signedPReopenDivisions
   <<" retry_guard_only_refinements="<<RetryWork.guardOnlyRefinements
   <<" retry_series_only_refinements="<<RetryWork.seriesOnlyRefinements
   <<" retry_exact_square_classifications="<<RetryWork.exactSquareClassifications
   <<" retry_square_slack_admissions="<<RetryWork.squareSlackAdmissions
   <<" retry_root_builds="<<RetryWork.rootBuilds
   <<" retry_certificate_attempts="<<RetryWork.certificateAttempts
   <<" retry_planner_nodes_total="<<RetryWork.scheduleNodesTotal
   <<" retry_planner_right_first_total="<<RetryWork.scheduleRightFirstTotal
   <<" source_indexed_affine_edge_exact=true"
   <<" source_full_prefix_rebuild_on_retry=false"
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
