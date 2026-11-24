// Paper 9 COMP5s: source-aware output-precision scheduling model (UNTESTED).
// A forecast changes only the evaluation order of two independent children.
// It NEVER truncates P/Q/T, swaps the ordered product, relaxes certificates,
// or authenticates raw source integers without a separate scale receipt.
#pragma once
#include <algorithm>
#include <cmath>
#include <cstddef>
#include <limits>
#include <memory>

namespace paper9_projective_schedule {

struct WidthShape {
  long double pBits=0, qBits=0, tBits=0;
  long double storageBytes=0;
};

struct Plan {
  unsigned begin=0, end=0;
  bool rightFirst=false;
  WidthShape width;
  long double predictedPeakBytes=0;
  std::unique_ptr<Plan> left, right;
};

struct PlanningLedger {
  unsigned digits=0;
  unsigned precisionBits=0; // original root-enclosure precision index
  unsigned activeDepth=0;
  size_t planNodes=0, scheduledMerges=0, rightFirstMerges=0;
  long double modelPeakBytes=0;
  size_t planningObjectPayloadBytes=0; // exact sizeof(Plan)*count; excludes C++ allocator overhead
};

// Conservative mathematical magnitude estimates for the normalized source
// (not machine-certified FLOAT bounds and not measured allocation).
// Original normalized positive-index leaves:
//   |p_j| <= 72*j^3 and 0<q_j <= (640320^3/24)*j^3.
// Extra indexed prime content h_j>=1 only DECREASES their magnitudes.
// Each |p_j/q_j|=|P_j/Q_j| <1. Therefore for any interval [a,b),
//   |T_ab/Q_ab| <= (b-a)*(13591409+545140134*(b-1)).
// Uses the original ordered upper-triangular multiplication and triangle
// inequality; its logged floating evaluation is scheduling-only.
inline WidthShape projectedWidth(unsigned a,unsigned b) {
  if(a>=b) return {1,1,0,2};
  const unsigned lo=std::max(1u,a);
  const long double n= b>lo ? static_cast<long double>(b-lo):0.0L;
  const long double two=std::log(2.0L);
  const long double factorialLog2 = b>lo
      ? (std::lgamma(static_cast<long double>(b))
         -std::lgamma(static_cast<long double>(lo)))/two
      : 0.0L;
  const long double qConstant=(640320.0L*640320.0L*640320.0L)/24.0L;
  WidthShape result;
  // q has a positive exact bound; p can be negative, never zero.
  result.pBits=2.0L+n*std::log2(72.0L)+3.0L*factorialLog2;
  result.qBits=2.0L+n*std::log2(qConstant)+3.0L*factorialLog2;
  const long double maxIndex=static_cast<long double>(b-1);
  const long double maxCoef=13591409.0L+545140134.0L*maxIndex;
  result.tBits=result.qBits+std::log2(static_cast<long double>(b-a))
                 +std::log2(maxCoef)+3.0L;
  result.storageBytes=(result.pBits+result.qBits+result.tBits)/8.0L+24.0L;
  return result;
}
inline bool usable(long double x) {
  return std::isfinite(x) && x>=0;
}
inline std::unique_ptr<Plan> build(
    unsigned a,unsigned b,unsigned depth,unsigned precisionBits,
    PlanningLedger& stats,unsigned maxDepth=10) {
  auto plan=std::make_unique<Plan>();
  plan->begin=a;plan->end=b;
  plan->width=projectedWidth(a,b);
  ++stats.planNodes;
  stats.activeDepth=std::max(stats.activeDepth,depth);
  const long double size=plan->width.storageBytes;
  // Unplanned estimate includes a coarse factor for scratch and parent
  // allocations; it is NOT an observed, proved or tight GMP memory bound.
  plan->predictedPeakBytes=4.0L*size;
  const long double cutoffBits=std::max(
      4096.0L,static_cast<long double>(precisionBits)/16.0L);
  if(b-a<2 || depth>=maxDepth ||
      !usable(size) || size*8.0L<cutoffBits)
    return plan;

  const unsigned m=a+(b-a)/2;
  plan->left=build(a,m,depth+1,precisionBits,stats,maxDepth);
  plan->right=build(m,b,depth+1,precisionBits,stats,maxDepth);
  const long double ls=plan->left->width.storageBytes;
  const long double rs=plan->right->width.storageBytes;
  const long double lp=plan->left->predictedPeakBytes;
  const long double rp=plan->right->predictedPeakBytes;
  const long double mergeScratch=2.0L*
      std::max({plan->width.pBits,plan->width.qBits,
                plan->width.tBits})/8.0L;
  const long double mergePeak=ls+rs+mergeScratch;
  const long double leftFirst=std::max({lp,ls+rp,mergePeak});
  const long double rightFirst=std::max({rp,rs+lp,mergePeak});
  if(usable(leftFirst) && usable(rightFirst)) {
    ++stats.scheduledMerges;
    plan->rightFirst=rightFirst<leftFirst;
    if(plan->rightFirst) ++stats.rightFirstMerges;
    plan->predictedPeakBytes=std::min(leftFirst,rightFirst);
  }
  return plan;
}

inline std::unique_ptr<Plan> makePlan(
    unsigned cutoff,unsigned digits,unsigned precisionBits,
    PlanningLedger& ledger) {
  ledger=PlanningLedger{};
  ledger.digits=digits;
  ledger.precisionBits=precisionBits;
  std::unique_ptr<Plan> root=build(0,cutoff,0,precisionBits,ledger);
  ledger.modelPeakBytes=root->predictedPeakBytes;
  ledger.planningObjectPayloadBytes=ledger.planNodes*sizeof(Plan);
  return root;
}

// Raw source reconstruction is indexed, NOT an implicit equality.
// For original P/Q/T leaves M_j and prime-local content h_j,
//   M'_j=M_j/(24*h_j) (j>0), M'_0=M_0.
// For [a,b), G=product_(j in [a,b),j>0)(24*h_j).
// Product and signed next-term delta are homogeneous under G>0.
// The constant-time scale receipt is (a,b,prime-support,recipe),
// NOT the full huge integer G. Exact reopening computes G when needed.
// A future consumer requiring raw P/Q/T does NOT factor through
// M' alone without this receipt.
} // namespace paper9_projective_schedule
