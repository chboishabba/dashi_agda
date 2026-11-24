// Paper 9 COMP5o (UNTESTED): root-free exact integer-square floor verifier.
//
// This is a CONSUMER of source-authenticated original Chudnovsky P/Q/T,
// not a proof that arbitrary user-supplied triples are true binary splits.
// It verifies a candidate floor x for 10^d*pi, conditional on the classical
// Chudnovsky identity and the alternating two-neighbour enclosure.
//
// No mpz_sqrt or floating arithmetic. The large squares may be more costly
// than the original square-root certificate; benchmark/acceptance DEFERRED.
#pragma once
#include <gmpxx.h>
#include <stdexcept>
#include <utility>

namespace paper9_square_verifier {
using Z=mpz_class;

struct SourcePQT {
  Z p,q,t;
  unsigned cutoff;
  // Caller owes the ordered original source identity:
  // M(0,cutoff) = [[p,t],[0,q]], with original p_j,q_j,A+B*j.
};

struct SquareCertificate {
  bool sourceSignAdmissible=false;
  bool lowerAdmitted=false;
  bool upperAdmitted=false;
  Z lowerSquareSlack=0; // 10005*(F*Dhi)^2 - (x*Nhi)^2
  Z upperSquareSlack=0; // ((x+1)*Nlo)^2 - 10005*(F*Dlo)^2
  // Full acceptance is sourceSignAdmissible && both inequalities.
  bool accepted() const {
    return sourceSignAdmissible && lowerAdmitted && upperAdmitted;
  }
};

inline Z square(const Z& x){
  Z out;
  mpz_mul(out.get_mpz_t(),x.get_mpz_t(),x.get_mpz_t());
  return out;
}

inline SquareCertificate certifyCandidateFloor(
    unsigned digits,const Z& x,const SourcePQT& source){
  SquareCertificate proof;
  const unsigned n=source.cutoff;
  if(n<2 || x<0 || source.q<=0 || source.t<=0)return proof;

  const Z index(n);
  const Z a=Z(13591409)+Z(545140134)*index;
  const Z pn=Z(-24)*(2*index-1)*(6*index-5)*(6*index-1);
  const Z c=Z(640320)*640320*640320;
  const Z qn=c*index*index*index;
  const bool pIsNegative=source.p<0;

  // Actual original source signs: p_j<0 for j>=1 and
  // sign P(0,n)=(-1)^(n-1), Q(0,n)>0. The caller must
  // ALSO provide an authenticated ordered P/Q/T source receipt.
  if(pn>=0 || qn<=0 || a<=0 ||
     pIsNegative!=((n&1u)==0))return proof;

  Z residual=source.p*pn*a;
  Z nextN=source.t*qn+residual, nextD=source.q*qn;
  if(nextN<=0 || nextD<=0 || (residual>0)!=((n&1u)==0))
    return proof;

  Z lowN=source.t, lowD=source.q;
  Z highN=std::move(nextN), highD=std::move(nextD);
  if(n&1u){
    lowN.swap(highN);
    lowD.swap(highD);
  }
  proof.sourceSignAdmissible=true;

  // Exact output scaling K_d=426880*10^d*sqrt(10005).
  // Certified floor means x*S_hi <= K_d and K_d < (x+1)*S_lo.
  // For nonnegative quantities we may square both comparisons:
  // (x*Nhi)^2 <= 10005*(F*Dhi)^2
  // 10005*(F*Dlo)^2 < ((x+1)*Nlo)^2 .
  Z F;
  mpz_ui_pow_ui(F.get_mpz_t(),10,digits);
  mpz_mul_ui(F.get_mpz_t(),F.get_mpz_t(),426880);

  {
    const Z left=x*highN, right=F*highD;
    proof.lowerSquareSlack=Z(10005)*square(right)-square(left);
    proof.lowerAdmitted=proof.lowerSquareSlack>=0;
  }
  {
    const Z left=F*lowD, right=(x+1)*lowN;
    proof.upperSquareSlack=square(right)-Z(10005)*square(left);
    proof.upperAdmitted=proof.upperSquareSlack>0;
  }
  return proof;
}
} // namespace paper9_square_verifier
