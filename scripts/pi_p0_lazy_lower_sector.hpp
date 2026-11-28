// Paper 9 COMP5w (UNTESTED): original Chudnovsky shared-root sector
// certificate with NO lower quotient remainders on the ordinary path,
// and NO lower quotient remainders even on the exceptional path.
//
// A single upper-root numerator W=H*(R+1)*Dlo is sufficient to recover
// the *upper radical bound of the lower-series endpoint* by the
// next-leaf factor q_n. This replaces COMP5v's retained rho and ell.
// The original signed source edge, indexed scale G_[0,n), zero-mode,
// and analytic Chudnovsky/Bishop premises remain distinct.
// Do not silently equate normalized raw-source dyadic remainders.
#pragma once
#include <gmpxx.h>
#include <stdexcept>
#include <utility>
#include <cstdint>
#include "pi_p0_affine_edge_retry.hpp"
#include "pi_p0_dyadic_sector_contraction.hpp"

namespace paper9_lazy_lower_sector {
using Z=mpz_class;
using Sector=paper9_dyadic_sector::Sector;
using Decision=paper9_dyadic_sector::Decision;

struct Counts {
 uint64_t classifierCalls=0;
 uint64_t baseDecimalQProducts=0;
 uint64_t sharedRadicalProducts=0;
 uint64_t initialLowerParityQProducts=0;
 uint64_t lowerDyadicQuotients=0;
 uint64_t lowerIntegerQuotients=0;
 uint64_t lowerRemaindersConstructed=0; // invariant 0 in this candidate
 uint64_t upperDyadicQuotients=0;
 uint64_t upperRemaindersOnFailure=0;
 uint64_t upperSignedCorrectionsOnFailure=0;
 uint64_t upperParityQProducts=0;
 uint64_t lateSourceUpperQProductsEven=0;
 uint64_t lateSourceUpperDivisionsOdd=0;
 uint64_t lateSourceUpperDyadicShifts=0;
 uint64_t lowerSourceBoundChecks=0;
 uint64_t witnessFailures=0;
 uint64_t ambiguousUpperSource=0,ambiguousLowerSource=0;
 uint64_t admitted=0,sourceBlocked=0;
};

// Let H=426880*5^d, k=b-d, R=floor(2^b sqrt(10005)),
// signed source edge E_n=(T,Q,V), original q=q_n and
// Z=H*Q, Y=Z*R.
// For n even:
//   Dlo=Q, Dhi=Q*q, A=HRDhi=q*Y, W=H(R+1)Dlo=Y+Z.
// For n odd:
//   Dlo=Q*q, Dhi=Q, A=Y, W=q*(Y+Z).
// The first lower floor requires only:
//   x=floor(floor(A/2^k)/Nhi).
// The ordinary strict upper witness requires only:
//   u=floor(W/2^k) < (x+1)Nlo.
// If the upper test fails, compute eta=W mod 2^k.
// The lower radical of the UPPER pi endpoint is:
//   floor((W-HDlo)/2^k)
// = u+floor((eta-HDlo)/2^k). If it remains BELOW
// (x+1)*Nlo, the radical guard may resolve the ambiguity.
// Otherwise the source UPPER pi endpoint is already >= x+1.
// The *other* next-root product H(R+1)Dhi can be reopened
// from W without any lower A quotient remainder:
//   even n -> q*W; odd n -> W/q (the division is EXACT).
// Thus floor(H(R+1)Dhi/2^k)>=(x+1)Nhi means the LOWER
// pi endpoint may still cross on radical refinement;
// otherwise the original source interval must be extended.
// This is EXACTLY the same conservative three-sector rule
// as COMP5u/v, but does not materialize rho or ell anywhere.
//
// The width of q is dependent on the original cutoff:
// q=(640320*n)^3. Parity Q multiplication/division incurs a
// REAL cost on an exceptional branch, not a free contraction.
inline Decision classify(
    unsigned digits,unsigned rootBits,const Z& root,const Z& decimal5,
    const paper9_affine_retry::Edge& edge,Counts& work) {
 if(digits==0 || rootBits<digits || root<0 || decimal5<=0 ||
    !paper9_affine_retry::signedConeAdmissible(edge))
   throw std::invalid_argument("invalid signed original source or root index");
 const unsigned k=rootBits-digits;
 const bool even=(edge.n&1u)==0;
 const Z q=paper9_affine_retry::nextQ(edge.n);
 if(q<=0||edge.q<=0||edge.t<=0||edge.v<=0)
   throw std::invalid_argument("nonpositive original source");
 const Z& lowerN=even?edge.t:edge.v;
 const Z& upperN=even?edge.v:edge.t;
 ++work.classifierCalls;

 Z base=Z(426880)*decimal5*edge.q;
 ++work.baseDecimalQProducts;
 Z radical=base*root;
 ++work.sharedRadicalProducts;

 // Ordinary lower floor uses only two QUOTIENT operations.
 // In odd parity, shift radical directly (do not copy it).
 Z shifted;
 if(even){
   Z A;
   mpz_mul(A.get_mpz_t(),radical.get_mpz_t(),q.get_mpz_t());
   ++work.initialLowerParityQProducts;
   mpz_fdiv_q_2exp(shifted.get_mpz_t(),A.get_mpz_t(),k);
 }else{
   mpz_fdiv_q_2exp(shifted.get_mpz_t(),radical.get_mpz_t(),k);
 }
 ++work.lowerDyadicQuotients;
 Z x;
 mpz_fdiv_q(x.get_mpz_t(),shifted.get_mpz_t(),upperN.get_mpz_t());
 ++work.lowerIntegerQuotients;
 { Z dead;shifted.swap(dead); }

 Z W=radical+base;
 { Z dead;radical.swap(dead); }
 if(!even) {
   mpz_mul(W.get_mpz_t(),W.get_mpz_t(),q.get_mpz_t());
   ++work.upperParityQProducts;
 }
 Z u;
 mpz_fdiv_q_2exp(u.get_mpz_t(),W.get_mpz_t(),k);
 ++work.upperDyadicQuotients;
 const Z nextThreshold=(x+1)*lowerN;
 if(u<nextThreshold){
   ++work.admitted;
   return {std::move(x),Sector::AdmitFloor};
 }
 ++work.witnessFailures;

 // FAILURE ONLY: exact upper dyadic remainder and signed correction.
 Z eta;
 mpz_fdiv_r_2exp(eta.get_mpz_t(),W.get_mpz_t(),k);
 ++work.upperRemaindersOnFailure;
 Z scaleLo=base;
 if(!even) {
   mpz_mul(scaleLo.get_mpz_t(),scaleLo.get_mpz_t(),q.get_mpz_t());
   ++work.upperParityQProducts;
 }
 Z upperCorrection=eta-scaleLo;
 mpz_fdiv_q_2exp(upperCorrection.get_mpz_t(),
                  upperCorrection.get_mpz_t(),k);
 ++work.upperSignedCorrectionsOnFailure;
 if(u+upperCorrection<nextThreshold){
   ++work.ambiguousUpperSource;
   return {std::move(x),Sector::RefineRadical};
 }
 { Z dead;eta.swap(dead); }
 { Z dead;scaleLo.swap(dead); }
 { Z dead;upperCorrection.swap(dead); }
 { Z dead;u.swap(dead); }
 { Z dead;base.swap(dead); }

 // Only on a TRUE fixed-source upper-obstruction candidate:
 // Reuse W for the opposite series endpoint's *upper radical*
 // WITHOUT recomputing a large root multiplication or rho,ell.
 if(even){
   mpz_mul(W.get_mpz_t(),W.get_mpz_t(),q.get_mpz_t());
   ++work.lateSourceUpperQProductsEven;
 }else{
   // W was explicitly constructed as q*(Y+Z), so exact divisibility
   // is structural. Reject rather than silently use truncation
   // if this source identity was ever violated.
   if(!mpz_divisible_p(W.get_mpz_t(),q.get_mpz_t()))
     throw std::logic_error("non-divisible signed source next-root witness");
   mpz_divexact(W.get_mpz_t(),W.get_mpz_t(),q.get_mpz_t());
   ++work.lateSourceUpperDivisionsOdd;
 }
 mpz_fdiv_q_2exp(W.get_mpz_t(),W.get_mpz_t(),k);
 ++work.lateSourceUpperDyadicShifts;
 ++work.lowerSourceBoundChecks;
 const Z otherThreshold=(x+1)*upperN;
 if(W>=otherThreshold) {
   ++work.ambiguousLowerSource;
   return {std::move(x),Sector::RefineRadical};
 }
 ++work.sourceBlocked;
 return {std::move(x),Sector::ExtendSeries};
}

} // namespace paper9_lazy_lower_sector
