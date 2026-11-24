// Paper 9 COMP5v (UNTESTED): share ONE radical product between the two
// Chudnovsky adjacent endpoint consumers. Do not import SAT/finite-field claims.
// Preserve original ordered P/Q/T provenance, indexed positive source scale,
// signed residual/zero-mode domain, and exact dyadic Euclidean floor semantics.
#pragma once
#include <gmpxx.h>
#include <stdexcept>
#include <utility>
#include <cstdint>
#include "pi_p0_affine_edge_retry.hpp"
#include "pi_p0_dyadic_sector_contraction.hpp"

namespace paper9_shared_radical {
using Z=mpz_class;
using Sector=paper9_dyadic_sector::Sector;
using Decision=paper9_dyadic_sector::Decision;

struct Counts {
 uint64_t classifierCalls=0;
 uint64_t baseDecimalTimesQProducts=0;
 uint64_t sharedRadicalProducts=0;
 uint64_t parityQProducts=0;
 uint64_t lowerDyadicQrs=0;
 uint64_t lowerIntegerQrs=0;
 uint64_t upperDyadicQuotients=0;
 uint64_t upperDyadicRemaindersOnFailure=0;
 uint64_t upperSignedFloorCorrections=0;
 uint64_t lowerDyadicFloorCorrections=0;
 uint64_t upperWitnessFailures=0,upperRootAmbiguous=0;
 uint64_t lowerRootAmbiguous=0;
 uint64_t admitted=0,sourceBlocked=0;
};

// SOURCE FACTORIZATION:
// Let E_n=(T,Q,V=T*q+P*p_n*a_n), q=q_n>0, H=426880*5^d,
// k=b-d, R=floor(2^b sqrt(10005)), Z=H*Q, Y=Z*R.
// For EVEN n:  S_lo=T/Q, S_hi=V/(Q*q),
//              lowerPacked=q*Y, upperPacked=Y+Z.
// For ODD n:   S_lo=V/(Q*q), S_hi=T/Q,
//              lowerPacked=Y, upperPacked=q*(Y+Z).
// Thus original A=H*R*D_hi and W=H*(R+1)*D_lo
// are *both* computed from a SINGLE source-common Y, not two
// independent root multiplications. The usual lower/upper
// integer quotients and 3-sector failure decisions are UNCHANGED.
// On successful first upper admission, NO eta remainder is created.
// On failure, W yields eta by mod 2^k, and the original COMP5u
// signed correction decides guard-only versus suffix-only repair.
//
// Source authenticity of E_n and raw-scale G_[0,n) are independent
// external obligations. The algorithm does not truncate any integer.
inline Decision classify(
    unsigned digits,unsigned rootBits,const Z& root,const Z& decimal5,
    const paper9_affine_retry::Edge& edge,Counts& work) {
 if(digits==0 || rootBits<digits || root<0 || decimal5<=0 ||
    !paper9_affine_retry::signedConeAdmissible(edge))
   throw std::invalid_argument("invalid original positive signed edge");
 const unsigned k=rootBits-digits;
 const bool even=(edge.n&1u)==0;
 const Z q=paper9_affine_retry::nextQ(edge.n);
 if(q<=0)throw std::invalid_argument("nonpositive original next q");
 const Z& upperN=even?edge.v:edge.t;
 const Z& lowerN=even?edge.t:edge.v;
 if(upperN<=0 || lowerN<=0 || edge.q<=0)
   throw std::invalid_argument("nonpositive source numerator");
 ++work.classifierCalls;

 Z base=Z(426880)*decimal5*edge.q;
 ++work.baseDecimalTimesQProducts;
 Z radical=base*root;
 ++work.sharedRadicalProducts;

 Z A=radical;
 if(even) {
   mpz_mul(A.get_mpz_t(),A.get_mpz_t(),q.get_mpz_t());
   ++work.parityQProducts;
 }
 Z lowerShift,ell;
 mpz_fdiv_qr_2exp(lowerShift.get_mpz_t(),ell.get_mpz_t(),
                    A.get_mpz_t(),k);
 ++work.lowerDyadicQrs;
 {Z dead;A.swap(dead);}
 Z x,rho;
 mpz_fdiv_qr(x.get_mpz_t(),rho.get_mpz_t(),
              lowerShift.get_mpz_t(),upperN.get_mpz_t());
 ++work.lowerIntegerQrs;
 {Z dead;lowerShift.swap(dead);}

 Z W=radical+base;
 {Z dead;radical.swap(dead);}
 if(!even) {
   mpz_mul(W.get_mpz_t(),W.get_mpz_t(),q.get_mpz_t());
   ++work.parityQProducts;
 }
 Z upperShift;
 mpz_fdiv_q_2exp(upperShift.get_mpz_t(),W.get_mpz_t(),k);
 ++work.upperDyadicQuotients;
 const Z boundary=(x+1)*lowerN;
 if(upperShift<boundary) {
   ++work.admitted;
   return {std::move(x),Sector::AdmitFloor};
 }
 ++work.upperWitnessFailures;

 // Only failed certificates need the W remainder; do not retain eta
 // in the ordinary acceptance path.
 Z eta;
 mpz_fdiv_r_2exp(eta.get_mpz_t(),W.get_mpz_t(),k);
 ++work.upperDyadicRemaindersOnFailure;
 {Z dead;W.swap(dead);}

 // Exact floor(H*R*D_lo/2^k) from the already-computed
 // upper H*(R+1)*D_lo decomposition, with SIGNED floor correction.
 Z scaleLo=base;
 if(!even) {
   mpz_mul(scaleLo.get_mpz_t(),scaleLo.get_mpz_t(),q.get_mpz_t());
   ++work.parityQProducts;
 }
 Z upperCorrection=eta-scaleLo;
 mpz_fdiv_q_2exp(upperCorrection.get_mpz_t(),
                   upperCorrection.get_mpz_t(),k);
 ++work.upperSignedFloorCorrections;
 if(upperShift+upperCorrection<boundary) {
   ++work.upperRootAmbiguous;
   return {std::move(x),Sector::RefineRadical};
 }
 {Z dead;upperCorrection.swap(dead);}
 {Z dead;scaleLo.swap(dead);}
 {Z dead;eta.swap(dead);}

 // Exact crossing of the lower-source quotient's next integer
 // from rho,ell without recomputing any radical product.
 Z scaleHi=base;
 if(even) {
   mpz_mul(scaleHi.get_mpz_t(),scaleHi.get_mpz_t(),q.get_mpz_t());
   ++work.parityQProducts;
 }
 Z lowerCorrection=ell+scaleHi;
 mpz_fdiv_q_2exp(lowerCorrection.get_mpz_t(),
                   lowerCorrection.get_mpz_t(),k);
 ++work.lowerDyadicFloorCorrections;
 if(rho+lowerCorrection>=upperN) {
   ++work.lowerRootAmbiguous;
   return {std::move(x),Sector::RefineRadical};
 }
 ++work.sourceBlocked;
 return {std::move(x),Sector::ExtendSeries};
}

} // namespace paper9_shared_radical
