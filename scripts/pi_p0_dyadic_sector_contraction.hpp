// Paper 9 COMP5u (UNTESTED): exact dyadic residue-sector certificate.
// Inspired by P-vs-NP G83's lesson: large explicit representations do NOT
// impose the same cost on every selected consumer. No P-vs-NP theorem is
// imported. Every calculation below is original-source GMP integer arithmetic.
// The original Chudnovsky identity/tail and P/Q/T provenance remain EXTERNAL.
#pragma once
#include <gmpxx.h>
#include <stdexcept>
#include <cstdint>
#include <utility>

namespace paper9_dyadic_sector {
using Z=mpz_class;

// The only LIVE decision outcomes, not the full width of the P/Q/T geometry.
// Invalid original signed/zero source belongs to a separate rejected domain.
enum class Sector { AdmitFloor, RefineRadical, ExtendSeries };

struct Counts {
 uint64_t classifierCalls=0;
 uint64_t dyadicQuotientRemainders=0;
 uint64_t integerQuotientRemainders=0;
 uint64_t signedDyadicQuotients=0;
 uint64_t endpointScaleProducts=0; // logical f*D computations, not GMP mul count
 uint64_t upperRootFailed=0, lowerRootAmbiguous=0;
 uint64_t upperRootAmbiguous=0, sourceBlocked=0, admitted=0;
};

struct Decision {
 Z x=0;
 Sector sector=Sector::RefineRadical;
 // In the selected consumer, the full source n and b indexes and
 // original signed edge are retained separately by the caller.
};

// Let H=426880*5^d, k=b-d, R=floor(2^b sqrt(10005)).
// For authenticated 0<S_lo=Nlo/Dlo <= S <= S_hi=Nhi/Dhi:
//   x=floor(H*R*Dhi/(2^k*Nhi)).
// Instead of expanding full exact radical squares, make the decision
// from quotient/remainder sectors at the exact CURRENT dyadic precision.
// This can over-refine b relative to the perfect-square classifier,
// but never incorrectly admit or incorrectly force a source extension.
//
// Correctness identities (for all nonnegative integer numerators):
//   A = 2^k*(x*Nhi+rho)+ell, 0<=rho<Nhi, 0<=ell<2^k.
//   floor((A+H*Dhi)/2^k)=x*Nhi+rho+floor((ell+H*Dhi)/2^k)
//   W = 2^k*u+eta, 0<=eta<2^k.
//   floor((W-H*Dlo)/2^k)=u+floor((eta-H*Dlo)/2^k).
// W=H*(R+1)*Dlo. Signed floor-shift is intentional: negative
// (eta-H*Dlo) MUST use floor, not truncation toward zero.
inline Decision classify(
    unsigned digits,unsigned rootBits,const Z& root,const Z& decimal5,
    const Z& lowerN,const Z& lowerD,
    const Z& upperN,const Z& upperD,
    Counts& work) {
 if(digits==0 || rootBits<digits || root<0 || decimal5<=0 ||
    lowerN<=0 || lowerD<=0 || upperN<=0 || upperD<=0)
   throw std::invalid_argument("positive indexed source and root required");
 const unsigned k=rootBits-digits;
 ++work.classifierCalls;
 const Z H=Z(426880)*decimal5;

 Z A=H*root*upperD;
 Z lowShift,ell;
 mpz_fdiv_qr_2exp(lowShift.get_mpz_t(),ell.get_mpz_t(),
                   A.get_mpz_t(),k);
 ++work.dyadicQuotientRemainders;
 Z x,rho;
 mpz_fdiv_qr(x.get_mpz_t(),rho.get_mpz_t(),
             lowShift.get_mpz_t(),upperN.get_mpz_t());
 ++work.integerQuotientRemainders;
 { Z empty;A.swap(empty); }

 Z W=H*(root+1)*lowerD;
 Z upperShift,eta;
 mpz_fdiv_qr_2exp(upperShift.get_mpz_t(),eta.get_mpz_t(),
                   W.get_mpz_t(),k);
 ++work.dyadicQuotientRemainders;
 { Z empty;W.swap(empty); }
 const Z boundary=(x+1)*lowerN;
 if(upperShift<boundary){
   ++work.admitted;
   return {std::move(x),Sector::AdmitFloor};
 }
 ++work.upperRootFailed;

 // Exact lower radical root of the U endpoint: H*R*Dlo.
 // Reuse W=H*(R+1)*Dlo and its quotient/remainder, not a
 // second large radical product:
 //   floor((W-H*Dlo)/2^k)
 //     = upperShift + floor((eta-H*Dlo)/2^k).
 Z upperCorrection=eta-H*lowerD;
 ++work.endpointScaleProducts;
 mpz_fdiv_q_2exp(upperCorrection.get_mpz_t(),
                  upperCorrection.get_mpz_t(),k);
 ++work.signedDyadicQuotients;
 if(upperShift+upperCorrection<boundary){
   ++work.upperRootAmbiguous;
   return {std::move(x),Sector::RefineRadical};
 }

 // U_lo >= x+1: the original source upper endpoint is genuinely
 // too wide UNLESS the lower integer x itself is still root-ambiguous.
 // Detect that exactly from the already computed low-side remainders:
 //   floor((A+H*Dhi)/2^k) >= (x+1)*Nhi
 // iff rho + floor((ell+H*Dhi)/2^k) >= Nhi.
 Z lowerCorrection=ell+H*upperD;
 ++work.endpointScaleProducts;
 mpz_fdiv_q_2exp(lowerCorrection.get_mpz_t(),
                  lowerCorrection.get_mpz_t(),k);
 ++work.signedDyadicQuotients;
 if(rho+lowerCorrection>=upperN){
   ++work.lowerRootAmbiguous;
   return {std::move(x),Sector::RefineRadical};
 }
 ++work.sourceBlocked;
 return {std::move(x),Sector::ExtendSeries};
}

// EXACT SOURCE-GAUGE REOPENING for the intermediate Euclidean fibres.
// This routine is intentionally NOT called by the fast floor consumer.
// If the true raw P/Q/T/endpoint numerator and denominator equal the
// normalized ones times indexed scalar G>0, then the decimal floor is
// invariant but (rho,ell) are NOT equal to G*(rho',ell').
// With A'=2^k*(x*N'+rho')+ell', the raw integer A=G*A' has
//   t=floor(G*ell'/2^k), ell=(G*ell') mod 2^k,
//   rho=G*rho'+t, N=G*N'.
// This is the creation-vs-reopening CARRY ledger; omitting t is wrong.
// G must come from an authenticated original source-scale receipt.
struct GaugeReopening {
 Z rawN=0, rawRho=0, rawEll=0, carry=0;
};
inline GaugeReopening reopenRawDyadicFibre(
    const Z& indexedSourceScale,unsigned k,const Z& normN,
    const Z& normRho,const Z& normEll){
 if(indexedSourceScale<=0 || normN<=0 || normRho<0 ||
    normRho>=normN || normEll<0 ||
    (normEll!=0 && mpz_sizeinbase(normEll.get_mpz_t(),2)>k))
   throw std::invalid_argument("invalid indexed normalized remainder fibre");
 GaugeReopening out;
 Z scaledEll=indexedSourceScale*normEll;
 mpz_fdiv_qr_2exp(out.carry.get_mpz_t(),out.rawEll.get_mpz_t(),
                   scaledEll.get_mpz_t(),k);
 out.rawN=indexedSourceScale*normN;
 out.rawRho=indexedSourceScale*normRho+out.carry;
 if(out.rawRho>=out.rawN)
   throw std::logic_error("raw quotient remainder carry exceeded numerator");
 return out;
}

// Additional provenance obligation: reopening a signed residual
// delta'=V'-T'*q_n requires delta=G*delta'.  The affine edge and all
// original source index/normalization recipe data must be preserved.
// A coarse floor/hash does not authenticate the original coefficients.
} // namespace paper9_dyadic_sector
