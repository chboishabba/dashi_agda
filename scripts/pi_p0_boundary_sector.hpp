// COMP5x: exact four-corner boundary comparator; untested candidate.
#pragma once
#include "pi_p0_lazy_lower_sector.hpp"
#include <limits>
namespace paper9_boundary_sector {
using namespace paper9_lazy_lower_sector;
// Compare nonnegative a with b*2^k without allocating a shifted integer.
// GMP_NUMB_BITS excludes nail bits. mpz_getlimbn returns value limbs.
inline int compareShifted(const Z& a,const Z& b,mp_bitcnt_t k) {
 if(a<0 || b<0) throw std::invalid_argument("negative boundary operand");
 if(b==0) return mpz_sgn(a.get_mpz_t());
 if(a==0) return -1;
 const size_t ab=mpz_sizeinbase(a.get_mpz_t(),2);
 const size_t bb=mpz_sizeinbase(b.get_mpz_t(),2);
 if(ab<bb) return -1;
 const size_t gap=ab-bb;
 if(gap<k) return -1;
 if(gap>k) return 1;
 const size_t whole=k/GMP_NUMB_BITS;
 const unsigned part=k%GMP_NUMB_BITS;
 for(size_t i=mpz_size(a.get_mpz_t());i-- >0;) {
   mp_limb_t rhs=0;
   if(i>=whole) {
     const size_t j=i-whole;
     rhs=(mpz_getlimbn(b.get_mpz_t(),j)<<part)&GMP_NUMB_MASK;
     if(part && j) rhs|=mpz_getlimbn(b.get_mpz_t(),j-1)>>(GMP_NUMB_BITS-part);
   }
   const mp_limb_t lhs=mpz_getlimbn(a.get_mpz_t(),i);
   if(lhs!=rhs) return lhs<rhs?-1:1;
 }
 return 0;
}
struct BoundaryCounts {
 uint64_t comparisons=0, exactZeros=0, failureUpperLowerProducts=0,
 failureOtherProducts=0;
};
inline Decision classify(unsigned digits,unsigned rootBits,const Z& root,
 const Z& decimal5,const paper9_affine_retry::Edge& edge,Counts& work,
 BoundaryCounts& boundary) {
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
 Z Y=base*root;
 ++work.sharedRadicalProducts;
 Z shifted;
 if(even){
   Z A=Y*q;
   ++work.initialLowerParityQProducts;
   mpz_fdiv_q_2exp(shifted.get_mpz_t(),A.get_mpz_t(),k);
 }else mpz_fdiv_q_2exp(shifted.get_mpz_t(),Y.get_mpz_t(),k);
 ++work.lowerDyadicQuotients;
 Z x;
 mpz_fdiv_q(x.get_mpz_t(),shifted.get_mpz_t(),upperN.get_mpz_t());
 ++work.lowerIntegerQuotients;
 { Z dead; shifted.swap(dead); }
 Z U=Y+base;
 { Z dead; base.swap(dead); }
 const Z threshold=(x+1)*lowerN;
 auto cmp=[&](const Z& a,const Z& b){
   ++boundary.comparisons;
   const int s=compareShifted(a,b,k);
   if(!s) ++boundary.exactZeros;
   return s;
 };
 // Keep U unscaled in odd parity; only one temporary scaled corner.
 int admission;
 if(even) admission=cmp(U,threshold);
 else { Z W=q*U; ++work.upperParityQProducts; admission=cmp(W,threshold); }
 if(admission<0){++work.admitted;return {std::move(x),Sector::AdmitFloor};}
 ++work.witnessFailures;
 int lowerRoot;
 if(even) lowerRoot=cmp(Y,threshold);
 else { Z W=q*Y; ++boundary.failureUpperLowerProducts; lowerRoot=cmp(W,threshold); }
 if(lowerRoot<0){++work.ambiguousUpperSource;return {std::move(x),Sector::RefineRadical};}
 { Z dead; Y.swap(dead); }
 ++work.lowerSourceBoundChecks;
 const Z other=(x+1)*upperN;
 int crossing;
 if(even){ Z W=q*U; ++boundary.failureOtherProducts; crossing=cmp(W,other); }
 else crossing=cmp(U,other);
 if(crossing>=0){++work.ambiguousLowerSource;return {std::move(x),Sector::RefineRadical};}
 ++work.sourceBlocked;
 return {std::move(x),Sector::ExtendSeries};
}
}
