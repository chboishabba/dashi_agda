// COMP5z: fused affine parity boundary comparator; untested candidate.
#pragma once
#include "pi_p0_lazy_lower_sector.hpp"
#include <limits>
namespace paper9_affine_boundary_sector {
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
// Fixed-width fast path on ordinary nail-free <=64-bit GMP with uint128.
// Separate multiply streams avoid overflowing a 128-bit sum of two products.
// Other configurations and wider q fall back to exact GMP multiplication.
inline int compareAffineProductShifted(const Z& a,const Z& z,const Z& q,const Z& b,
 mp_bitcnt_t k, uint64_t& streamed,uint64_t& fallback) {
 if(a<0||z<0||q<0||b<0) throw std::invalid_argument("negative product boundary");
 if((a==0&&z==0)||q==0) return b==0?0:-1;
 if(b==0) return 1;
#if defined(__SIZEOF_INT128__) && GMP_NAIL_BITS == 0 && GMP_NUMB_BITS <= 64
 if(mpz_size(q.get_mpz_t())<=2) {
   using Wide=unsigned __int128;
   const size_t na=mpz_size(a.get_mpz_t()), nz=mpz_size(z.get_mpz_t()), nb=mpz_size(b.get_mpz_t());
   const size_t n=na>nz?na:nz;
   const size_t whole=k/GMP_NUMB_BITS;
   const unsigned part=k%GMP_NUMB_BITS;
   // Affine sum has at most n+1 limbs; product at most n+3. A nonzero shifted b has at least
   // whole+nb limbs. Avoid overflow in length arithmetic.
   if(n>std::numeric_limits<size_t>::max()-3 ||
      whole>std::numeric_limits<size_t>::max()-nb)
     throw std::overflow_error("boundary support");
   const size_t end=n+3;
   ++streamed;
   if(whole+nb>end) return -1;
   // Check whether the shifted boundary extends beyond product support.
   if(whole+nb==end && part &&
      (mpz_getlimbn(b.get_mpz_t(),nb-1)>>(GMP_NUMB_BITS-part))) return -1;
   const mp_limb_t q0=mpz_getlimbn(q.get_mpz_t(),0);
   const mp_limb_t q1=mpz_getlimbn(q.get_mpz_t(),1);
   Wide c0=0,c1=0;
   unsigned affineCarry=0;
   mp_limb_t previous=0;
   unsigned addCarry=0;
   int sign=0;
   for(size_t i=0;i<end;++i) {
     const Wide affine=Wide(i<na?mpz_getlimbn(a.get_mpz_t(),i):0)
       + (i<nz?mpz_getlimbn(z.get_mpz_t(),i):0)+affineCarry;
     const mp_limb_t ai=static_cast<mp_limb_t>(affine);
     affineCarry=static_cast<unsigned>(affine>>GMP_NUMB_BITS);
     const Wide t0=Wide(q0)*ai+c0;
     const Wide t1=Wide(q1)*ai+c1;
     c0=t0>>GMP_NUMB_BITS; c1=t1>>GMP_NUMB_BITS;
     const Wide sum=Wide(static_cast<mp_limb_t>(t0))+previous+addCarry;
     const mp_limb_t p=static_cast<mp_limb_t>(sum);
     addCarry=static_cast<unsigned>(sum>>GMP_NUMB_BITS);
     previous=static_cast<mp_limb_t>(t1);
     mp_limb_t v=0;
     if(i>=whole) {
       const size_t j=i-whole;
       if(j<nb) v=mpz_getlimbn(b.get_mpz_t(),j)<<part;
       if(part && j && j-1<nb)
         v|=mpz_getlimbn(b.get_mpz_t(),j-1)>>(GMP_NUMB_BITS-part);
     }
     if(p!=v) sign=p<v?-1:1;
   }
   if(affineCarry||c0||c1||previous||addCarry) throw std::logic_error("unflushed product");
   return sign;
 }
#endif
 ++fallback;
 const Z product=(a+z)*q;
 return compareShifted(product,b,k);
}
struct BoundaryCounts {
 uint64_t streamedProducts=0, fallbackProducts=0;
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
 const Z zero=0, one=1;
 const Z threshold=(x+1)*lowerN;
 auto cmp=[&](const Z& a,const Z& b){
   ++boundary.comparisons;
   const int s=compareShifted(a,b,k);
   if(!s) ++boundary.exactZeros;
   return s;
 };
 auto cmpProduct=[&](const Z& a,const Z& b){
   ++boundary.comparisons;
   const int sign=compareAffineProductShifted(a,zero,q,b,k,boundary.streamedProducts,boundary.fallbackProducts);
   if(!sign) ++boundary.exactZeros;
   return sign;
 };
 auto cmpAffine=[&](const Z& factor,const Z& b){
   ++boundary.comparisons;
   const int sign=compareAffineProductShifted(Y,base,factor,b,k,boundary.streamedProducts,boundary.fallbackProducts);
   if(!sign) ++boundary.exactZeros;
   return sign;
 };
 // No materialized affine corner on supported streaming path.
 int admission;
 admission=cmpAffine(even?one:q,threshold);
 if(admission<0){++work.admitted;return {std::move(x),Sector::AdmitFloor};}
 ++work.witnessFailures;
 int lowerRoot;
 if(even) lowerRoot=cmp(Y,threshold);
 else lowerRoot=cmpProduct(Y,threshold);
 if(lowerRoot<0){++work.ambiguousUpperSource;return {std::move(x),Sector::RefineRadical};}
 ++work.lowerSourceBoundChecks;
 const Z other=(x+1)*upperN;
 int crossing;
 crossing=cmpAffine(even?q:one,other);
 if(crossing>=0){++work.ambiguousLowerSource;return {std::move(x),Sector::RefineRadical};}
 ++work.sourceBlocked;
 return {std::move(x),Sector::ExtendSeries};
}
}
