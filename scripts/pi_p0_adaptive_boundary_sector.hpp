// COMP6a UNTESTED: bounded high-prefix interval observer with exact COMP5z fallback.
#pragma once
#include "pi_p0_affine_boundary_sector.hpp"
#include <algorithm>
namespace paper9_adaptive_boundary_sector {
using namespace paper9_lazy_lower_sector;
using paper9_affine_boundary_sector::compareShifted;
struct BoundaryCounts {
 uint64_t streamedProducts=0, fallbackProducts=0;
 uint64_t prefixAttempts=0,prefixDecisions=0,prefixExact=0,prefixFallbacks=0,prefixLimbsRead=0;
 uint64_t comparisons=0, exactZeros=0, failureUpperLowerProducts=0,
 failureOtherProducts=0;
};

// Import only the selected high window, including virtual dyadic boundary
// limbs. No full shifted integer or quotient is constructed.
inline Z highWindow(const Z& a,size_t h,size_t width,mp_bitcnt_t shift) {
 if(width>32) throw std::invalid_argument("prefix width");
 mp_limb_t buf[32]={};
 const size_t n=mpz_size(a.get_mpz_t());
 const size_t whole=shift/GMP_NUMB_BITS;
 const unsigned part=shift%GMP_NUMB_BITS;
 for(size_t i=0;i<width;++i){
   const size_t at=h+i;
   if(at<whole) continue;
   const size_t j=at-whole;
   if(j<n) buf[i]=(mpz_getlimbn(a.get_mpz_t(),j)<<part)&GMP_NUMB_MASK;
   if(part&&j&&j-1<n)
      buf[i]|=mpz_getlimbn(a.get_mpz_t(),j-1)>>(GMP_NUMB_BITS-part);
 }
 Z out;
 mpz_import(out.get_mpz_t(),width,-1,sizeof(mp_limb_t),0,GMP_NAIL_BITS,buf);
 return out;
}
inline int adaptiveCompare(const Z& a,const Z& z,const Z& q,const Z& b,
 mp_bitcnt_t k,BoundaryCounts& work) {
 if(a<0||z<0||q<0||b<0) throw std::invalid_argument("negative adaptive operand");
 if(q==0||(a==0&&z==0)) return b==0?0:-1;
 if(b==0) return 1;
 const auto fallback=[&](){
   ++work.prefixFallbacks;
   return paper9_affine_boundary_sector::compareAffineProductShifted(
      a,z,q,b,k,work.streamedProducts,work.fallbackProducts);
 };
 if(mpz_size(q.get_mpz_t())>2) return fallback();
 const size_t nb=mpz_size(b.get_mpz_t()), whole=k/GMP_NUMB_BITS;
 if(whole>std::numeric_limits<size_t>::max()-nb-1) return fallback();
 const unsigned part=k%GMP_NUMB_BITS;
 const size_t bn=whole+nb+
   (part&& (mpz_getlimbn(b.get_mpz_t(),nb-1)>>(GMP_NUMB_BITS-part)) ? 1:0);
 const size_t total=std::max({mpz_size(a.get_mpz_t()),mpz_size(z.get_mpz_t()),bn});
 // For a nonzero unknown lower block, q(aL+zL)-bL is strictly
 // between -M^h and t*q*M^h, where t is the number of nonzero operands.
 const Z negativeLimit=-(q*((a!=0&&z!=0)?2:1));
 for(size_t cap:{size_t(4),size_t(8),size_t(16),size_t(32)}){
   const size_t width=std::min(cap,total), h=total-width;
   const Z ah=highWindow(a,h,width,0), zh=highWindow(z,h,width,0),
           bh=highWindow(b,h,width,k);
   const Z delta=q*(ah+zh)-bh;
   ++work.prefixAttempts;
   work.prefixLimbsRead+=3*width; // window slots, not physical memory reads
   if(!h){++work.prefixExact;return mpz_sgn(delta.get_mpz_t());}
   if(delta>0){++work.prefixDecisions;return 1;}
   if(delta<=negativeLimit){++work.prefixDecisions;return -1;}
 }
 return fallback(); // unknown is never silently identified with equality
}
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
   const int sign=adaptiveCompare(a,zero,q,b,k,boundary);
   if(!sign) ++boundary.exactZeros;
   return sign;
 };
 auto cmpAffine=[&](const Z& factor,const Z& b){
   ++boundary.comparisons;
   const int sign=adaptiveCompare(Y,base,factor,b,k,boundary);
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
