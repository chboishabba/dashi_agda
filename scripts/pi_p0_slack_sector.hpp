// COMP6b UNTESTED: both-parity slack fibre, generalizing COMP5q.
// Original signed Chudnovsky source, not a new series or stopping policy.
#pragma once
#include "pi_p0_gmp_dyadic_divmod.hpp"
#include "pi_p0_affine_boundary_sector.hpp"
namespace paper9_slack_sector {
using namespace paper9_lazy_lower_sector;
using paper9_affine_boundary_sector::compareShifted;
struct BoundaryCounts {
 uint64_t lowerDyadicDivmods=0,lowerIntegerDivmods=0;
 uint64_t sourceDefectProducts=0,slackParityProducts=0,slackTailProducts=0;
 uint64_t correctionParityProducts=0,upperCorrectionProducts=0;
 uint64_t middleParityProducts=0,nonpositiveSlack=0;
 uint64_t comparisons=0,exactZeros=0;
};
// Return sign of nonnegative a - 2^k*b even for signed b.
inline int compareSlack(const Z& a,const Z& b,unsigned k,BoundaryCounts& w){
 if(a<0) throw std::logic_error("negative slack correction");
 ++w.comparisons;
 const int s=b<0?1:compareShifted(a,b,k);
 if(!s) ++w.exactZeros;
 return s;
}
inline Decision classify(unsigned digits,unsigned rootBits,const Z& root,
 const Z& decimal5,const paper9_affine_retry::Edge& edge,Counts& work,
 BoundaryCounts& boundary){
 if(!digits||rootBits<digits||root<0||decimal5<=0||
    edge.n<2||edge.q<=0||edge.t<=0||edge.v<=0)
   throw std::invalid_argument("invalid indexed source or root");
 const unsigned k=rootBits-digits;
 const bool even=(edge.n&1u)==0;
 const Z q=paper9_affine_retry::nextQ(edge.n);
 if(q<=0) throw std::invalid_argument("nonpositive next q");
 Z e=edge.v-edge.t*q;
 ++boundary.sourceDefectProducts;
 if(e==0||(e>0)!=even) throw std::invalid_argument("signed source cone");
 if(!even) e=-e;
 // The original signed source is still recoverable from edge and n.
 const Z& Nh=even?edge.v:edge.t;
 const Z& Nl=even?edge.t:edge.v;
 (void)Nl; // used by derivation, no absolute endpoint threshold needed.
 ++work.classifierCalls;
 Z base=Z(426880)*decimal5*edge.q;
 ++work.baseDecimalQProducts;
 Z packed=base*root;
 ++work.sharedRadicalProducts;
 if(even){
   mpz_mul(packed.get_mpz_t(),packed.get_mpz_t(),q.get_mpz_t());
   ++work.initialLowerParityQProducts;
 }
 Z ell,x,rho;
 // GMP input/output alias permitted; the two output objects are distinct.
 paper9_gmp::fdiv_qr_2exp(packed.get_mpz_t(),ell.get_mpz_t(),packed.get_mpz_t(),k);
 ++boundary.lowerDyadicDivmods; ++work.lowerRemaindersConstructed;
 mpz_fdiv_qr(x.get_mpz_t(),rho.get_mpz_t(),packed.get_mpz_t(),Nh.get_mpz_t());
 ++boundary.lowerIntegerDivmods; ++work.lowerRemaindersConstructed;
 { Z dead; packed.swap(dead); }
 Z L=Nh-rho;
 { Z dead; rho.swap(dead); }
 Z J=L;
 if(!even){
   mpz_mul(J.get_mpz_t(),J.get_mpz_t(),q.get_mpz_t());
   ++boundary.slackParityProducts;
 }
 mpz_submul(J.get_mpz_t(),Z(x+1).get_mpz_t(),e.get_mpz_t());
 ++boundary.slackTailProducts;
 { Z dead; e.swap(dead); }

 // C=ell+a*Z, with a=q for even and a=1 for odd.
 // Compute in base's storage; the original edge/root recover base if needed.
 if(even){
   mpz_mul(base.get_mpz_t(),base.get_mpz_t(),q.get_mpz_t());
   ++boundary.correctionParityProducts;
 }
 mpz_add(base.get_mpz_t(),base.get_mpz_t(),ell.get_mpz_t());
 // Admission: b*C < 2^k J. If J<=0, no strict negative sign possible.
 if(J>0){
   int sign;
   if(even) sign=compareSlack(base,J,k,boundary);
   else {
     Z upper=q*base;
     ++boundary.upperCorrectionProducts;
     sign=compareSlack(upper,J,k,boundary);
   }
   if(sign<0){++work.admitted;return {std::move(x),Sector::AdmitFloor};}
   ++work.witnessFailures;
   // Same intermediate upper-source lower-root predicate as COMP5w.
   if(even) sign=compareSlack(ell,J,k,boundary);
   else {
     Z middle=q*ell;
     ++boundary.middleParityProducts;
     sign=compareSlack(middle,J,k,boundary);
   }
   if(sign<0){++work.ambiguousUpperSource;return {std::move(x),Sector::RefineRadical};}
 }else{
   ++boundary.nonpositiveSlack;
   ++work.witnessFailures;
   // J<0 makes both residuals positive; J=0 can give exact middle
   // equality when ell=0. Equality is never a strict admission/refine.
   if(J==0){
     if(base==0) ++boundary.exactZeros;
     if(ell==0) ++boundary.exactZeros;
   }
 }
 { Z dead; J.swap(dead); }
 { Z dead; ell.swap(dead); }
 ++work.lowerSourceBoundChecks;
 if(compareSlack(base,L,k,boundary)>=0){
   ++work.ambiguousLowerSource;return {std::move(x),Sector::RefineRadical};
 }
 ++work.sourceBlocked;return {std::move(x),Sector::ExtendSeries};
}
}
