// COMP6e UNTESTED: common unscaled quotient, exact signed even correction.
// Reuses COMP6d odd route and original indexed defect producer.
// No full qY is formed in the even route, including correction fallback.
#pragma once
#include "pi_p0_gmp_dyadic_divmod.hpp"
#include "pi_p0_defect_sector.hpp"
#include <limits>
namespace paper9_quotient_sector {
using paper9_defect_sector::Z;
using paper9_defect_sector::Counts;
using paper9_defect_sector::Decision;
using paper9_defect_sector::Sector;
struct BoundaryCounts : paper9_defect_sector::BoundaryCounts {
 uint64_t commonEvenQuotients=0,zeroProductProofs=0,bitProductProofs=0;
 uint64_t signedResidualProducts=0,signedTailSubmul=0,dyadicCarryProducts=0;
 uint64_t zeroCorrectionBeforeCarry=0,zeroCorrectionAfterCarry=0;
 uint64_t correctedFloors=0,correctionDivmods=0,multiIntegerCorrections=0;
 uint64_t singleCorrectionBitProofs=0,singleCorrectionExactChecks=0;
 uint64_t commonSlackChecks=0,correctedSlackChecks=0,correctedRadicalProducts=0;
 uint64_t observedFZeros=0;
};
// Strict upper bound on x*e against lower bound on q*rho.
// No multiply or precision probe. False is unknown, NOT negative.
inline bool sufficientNoCorrection(const Z& x,const Z& e,const Z& q,
 const Z& rho,BoundaryCounts& w){
 if(x==0){++w.zeroProductProofs;return true;}
 if(rho==0)return false;
 const size_t lx=mpz_sizeinbase(x.get_mpz_t(),2),
              le=mpz_sizeinbase(e.get_mpz_t(),2),
              lq=mpz_sizeinbase(q.get_mpz_t(),2),
              lr=mpz_sizeinbase(rho.get_mpz_t(),2);
 const size_t cap=std::numeric_limits<size_t>::max();
 if(lx>cap-le || lq-1>cap-(lr-1))return false;
 if(lx+le<=(lq-1)+(lr-1)){
   ++w.bitProductProofs;return true;
 }
 return false;
}
inline Decision classify(unsigned digits,unsigned rootBits,const Z& root,
 const Z& decimal5,const paper9_defect_source::Edge& edge,Counts& work,
 BoundaryCounts& boundary,paper9_defect_source::SourceCounts& source){
 if(!digits||rootBits<digits||root<0||decimal5<=0||!edge.signedConeAdmissible())
   throw std::invalid_argument("invalid original indexed source or root");
 if(edge.n()&1u)
   return paper9_defect_sector::classify(digits,rootBits,root,decimal5,
       edge,work,boundary,source);
 const unsigned k=rootBits-digits;
 const Z q=paper9_affine_retry::nextQ(edge.n());
 const Z& T=edge.t();
 const Z& e=edge.delta();
 if(q<=0||T<=0||e<=0)throw std::invalid_argument("invalid even source");
 ++work.classifierCalls;
 ++boundary.commonEvenQuotients;
 Z base=Z(426880)*decimal5*edge.q();
 ++work.baseDecimalQProducts;
 Z packed=base*root;
 ++work.sharedRadicalProducts;
 Z ell,x0,rho;
 paper9_gmp::fdiv_qr_2exp(packed.get_mpz_t(),ell.get_mpz_t(),packed.get_mpz_t(),k);
 ++boundary.lowerDyadicDivmods; ++work.lowerRemaindersConstructed;
 mpz_fdiv_qr(x0.get_mpz_t(),rho.get_mpz_t(),packed.get_mpz_t(),T.get_mpz_t());
 ++boundary.lowerIntegerDivmods; ++work.lowerRemaindersConstructed;
 { Z dead; packed.swap(dead); }
 // Common x0 valid: upper-source lower radical is exactly in this cell.
 // Admission iff ell+base < 2^k(T-rho); otherwise refine upper radical.
 auto commonDecision=[&]()->Decision{
   const Z L=T-rho;
   mpz_add(base.get_mpz_t(),base.get_mpz_t(),ell.get_mpz_t());
   ++boundary.commonSlackChecks;
   const int sign=paper9_defect_sector::compareSlack(base,L,k,boundary);
   if(sign<0){++work.admitted;return {std::move(x0),Sector::AdmitFloor};}
   ++work.witnessFailures; ++work.ambiguousUpperSource;
   return {std::move(x0),Sector::RefineRadical};
 };
 if(sufficientNoCorrection(x0,e,q,rho,boundary)){
   ++boundary.zeroCorrectionBeforeCarry;
   return commonDecision();
 }
 Z F=q*rho;
 ++boundary.signedResidualProducts;
 mpz_submul(F.get_mpz_t(),x0.get_mpz_t(),e.get_mpz_t());
 ++boundary.signedTailSubmul;
 if(F>=0){
   // F0=0 does not prove F=0 without the unobserved carry.
   ++boundary.zeroCorrectionBeforeCarry;
   {Z dead;F.swap(dead);}
   return commonDecision();
 }
 // Only now transport the dyadic residue into the parity chart.
 Z eta=q*ell,carry;
 ++boundary.dyadicCarryProducts;
 paper9_gmp::fdiv_qr_2exp(carry.get_mpz_t(),eta.get_mpz_t(),eta.get_mpz_t(),k);
 F+=carry;
 {Z dead;carry.swap(dead);}
 if(F==0)++boundary.observedFZeros;
 if(F>=0){
   ++boundary.zeroCorrectionAfterCarry;
   {Z dead;F.swap(dead);}
   {Z dead;eta.swap(dead);}
   return commonDecision();
 }
 // F<0: upper-source lower radical has floor x0 > corrected x.
 // First and intermediate strict predicates MUST fail. Only the
 // opposite lower-source upper-radical crossing remains necessary.
 {Z dead;rho.swap(dead);}
 {Z dead;ell.swap(dead);}
 // Negative deficit d=-F. If d<=V, h=1 and the corrected
 // slack is exactly d: no division and no remainder reconstruction.
 // Prove d<q*T<=V with lower bit-length bounds when possible.
 const size_t lt=mpz_sizeinbase(T.get_mpz_t(),2),
              lq=mpz_sizeinbase(q.get_mpz_t(),2),
              ld=mpz_sizeinbase(F.get_mpz_t(),2);
 Z L;
 ++boundary.correctedFloors;
 if(lt-1>=ld || lq-1>=ld-(lt-1)){
   ++boundary.singleCorrectionBitProofs;
   x0-=1;
   L.swap(F);
   mpz_neg(L.get_mpz_t(),L.get_mpz_t());
 }else{
   Z V=T*q+e;
   ++source.evenEndpointProducts;
   if(mpz_cmpabs(F.get_mpz_t(),V.get_mpz_t())<=0){
     ++boundary.singleCorrectionExactChecks;
     x0-=1;
     L.swap(F);
     mpz_neg(L.get_mpz_t(),L.get_mpz_t());
   }else{
     Z correction,r;
     mpz_fdiv_qr(correction.get_mpz_t(),r.get_mpz_t(),F.get_mpz_t(),V.get_mpz_t());
     ++boundary.correctionDivmods;
     ++boundary.multiIntegerCorrections;
     if(correction>=-1||r<0||r>=V)
       throw std::logic_error("invalid multi-integer correction");
     x0+=correction;
     L=V-r;
   }
 }
 if(x0<0||L<=0)throw std::logic_error("invalid corrected floor or slack");
 {Z dead;F.swap(dead);}
 mpz_addmul(eta.get_mpz_t(),base.get_mpz_t(),q.get_mpz_t());
 ++boundary.correctedRadicalProducts;
 ++boundary.correctedSlackChecks;
 ++work.witnessFailures;
 ++work.lowerSourceBoundChecks;
 if(paper9_defect_sector::compareSlack(eta,L,k,boundary)>=0){
   ++work.ambiguousLowerSource;
   return {std::move(x0),Sector::RefineRadical};
 }
 ++work.sourceBlocked;
 return {std::move(x0),Sector::ExtendSeries};
}
}
