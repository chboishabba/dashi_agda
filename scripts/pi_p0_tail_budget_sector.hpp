// COMP6c UNTESTED: integer tail budgets and sufficient product bounds.
// Original signed Chudnovsky source, not a new series or stopping policy.
#pragma once
#include "pi_p0_affine_boundary_sector.hpp"
#include <limits>
namespace paper9_tail_budget_sector {
using namespace paper9_lazy_lower_sector;
using paper9_affine_boundary_sector::compareShifted;
struct BoundaryCounts {
 uint64_t lowerDyadicDivmods=0,lowerIntegerDivmods=0;
 uint64_t sourceDefectProducts=0,slackParityProducts=0,slackTailProducts=0;
 uint64_t correctionParityProducts=0,upperCorrectionProducts=0;
 uint64_t middleParityProducts=0,nonpositiveSlack=0;
 uint64_t comparisons=0,exactZeros=0;
 uint64_t budgetShifts=0,nonpositiveBudgets=0,bitBoundAdmissions=0;
 uint64_t prefixBoundAdmissions=0,prefixAttempts=0,exactTailFallbacks=0,budgetTies=0;
};
// Return sign of nonnegative a - 2^k*b even for signed b.
inline int compareSlack(const Z& a,const Z& b,unsigned k,BoundaryCounts& w){
 if(a<0) throw std::logic_error("negative slack correction");
 ++w.comparisons;
 const int s=b<0?1:compareShifted(a,b,k);
 if(!s) ++w.exactZeros;
 return s;
}

// Strictly certify u*v<K using exact bit lengths, then bounded high windows.
// No source-provenance assumption beyond the supplied positive integers.
// A false result is UNKNOWN, not a nonnegative residual or equality.
inline bool sufficientProduct(const Z& u,const Z& v,const Z& K,BoundaryCounts& w){
 if(u<=0||v<=0) throw std::invalid_argument("positive tail factors");
 if(K<=0){++w.nonpositiveBudgets;return false;}
 const size_t lu=mpz_sizeinbase(u.get_mpz_t(),2),
              lv=mpz_sizeinbase(v.get_mpz_t(),2),
              lk=mpz_sizeinbase(K.get_mpz_t(),2);
 if(lu<=lk-1 && lv<=lk-1-lu){++w.bitBoundAdmissions;return true;}
 // For each operand keep at most 64 high bits. (prefix+1)*2^shift
 // is a STRICT upper bound even when the omitted suffix is zero.
 const size_t su=lu>64?lu-64:0, sv=lv>64?lv-64:0;
 if(su>std::numeric_limits<mp_bitcnt_t>::max() ||
    sv>std::numeric_limits<mp_bitcnt_t>::max()-su) return false;
 Z hu,hv;
 mpz_fdiv_q_2exp(hu.get_mpz_t(),u.get_mpz_t(),su);
 mpz_fdiv_q_2exp(hv.get_mpz_t(),v.get_mpz_t(),sv);
 Z bound=(hu+1)*(hv+1);
 ++w.prefixAttempts;
 if(compareShifted(K,bound,su+sv)>=0){++w.prefixBoundAdmissions;return true;}
 return false;
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
 mpz_fdiv_qr_2exp(packed.get_mpz_t(),ell.get_mpz_t(),packed.get_mpz_t(),k);
 ++boundary.lowerDyadicDivmods; ++work.lowerRemaindersConstructed;
 mpz_fdiv_qr(x.get_mpz_t(),rho.get_mpz_t(),packed.get_mpz_t(),Nh.get_mpz_t());
 ++boundary.lowerIntegerDivmods; ++work.lowerRemaindersConstructed;
 { Z dead; packed.swap(dead); }
 Z L=Nh-rho;
 { Z dead; rho.swap(dead); }
 Z slack=L;
 if(!even){
   mpz_mul(slack.get_mpz_t(),slack.get_mpz_t(),q.get_mpz_t());
   ++boundary.slackParityProducts;
 }
 // C=ell+a*Z, with a=q for even and a=1 for odd.
 // Compute in base's storage; the original edge/root recover base if needed.
 if(even){
   mpz_mul(base.get_mpz_t(),base.get_mpz_t(),q.get_mpz_t());
   ++boundary.correctionParityProducts;
 }
 mpz_add(base.get_mpz_t(),base.get_mpz_t(),ell.get_mpz_t());
 // K1=bL-floor(bC/2^k). Keep dyadic exactness separately from
 // a budget tie: floor equality alone does not mean original residual zero.
 Z K1;
 bool upperDyadicZero;
 {
   Z upper=base;
   if(!even){mpz_mul(upper.get_mpz_t(),upper.get_mpz_t(),q.get_mpz_t());
     ++boundary.upperCorrectionProducts;}
   upperDyadicZero=mpz_divisible_2exp_p(upper.get_mpz_t(),k)!=0;
   mpz_fdiv_q_2exp(upper.get_mpz_t(),upper.get_mpz_t(),k);
   ++boundary.budgetShifts;
   K1=slack-upper;
 }
 const Z successor=x+1;
 if(sufficientProduct(successor,e,K1,boundary)){
   ++work.admitted;return {std::move(x),Sector::AdmitFloor};
 }
 // Unknown is resolved by exact tail multiplication, not by rejection.
 Z tail=successor*e;
 ++boundary.exactTailFallbacks; ++boundary.slackTailProducts;
 { Z dead; e.swap(dead); }
 ++boundary.comparisons;
 if(tail<K1){++work.admitted;return {std::move(x),Sector::AdmitFloor};}
 if(tail==K1){++boundary.budgetTies;if(upperDyadicZero)++boundary.exactZeros;}
 ++work.witnessFailures;
 { Z dead; K1.swap(dead); }
 // K0=bL-floor(b*ell/2^k). Same intermediate COMP5w predicate.
 {
   Z middle=ell;
   if(!even){mpz_mul(middle.get_mpz_t(),middle.get_mpz_t(),q.get_mpz_t());
     ++boundary.middleParityProducts;}
   const bool middleDyadicZero=mpz_divisible_2exp_p(middle.get_mpz_t(),k)!=0;
   mpz_fdiv_q_2exp(middle.get_mpz_t(),middle.get_mpz_t(),k);
   ++boundary.budgetShifts;
   Z K0=slack-middle;
   ++boundary.comparisons;
   if(tail<K0){++work.ambiguousUpperSource;return {std::move(x),Sector::RefineRadical};}
   if(tail==K0){++boundary.budgetTies;if(middleDyadicZero)++boundary.exactZeros;}
 }
 { Z dead; slack.swap(dead); }
 { Z dead; tail.swap(dead); }
 { Z dead; ell.swap(dead); }
 ++work.lowerSourceBoundChecks;
 if(compareSlack(base,L,k,boundary)>=0){
   ++work.ambiguousLowerSource;return {std::move(x),Sector::RefineRadical};
 }
 ++work.sourceBlocked;return {std::move(x),Sector::ExtendSeries};
}
}
