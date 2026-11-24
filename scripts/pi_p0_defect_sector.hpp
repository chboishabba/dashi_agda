// COMP6d UNTESTED: retain signed defect, materialize only selected endpoint.
#pragma once
#include "pi_p0_tail_budget_sector.hpp"
#include "pi_p0_defect_source.hpp"
namespace paper9_defect_sector {
using namespace paper9_tail_budget_sector;
inline Decision classify(unsigned digits,unsigned rootBits,const Z& root,
 const Z& decimal5,const paper9_defect_source::Edge& edge,Counts& work,
 BoundaryCounts& boundary,paper9_defect_source::SourceCounts& source){
 if(!digits||rootBits<digits||root<0||decimal5<=0||
    !edge.signedConeAdmissible())
   throw std::invalid_argument("invalid indexed source or root");
 const unsigned k=rootBits-digits;
 const bool even=(edge.n()&1u)==0;
 const Z q=paper9_affine_retry::nextQ(edge.n());
 if(q<=0) throw std::invalid_argument("nonpositive next q");
 // The producer proved positivity and retained the original signed defect.
 // Only odd parity needs a temporary positive magnitude for COMP6c.
 Z magnitude;
 if(!even){mpz_abs(magnitude.get_mpz_t(),edge.delta().get_mpz_t());
   ++source.oddMagnitudeCopies;}
 const Z& e=even?edge.delta():magnitude;
 // Only even parity needs V for the lower quotient. Odd uses T directly.
 Z adjacent;
 if(even){
   adjacent=edge.t()*q+edge.delta();
   ++source.evenEndpointProducts;
 }
 const Z& Nh=even?adjacent:edge.t();
 ++work.classifierCalls;
 Z base=Z(426880)*decimal5*edge.q();
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
 { Z dead; adjacent.swap(dead); } // Nh not used below this point
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
 { Z dead; magnitude.swap(dead); }
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
