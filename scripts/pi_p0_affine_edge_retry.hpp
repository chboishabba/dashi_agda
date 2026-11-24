// Paper 9 COMP5t (UNTESTED): reversible affine Chudnovsky endpoint edge.
// Exact source algebra only. Any caller must authenticate the original
// ordered P/Q/T producer and its prime-local projective gauge independently.
// No floating-point or user-precision truncation is used by this interface.
#pragma once
#include <gmpxx.h>
#include <stdexcept>
#include <utility>

namespace paper9_affine_retry {
using Z=mpz_class;

inline Z nextP(unsigned n){
 const Z i(n);
 return Z(-24)*(2*i-1)*(6*i-5)*(6*i-1);
}
inline Z nextQ(unsigned n){
 const Z i(n);
 const Z c=Z(640320)*640320*640320;
 return c*i*i*i;
}
inline Z nextA(unsigned n){
 return Z(13591409)+Z(545140134)*Z(n);
}
inline Z square(const Z& x){
 Z y;mpz_mul(y.get_mpz_t(),x.get_mpz_t(),x.get_mpz_t());return y;
}

// Source complete for the selected certified-adjacent-endpoint consumers:
// V_n = T_n*q_n + P_n*p_n*(A+B*n).
// (P,Q,T) <--> (T,Q,V_n), with the ORIGINAL cutoff n as an index.
// Projective prime-local scale G(0,n) is a SEPARATE indexed receipt.
struct Edge {
 unsigned n=0;
 Z t=0, q=1, v=0; // v is T_(n+1) numerator over Q_n*q_n
};

inline Edge fromNormalizedTriple(
    unsigned n,Z p,Z q,Z t){
 if(n<2 || q<=0 || t<=0)throw std::invalid_argument("source edge");
 const Z pn=nextP(n),an=nextA(n),qn=nextQ(n);
 if(p==0 || pn>=0 || an<=0 || qn<=0 ||
    (p<0)!=((n&1u)==0))throw std::invalid_argument("signed source cone");
 Z v=t*qn+p*pn*an;
 if(v<=0)throw std::invalid_argument("next endpoint not positive");
 return {n,std::move(t),std::move(q),std::move(v)};
}

inline Z sourceResidual(const Edge& edge){
 return edge.v-edge.t*nextQ(edge.n);
}

inline Z reconstructNormalizedP(const Edge& edge){
 if(edge.n<2 || edge.q<=0 || edge.t<=0 || edge.v<=0)
   throw std::invalid_argument("unusable indexed edge");
 const Z denom=nextP(edge.n)*nextA(edge.n);
 if(denom==0)throw std::invalid_argument("zero source-next factor");
 const Z delta=sourceResidual(edge);
 if(delta==0 || (delta>0)!=((edge.n&1u)==0))
   throw std::invalid_argument("signed residual cone");
 if(!mpz_divisible_p(delta.get_mpz_t(),denom.get_mpz_t()))
   throw std::invalid_argument("edge cannot reopen exact source P");
 Z p;
 mpz_divexact(p.get_mpz_t(),delta.get_mpz_t(),denom.get_mpz_t());
 if((p<0)!=((edge.n&1u)==0))throw std::invalid_argument("source P sign");
 return p;
}

// The full original raw triple is reconstructed only after multiplying
// the returned normalized p,q,t by the deterministic source scale
// G_[0,n) = product_(j=1)^(n-1) (24*h_j), from COMP5r/COMP5s.
inline bool signedConeAdmissible(const Edge& edge){
 if(edge.n<2 || edge.q<=0 || edge.t<=0 || edge.v<=0)return false;
 const Z delta=sourceResidual(edge);
 return delta!=0 && (delta>0)==((edge.n&1u)==0);
}

// Output-oriented views: for even n, S_n is lower; for odd n, S_n+1.
// The next denominator is derived from Q_n and the original q_n source.
struct OrderedEndpoints {
 const Z *lowerNum=nullptr,*lowerDen=nullptr;
 const Z *upperNum=nullptr,*upperDen=nullptr;
 Z nextDen=0;
};
inline OrderedEndpoints viewEndpoints(const Edge& edge){
 if(!signedConeAdmissible(edge))throw std::invalid_argument("bad source edge");
 OrderedEndpoints x;
 x.nextDen=edge.q*nextQ(edge.n);
 if((edge.n&1u)==0){
   x.lowerNum=&edge.t;x.lowerDen=&edge.q;
   x.upperNum=&edge.v;x.upperDen=&x.nextDen;
 }else{
   x.lowerNum=&edge.v;x.lowerDen=&x.nextDen;
   x.upperNum=&edge.t;x.upperDen=&edge.q;
 }
 // NOTE: addresses of nextDen inside a movable value are NOT stable
 // across return-by-value; callers must bind denominators after return.
 return x;
}

// Source-typed continuation classifier for current lower integer x.
// All numerators, denominators and F are nonnegative, denominators positive.
// The conservative dyadic lower quotient always obeys x<=K/S_hi.
// If (x+1)^2*N_hi^2 <=10005*F^2*D_hi^2, then the root guard alone
// has not yet resolved the lower floor; refine b with unchanged n.
// Otherwise x=floor(K/S_hi). The exact upper square test can then
// accept (without finer sqrt) or demand a genuine series extension.
enum class Repair { IncreaseRootGuard, AdmitBySquareSlack, ExtendSeries };
inline Repair selectRepair(const Z& x,const Z& F,
                           const Z& lowN,const Z& lowD,
                           const Z& highN,const Z& highD){
 if(x<0 || F<=0 || lowN<=0 || lowD<=0 || highN<=0 || highD<=0)
   throw std::invalid_argument("positive projective endpoint required");
 const Z successor=x+1;
 const Z lowerScaled=successor*highN;
 const Z rootScaled=F*highD;
 if(square(lowerScaled)<=Z(10005)*square(rootScaled))
   return Repair::IncreaseRootGuard;
 const Z upperScaled=successor*lowN;
 const Z lowerRootScaled=F*lowD;
 if(square(upperScaled)>Z(10005)*square(lowerRootScaled))
   return Repair::AdmitBySquareSlack;
 return Repair::ExtendSeries;
}

} // namespace paper9_affine_retry
