// COMP6e source-matched acceptance packet. NOT executed at authoring time.
// Build from repository root:
// c++ -O2 -std=c++17 scripts/check_pi_p0_quotient_sector_exact.cpp -lgmpxx -lgmp -o /tmp/pi_p0_quotient_exact
// /tmp/pi_p0_quotient_exact
#include "pi_p0_quotient_sector.hpp"
#include <iostream>
#include <stdexcept>
namespace S=paper9_quotient_sector;
namespace D=paper9_defect_source;
using Z=mpz_class;
using Sector=S::Sector;
static void require(bool ok,const char* msg){if(!ok)throw std::runtime_error(msg);}
static S::Decision direct(unsigned d,unsigned bits,const Z& R,const Z& decimal5,const D::Edge& edge){
 const bool even=(edge.n()&1u)==0;
 const Z q=paper9_affine_retry::nextQ(edge.n()), V=edge.reopenV();
 const Z& T=edge.t();
 const Z& Nh=even?V:T;
 const Z& Nl=even?T:V;
 const Z a=even?q:Z(1), b=even?Z(1):q;
 const Z H=Z(426880)*decimal5*edge.q();
 const Z DY=Z(1)<<(bits-d);
 const Z Y=H*R, A=a*Y, den=DY*Nh;
 Z x;
 mpz_fdiv_q(x.get_mpz_t(),A.get_mpz_t(),den.get_mpz_t());
 const Z hi=DY*(x+1)*Nl, lo=DY*(x+1)*Nh;
 if(b*(Y+H)<hi)return {x,Sector::AdmitFloor};
 if(b*Y<hi)return {x,Sector::RefineRadical};
 if(a*(Y+H)>=lo)return {x,Sector::RefineRadical};
 return {x,Sector::ExtendSeries};
}
static unsigned long cases=0,authentic=0,synthetic=0,multi=0,aliasCases=0;
static void check(unsigned d,unsigned bits,const Z& R,const Z& decimal5,
                  unsigned n,const Z& P,const Z& Q,const Z& T,bool actual){
 D::SourceCounts src;
 const auto edge=D::Edge::fromNormalizedTriple(n,P,Q,T,src);
 require(edge.reopenP()==P,"source P BIDI");
 require(edge.reopenV()==T*paper9_affine_retry::nextQ(n)+edge.delta(),"source V BIDI");
 S::Counts w,priorW; S::BoundaryCounts b;
 paper9_defect_sector::BoundaryCounts priorB;
 const auto got=S::classify(d,bits,R,decimal5,edge,w,b,src);
 const auto want=direct(d,bits,R,decimal5,edge);
 const auto prior=paper9_defect_sector::classify(d,bits,R,decimal5,edge,priorW,priorB,src);
 require(got.x==want.x&&got.sector==want.sector,"literal corner mismatch");
 require(got.x==prior.x&&got.sector==prior.sector,"COMP6d mismatch");
 require(w.initialLowerParityQProducts==0,"full parity numerator rebuilt");
 const auto scaled=D::Edge::fromNormalizedTriple(n,17*P,17*Q,17*T,src);
 S::Counts sw; S::BoundaryCounts sb;
 const auto gs=S::classify(d,bits,R,decimal5,scaled,sw,sb,src);
 require(gs.x==got.x&&gs.sector==got.sector,"positive gauge mismatch");
 ++cases; if(actual)++authentic;else ++synthetic;
 multi+=b.multiIntegerCorrections;
}
static void aliasChecks(){
 for(long i=-257;i<=257;++i)for(unsigned k=0;k<=12;++k){
   const Z a=i, D=Z(1)<<k;
   Z q,r;
   mpz_fdiv_qr(q.get_mpz_t(),r.get_mpz_t(),a.get_mpz_t(),D.get_mpz_t());
   Z u=a,v;
   paper9_gmp::fdiv_qr_2exp(u.get_mpz_t(),v.get_mpz_t(),u.get_mpz_t(),k);
   require(u==q&&v==r,"quotient alias mismatch");
   u=a;v=0;
   paper9_gmp::fdiv_qr_2exp(v.get_mpz_t(),u.get_mpz_t(),u.get_mpz_t(),k);
   require(v==q&&u==r,"remainder alias mismatch");
   ++aliasCases;
 }
}
int main(){
 aliasChecks();
 // Actual original unnormalized ordered prefix, no fabricated series values.
 Z P=1,Q=1,T=13591409;
 for(unsigned j=1;j<=16;++j){
   const Z p=paper9_affine_retry::nextP(j),q=paper9_affine_retry::nextQ(j);
   T=T*q+P*p*paper9_affine_retry::nextA(j); P*=p; Q*=q;
   for(unsigned d:{1u,7u,14u,28u,60u}){
     const unsigned bits=4*d+16;
     const Z rad=Z(10005)<<(2*bits);
     Z R,decimal5; mpz_sqrt(R.get_mpz_t(),rad.get_mpz_t());
     mpz_ui_pow_ui(decimal5.get_mpz_t(),5,d);
     check(d,bits,R,decimal5,j+1,P,Q,T,true);
   }
 }
 // Shape-valid synthetic signed edges, NOT authenticated Chudnovsky prefixes.
 // Tiny/large T and varied root scales exercise large correction, k=0,
 // zero root, and exact arithmetic boundaries without relying on pi.
 for(unsigned n=2;n<=9;++n)for(unsigned m=1;m<=5;++m){
   Z p=m;if((n&1u)==0)p=-p;
   const Z delta=p*paper9_affine_retry::nextP(n)*paper9_affine_retry::nextA(n);
   const Z q=paper9_affine_retry::nextQ(n);
   Z T0=1;
   if(delta<0){Z e=-delta;mpz_fdiv_q(T0.get_mpz_t(),e.get_mpz_t(),q.get_mpz_t());T0+=1;}
   for(unsigned s:{0u,8u,64u})for(unsigned k:{0u,1u,63u,64u,65u}){
     Z T=T0+(Z(1)<<s),Q=(Z(1)<<s)+m;
     for(unsigned long root:{0ul,1ul,17ul,1000000ul})
       check(1,k+1,Z(root),Z(5),n,p,Q,T,false);
   }
 }
 require(multi>0,"multi-integer correction not exercised");
 std::cout<<"cases="<<cases<<" authentic="<<authentic<<" synthetic="<<synthetic
          <<" multi="<<multi<<" alias_cases="<<aliasCases<<" PASS\n";
}
