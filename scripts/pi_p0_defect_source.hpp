// COMP6d UNTESTED: producer-retained signed next-term coordinate.
// Authentic original ordered split and its indexed scale remain external.
#pragma once
#include "pi_p0_affine_edge_retry.hpp"
#include <cstdint>
#include <cstddef>
namespace paper9_defect_source {
using Z=mpz_class;
struct SourceCounts {
 uint64_t defectBuilds=0,oddPositiveBitProofs=0,oddPositiveExactChecks=0;
 uint64_t evenEndpointProducts=0,oddMagnitudeCopies=0;
};
struct Prefix { Z p,q,t; };
class Edge {
 unsigned n_;
 Z t_,q_,delta_;
 Edge(unsigned n,Z t,Z q,Z delta):
   n_(n),t_(std::move(t)),q_(std::move(q)),delta_(std::move(delta)){}
public:
 static Edge fromNormalizedTriple(unsigned n,Z p,Z q,Z t,SourceCounts& w){
   if(n<2||q<=0||t<=0||p==0||(p<0)!=((n&1u)==0))
     throw std::invalid_argument("invalid signed original prefix");
   const Z f=paper9_affine_retry::nextP(n)*paper9_affine_retry::nextA(n);
   if(f>=0) throw std::logic_error("invalid signed next-term factor");
   mpz_mul(p.get_mpz_t(),p.get_mpz_t(),f.get_mpz_t());
   ++w.defectBuilds;
   if(n&1u){
     // Need q_n*T' > |delta|. A lower bit-length bound can certify
     // positivity without constructing q_n*T' or V.
     const Z qn=paper9_affine_retry::nextQ(n);
     const size_t lt=mpz_sizeinbase(t.get_mpz_t(),2),
                  lq=mpz_sizeinbase(qn.get_mpz_t(),2),
                  le=mpz_sizeinbase(p.get_mpz_t(),2);
     // lt+lq-2 >= le, written without overflowing size_t.
     if(lt-1>=le || lq-1>=le-(lt-1)){
       ++w.oddPositiveBitProofs;
     }else{
       ++w.oddPositiveExactChecks;
       const Z v=t*qn+p;
       if(v<=0) throw std::invalid_argument("nonpositive adjacent source");
     }
   }
   return Edge(n,std::move(t),std::move(q),std::move(p));
 }
 unsigned n()const{return n_;}
 const Z& t()const{return t_;}
 const Z& q()const{return q_;}
 const Z& delta()const{return delta_;}
 bool signedConeAdmissible()const{
   return n_>=2&&q_>0&&t_>0&&delta_!=0&&
     (delta_>0)==((n_&1u)==0);
 }
 // Optional explicit BIDI consumer. Not used on odd admission.
 Z reopenV()const{
   if(!signedConeAdmissible())throw std::invalid_argument("invalid defect edge");
   return t_*paper9_affine_retry::nextQ(n_)+delta_;
 }
 Z reopenP()const{
   if(!signedConeAdmissible())throw std::invalid_argument("invalid defect edge");
   const Z f=paper9_affine_retry::nextP(n_)*paper9_affine_retry::nextA(n_);
   if(f>=0||!mpz_divisible_p(delta_.get_mpz_t(),f.get_mpz_t()))
     throw std::invalid_argument("nonintegral original prefix reopening");
   Z p;
   mpz_divexact(p.get_mpz_t(),delta_.get_mpz_t(),f.get_mpz_t());
   return p;
 }
 Prefix releasePrefix()&&{
   Z p=reopenP();
   {Z dead;delta_.swap(dead);}
   return {std::move(p),std::move(q_),std::move(t_)};
 }
};
}
