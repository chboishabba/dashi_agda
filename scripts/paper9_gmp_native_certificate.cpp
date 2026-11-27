// Exact certificate adapter for the ORIGINAL GMP quotient/residual owner.
// Do not change the benchmark source or its pinned blob. Lean consumer:
// Integration.Paper9GmpCertificate.gmpAdmission (source-written).
// No external proof status is inferred from executing this binary.
#define main paper9_original_benchmark_main
#include "check_pi_gmp_quotient_residual.cpp"
#undef main
#include <fstream>
#include <limits>

static void require(bool b, const char* msg) {
 if (!b) throw std::runtime_error(msg);
}

// Proof-replay mode: same midpoint split and threshold branch as split().
// Emit postorder nodes with the literal exact cross-GCD division equations.
// The normal fast path calls original split without allocating a trace.
static Triple traceSplit(unsigned a,unsigned b,unsigned threshold,std::ostream& out) {
 if(a==b){out<<"empty "<<a<<"\n";return {1,1,0};}
 if(b-a==1){
  auto v=split(a,b,threshold);
  out<<"leaf "<<a<<" "<<v.p<<" "<<v.q<<" "<<v.t<<"\n";
  return v;
 }
 unsigned m=a+(b-a)/2;
 auto l=traceSplit(a,m,threshold,out),r=traceSplit(m,b,threshold,out);
 require(l.q>0&&r.q>0,"nonpositive child denominator");
 Z g=1,lp=l.p,rq=r.q;
 if(b-a>=threshold){
  mpz_gcd(g.get_mpz_t(),l.p.get_mpz_t(),r.q.get_mpz_t());
  require(g>0,"invalid cross gcd");
  mpz_divexact(lp.get_mpz_t(),l.p.get_mpz_t(),g.get_mpz_t());
  mpz_divexact(rq.get_mpz_t(),r.q.get_mpz_t(),g.get_mpz_t());
 }
 require(rq>0&&l.p==g*lp&&r.q==g*rq,"inexact gcd witness");
 Triple v{lp*r.p,l.q*rq,l.t*rq+lp*r.t};
 require(v.q>0,"nonpositive joined denominator");
 // The proof's reducedCoordinates: common factor on every coordinate.
 require(g*v.p==l.p*r.p&&g*v.q==l.q*r.q&&
         g*v.t==l.t*r.q+l.p*r.t,"signed reduction mismatch");
 out<<"join "<<a<<" "<<m<<" "<<b<<" "<<g<<" "<<lp<<" "<<rq
    <<" "<<v.p<<" "<<v.q<<" "<<v.t<<"\n";
 return v;
}

struct Window {
 Z lowN,lowD,highN,highD;
};
static Window window(const Triple& a,const Triple& b,const Z& r,const Z& scale) {
 require(a.q>0&&b.q>0&&a.t>0&&b.t>0&&scale>0,"invalid interval denominators");
 const Triple* lo=&a;const Triple* hi=&b;
 if(a.t*b.q>b.t*a.q)std::swap(lo,hi);
 return {Z(426880)*r*hi->q,scale*hi->t,
         Z(426880)*(r+1)*lo->q,scale*lo->t};
}

static void writeReceipt(std::ostream& o,unsigned digits,unsigned n,unsigned bits,
                         const Triple& a,const Triple& b,const Z& r,const Z& scale,
                         const Window& w,const Z& x) {
 o<<"schema paper9-gmp-native-coordinate-v1\n";
 o<<"formal_status source_written_unaccepted\n";
 o<<"digits "<<digits<<"\ncutoff "<<n<<"\nroot_bits "<<bits<<"\n";
 o<<"prefix "<<a.p<<" "<<a.q<<" "<<a.t<<"\n";
 o<<"next_prefix "<<b.p<<" "<<b.q<<" "<<b.t<<"\n";
 o<<"sqrt "<<r<<" "<<scale<<"\n";
 o<<"low "<<w.lowN<<" "<<w.lowD<<"\n";
 o<<"high "<<w.highN<<" "<<w.highD<<"\n";
 o<<"floor "<<x<<"\nsha "<<sha(x.get_str())<<"\n";
}

int main(int argc,char** argv) {
 try {
  if(argc<2||argc>4){
   std::cerr<<"usage: paper9_gmp_native_certificate digits [receipt-path] [trace-path]\n";
   return 2;
  }
  auto d=std::stoull(argv[1]);
  require(d<=std::numeric_limits<unsigned>::max()/16,"digits overflow");
  unsigned digits=static_cast<unsigned>(d),n=digits/14+2;
  unsigned bits=static_cast<unsigned>(std::ceil(digits*std::log2(10.0)))+64;
  Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),10,digits);
  for(;;) {
   require(n<std::numeric_limits<unsigned>::max()/6,"prefix index overflow");
   auto a=split(0,n,2);
   // Original production recurrence for the adjacent prefix: retain
   // the same compressed a, signed leaf P, and exact positive Q.
   auto leaf=split(n,n+1,2);
   Triple b{a.p*leaf.p,a.q*leaf.q,a.t*leaf.q+a.p*leaf.t};
   Z scale=Z(1)<<bits,r,radicand=10005*scale*scale;
   mpz_sqrt(r.get_mpz_t(),radicand.get_mpz_t());
   require(r*r<=radicand&&radicand<(r+1)*(r+1),"invalid strict floor sqrt");
   auto w=window(a,b,r,scale);
   require(w.lowN*w.highD<=w.highN*w.lowD,"inverted interval");
   Z x=floor_div(w.lowN*decimal,w.lowD);
   require(x*w.lowD<=w.lowN*decimal&&w.lowN*decimal<(x+1)*w.lowD,
           "invalid lower floor");
   if(w.highN*decimal<(x+1)*w.highD){
    if(argc>=3){
     std::ofstream out(argv[2]);require(bool(out),"cannot open receipt");
     writeReceipt(out,digits,n,bits,a,b,r,scale,w,x);
     require(bool(out),"receipt write failed");
    }
    if(argc==4){
     std::ofstream trace(argv[3]);require(bool(trace),"cannot open trace");
     trace<<"paper9-postorder-v1 "<<n<<"\n";
     auto t=traceSplit(0,n,2,trace);
     require(t.p==a.p&&t.q==a.q&&t.t==a.t,"trace not original source split");
     trace<<"leaf "<<n<<" "<<leaf.p<<" "<<leaf.q<<" "<<leaf.t<<"\n";
     trace<<"append "<<n<<" "<<b.p<<" "<<b.q<<" "<<b.t<<"\n";
     require(bool(trace),"trace write failed");
    }
    // No proof receipt is asserted here. Kernel acceptance is separate.
    std::cout<<"CERT digits="<<digits<<" cutoff="<<n<<" bits="<<bits
             <<" sha="<<sha(x.get_str())<<"\n";
    return 0;
   }
   unsigned dn=std::max(1u,n/16),db=std::max(32u,bits/16);
   require(n<=std::numeric_limits<unsigned>::max()-dn&&
           bits<=std::numeric_limits<unsigned>::max()-db,"retry overflow");
   n+=dn;bits+=db;
  }
 } catch(const std::exception& e){std::cerr<<e.what()<<"\n";return 1;}
}
