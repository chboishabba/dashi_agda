// Source-written receipt adapter; original production split/certify unchanged.
// g++ -O3 -std=c++17 scripts/paper9_gmp_certificate_receipt.cpp -lgmpxx -lgmp -lcrypto -o /tmp/paper9_receipt
#define main paper9_original_bench_main
#include "check_pi_gmp_quotient_residual.cpp"
#undef main
#include <limits>

int main(int argc,char**argv) {
 try {
  if(argc!=3) throw runtime_error("usage: paper9_receipt decimal_digits plain|cross");
  const auto requested=stoull(argv[1]);
  // Original leaf factors use unsigned 6*n and scale counters use unsigned.
  if(requested>100000000ULL) throw runtime_error("receipt adapter digit limit: 100000000");
  const unsigned digits=static_cast<unsigned>(requested);
  const string mode=argv[2];
  if(mode!="plain" && mode!="cross") throw runtime_error("unknown mode");
  const unsigned threshold=mode=="cross"?2:1000000000;
  const auto receipt=certify(digits,threshold,true,true);
  unsigned n=digits/14+2,bits=(unsigned)ceil(digits*log2(10.0))+64;
  for(unsigned i=1;i<receipt.profile.tries;i++){
   n+=max(1u,n/16);bits+=max(32u,bits/16);
  }
  if(n!=receipt.n) throw runtime_error("schedule mismatch");
  const Triple s=split(0,n,threshold);
  Z scale=Z(1)<<bits,r,radicand=10005*scale*scale;
  mpz_sqrt(r.get_mpz_t(),radicand.get_mpz_t());
  Z pn=Z(-24)*(2*Z(n)-1)*(6*Z(n)-5)*(6*Z(n)-1),qn=C*Z(n)*n*n;
  Z nextT=s.t*qn+s.p*pn*(A+B*n),nextQ=s.q*qn;
  Z lo=s.t,loD=s.q,hi=nextT,hiD=nextQ;
  if(lo<=0||hi<=0||loD<=0||hiD<=0) throw runtime_error("nonpositive window");
  if(hi*loD<lo*hiD){swap(lo,hi);swap(loD,hiD);}
  Z lN=Z(426880)*r*hiD,lD=scale*hi;
  Z uN=Z(426880)*(r+1)*loD,uD=scale*lo;
  Z decimal;mpz_ui_pow_ui(decimal.get_mpz_t(),10,digits);
  Z x=floor_div(lN*decimal,lD);
  Z lower=lN*decimal-x*lD,upper=(x+1)*uD-uN*decimal;
  if(!(r*r<=radicand && radicand<(r+1)*(r+1))) throw runtime_error("sqrt witness failed");
  if(!(lN*uD<=uN*lD && lower>=0 && lower<lD && upper>0))
   throw runtime_error("floor witness failed");
  if(sha(x.get_str())!=receipt.digest || x.get_str().size()!=receipt.length)
   throw runtime_error("original engine digest mismatch");
  cout<<"{\"schema\":\"paper9-gmp-window-v1\",\"mode\":\""<<mode
      <<"\",\"digits\":"<<digits<<",\"n\":"<<n<<",\"bits\":"<<bits
      <<",\"tries\":"<<receipt.profile.tries<<",\"sha256\":\""<<receipt.digest<<"\"";
  auto field=[](const char* key,const Z& v){cout<<",\""<<key<<"\":\""<<v.get_str(16)<<"\"";};
  field("p",s.p);field("q",s.q);field("t",s.t);
  field("next_t",nextT);field("next_q",nextQ);
  field("scale",scale);field("root",r);field("lower_num",lN);field("lower_den",lD);
  field("upper_num",uN);field("upper_den",uD);field("floor",x);
  field("lower_residual",lower);field("upper_residual",upper);
  cout<<"}\n";
  return 0;
 } catch(const exception& e){cerr<<e.what()<<"\n";return 1;}
}
