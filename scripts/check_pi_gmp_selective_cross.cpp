// Selective cross-GCD sweep on the original quotient residual backend.
// Compile from repository checkout; no alteration of original certificate.
#define main original_quotient_main
#include "check_pi_gmp_quotient_residual.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=3){cerr<<"usage: selective digits threshold\n";return 2;}
 unsigned d=stoul(argv[1]),t=stoul(argv[2]);
 if(t<2)return 2;
 auto r=certify(d,t,true,true);
 cout<<fixed<<setprecision(3)<<"digits="<<d<<" threshold="<<t
 <<" total="<<r.profile.total<<" split="<<r.profile.split
 <<" div="<<r.profile.divisions<<" bits="<<r.profile.bits
 <<" attempts="<<r.profile.tries<<" sha="<<r.digest<<"\n";
 return 0;
}
