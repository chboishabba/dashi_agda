#include <gmp.h>
#include <cstring>
extern "C" void multiply(const unsigned char*a,size_t na,const unsigned char*b,size_t nb,unsigned char*out,size_t no){mpz_t x,y;mpz_inits(x,y,nullptr);mpz_import(x,na,-1,1,0,0,a);mpz_import(y,nb,-1,1,0,0,b);mpz_mul(x,x,y);mpz_fdiv_r_2exp(x,x,8*no);memset(out,0,no);mpz_export(out,nullptr,-1,1,0,0,x);mpz_clears(x,y,nullptr);}
