#include <gmpxx.h>
#include <iostream>
#include <vector>
#include <string>
int main(){
 size_t n; if(!(std::cin>>n)||n==0)return 2;
 std::vector<mpz_class> h(n),l(n);std::string s;
 for(auto &v:h){if(!(std::cin>>s)||v.set_str(s,16)!=0)return 3;}
 if(h[0]!=1)return 4;
 for(size_t k=1;k<n;++k){l[k]=h[k]*k;for(size_t i=1;i<k;++i)if(h[i]!=0)mpz_submul(l[k].get_mpz_t(),h[i].get_mpz_t(),l[k-i].get_mpz_t());}
 // Independent scatter accumulation of H*L against Euler derivative.
 std::vector<mpz_class> r(n);
 for(size_t i=0;i<n;++i)if(h[i]!=0)for(size_t j=0;j<n-i;++j)if(l[j]!=0)mpz_addmul(r[i+j].get_mpz_t(),h[i].get_mpz_t(),l[j].get_mpz_t());
 for(size_t k=0;k<n;++k)if(r[k]!=h[k]*k)return 5;
 for(auto &v:l)std::cout<<v.get_str(16)<<'\n';
}
