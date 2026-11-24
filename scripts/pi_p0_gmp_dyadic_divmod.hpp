// Standard GMP exposes separate dyadic quotient and remainder calls.
// Preserve alias safety when the input is one of the two distinct outputs.
// Both are FLOOR operations, including negative source inputs.
#pragma once
#include <gmp.h>
#include <stdexcept>
namespace paper9_gmp {
inline void fdiv_qr_2exp(mpz_ptr q,mpz_ptr r,mpz_srcptr a,mp_bitcnt_t k){
 if(q==r)throw std::invalid_argument("distinct dyadic outputs required");
 if(r==a){mpz_fdiv_q_2exp(q,a,k);mpz_fdiv_r_2exp(r,a,k);}
 else {mpz_fdiv_r_2exp(r,a,k);mpz_fdiv_q_2exp(q,a,k);}
}
}
