/* Four independent 14-bit residue lanes in uint64_t. No SIMD claim. */
#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#define ONES UINT64_C(0x0001000100010001)
#define GUARD UINT64_C(0x8000800080008000)
static uint64_t add(uint64_t a,uint64_t b,unsigned p){
    uint64_t s=a+b,P=ONES*p;
    uint64_t d=(s|GUARD)-P;
    uint64_t mask=((d&GUARD)>>15)*UINT64_C(0xffff);
    return (s&~mask)|((d&~GUARD)&mask);
}
static uint64_t sub(uint64_t a,uint64_t b,unsigned p){return add(a,ONES*p-b,p);}
static uint64_t mul(uint64_t a,uint64_t b,unsigned p){
    uint64_t c=0;
    for(unsigned i=0;i<14;i++){
        uint64_t mask=((b>>i)&ONES)*UINT64_C(0xffff);
        c=add(c,a&mask,p);a=add(a,a,p);
    }
    return c;
}
static uint64_t rng=41;
static unsigned next(unsigned p){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng%p;}
static void check(uint64_t a,uint64_t b,unsigned p){
    uint64_t s=add(a,b,p),d=sub(a,b,p),m=mul(a,b,p);
    for(unsigned i=0;i<4;i++){
        unsigned x=(a>>(16*i))&65535,y=(b>>(16*i))&65535;
        assert(((s>>(16*i))&65535)==(x+y)%p);
        assert(((d>>(16*i))&65535)==(x+p-y)%p);
        assert(((m>>(16*i))&65535)==(x*y)%p);
    }
}
int main(void){
    for(unsigned x=0;x<83;x++)for(unsigned y=0;y<83;y++){
        uint64_t a=x|((uint64_t)y<<16)|((uint64_t)(82-x)<<32)|((uint64_t)(82-y)<<48);
        uint64_t b=y|((uint64_t)x<<16)|((uint64_t)(82-y)<<32)|((uint64_t)(82-x)<<48);
        check(a,b,83);
    }
    for(unsigned k=0;k<100000;k++){
        uint64_t a=0,b=0;for(unsigned i=0;i<4;i++){a|=(uint64_t)next(16381)<<(16*i);b|=(uint64_t)next(16381)<<(16*i);}check(a,b,16381);
    }
    printf("PASS 6889 exhaustive pair cases at p=83, 100000 packed random cases at p=16381; 4 lanes x 3 operations each\n");
}
