/*
 * Rigorous Monster Climbing Gym zero/phase certificate producer.
 *
 * External numerical producer only; Agda remains the checker/claim authority.
 *
 * Build against FLINT/Arb, e.g.
 *   cc -O2 -std=c11 monster_climbing_gym_flint_certify.c \
 *      $(pkg-config --cflags --libs flint) -o monster_climbing_gym_flint_certify
 *
 * The program emits newline-delimited JSON.  Every interval is exported in the
 * exact Arb dyadic form
 *
 *      [lower_mantissa, upper_mantissa] * 2^two_exp.
 *
 * No decimal re-rounding is used.  A row is marked cell_unique only when the
 * complete rigorous phase ball lies strictly within a single p^a cell.
 * Boundary/straddling cases are retained as unresolved rather than rounded into
 * a cell.
 *
 * Source roles:
 *   - FLINT acb_dirichlet / Arb API: external producer semantics;
 *   - Johansson 2017, DOI 10.1109/TC.2017.2690633: Arb method;
 *   - Platt--Trudgian 2021, DOI 10.1112/blms.12460: independent rigorous
 *     zeta-zero verification context.
 *
 * None of those citations imports proof into Agda or establishes Monster
 * specificity.  The downstream Agda checker verifies only exact dyadic cell
 * containment from the emitted data.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/arb.h>
#include <flint/acb_dirichlet.h>

struct wall {
    ulong prime;
    ulong exponent;
};

/* 15 canonical Ogg primes at depth one, five non-Ogg controls, then the
   deeper p=2/3 forms from the supplied climbing-gym figure. */
static const struct wall WALLS[] = {
    {2,1},{3,1},{5,1},{7,1},{11,1},{13,1},{17,1},{19,1},{23,1},{29,1},
    {31,1},{41,1},{47,1},{59,1},{71,1},
    {37,1},{43,1},{53,1},{61,1},{67,1},
    {2,2},{2,3},{3,2}
};

static ulong ui_pow(ulong base, ulong exponent)
{
    ulong result = 1;
    for (ulong i = 0; i < exponent; i++)
        result *= base;
    return result;
}

static void print_fmpz_json_string(const fmpz_t x)
{
    char *s = fmpz_get_str(NULL, 10, x);
    printf("\"%s\"", s);
    flint_free(s);
}

static void print_exact_dyadic_interval(const arb_t x)
{
    fmpz_t lo, hi, exp;
    fmpz_init(lo); fmpz_init(hi); fmpz_init(exp);
    arb_get_interval_fmpz_2exp(lo, hi, exp, x);
    printf("{\"lower_mantissa\":"); print_fmpz_json_string(lo);
    printf(",\"upper_mantissa\":"); print_fmpz_json_string(hi);
    printf(",\"two_exp\":"); print_fmpz_json_string(exp);
    printf("}");
    fmpz_clear(lo); fmpz_clear(hi); fmpz_clear(exp);
}

/* Return 1 iff the whole ball lies in one half-open integer strip [k,k+1)
   with neither interval endpoint reaching the upper boundary.  We deliberately
   use the floors of exact outward endpoints: if the upper endpoint is exactly
   integral, the interval is treated as unresolved for strict open-cell use. */
static int unique_floor(fmpz_t floor_value, const arb_t x, slong prec)
{
    arf_t lo, hi;
    fmpz_t flo, fhi;
    arf_init(lo); arf_init(hi);
    fmpz_init(flo); fmpz_init(fhi);

    arb_get_interval_arf(lo, hi, x, prec);
    arf_get_fmpz(flo, lo, ARF_RND_FLOOR);
    arf_get_fmpz(fhi, hi, ARF_RND_FLOOR);

    int ok = (fmpz_cmp(flo, fhi) == 0);
    if (ok)
        fmpz_set(floor_value, flo);

    fmpz_clear(flo); fmpz_clear(fhi);
    arf_clear(lo); arf_clear(hi);
    return ok;
}

static void emit_row(
    ulong zero_index,
    const arb_t zero_ordinate,
    ulong prime,
    ulong exponent,
    slong prec)
{
    ulong wall_n = ui_pow(prime, exponent);

    arb_t logp, pi, two_pi, raw_phase, phase, scaled_phase;
    arb_init(logp); arb_init(pi); arb_init(two_pi);
    arb_init(raw_phase); arb_init(phase); arb_init(scaled_phase);

    fmpz_t raw_floor, cell_floor;
    fmpz_init(raw_floor); fmpz_init(cell_floor);

    arb_log_ui(logp, prime, prec);
    arb_const_pi(pi, prec);
    arb_mul_ui(two_pi, pi, 2, prec);
    arb_mul(raw_phase, zero_ordinate, logp, prec);
    arb_div(raw_phase, raw_phase, two_pi, prec);

    int frac_unique = unique_floor(raw_floor, raw_phase, prec);
    int cell_unique = 0;

    if (frac_unique) {
        arb_sub_fmpz(phase, raw_phase, raw_floor, prec);
        arb_mul_ui(scaled_phase, phase, wall_n, prec);
        cell_unique = unique_floor(cell_floor, scaled_phase, prec);
    }

    printf("{\"type\":\"phase_certificate_candidate\"");
    printf(",\"zero_index\":%lu", zero_index);
    printf(",\"prime\":%lu,\"exponent\":%lu,\"wall_n\":%lu", prime, exponent, wall_n);
    printf(",\"precision_bits\":%ld", (long) prec);
    printf(",\"zero_ordinate_interval\":");
    print_exact_dyadic_interval(zero_ordinate);
    printf(",\"fractional_strip_unique\":%s", frac_unique ? "true" : "false");

    if (frac_unique) {
        printf(",\"raw_phase_floor\":"); print_fmpz_json_string(raw_floor);
        printf(",\"phase_interval\":"); print_exact_dyadic_interval(phase);
        printf(",\"cell_unique\":%s", cell_unique ? "true" : "false");
        if (cell_unique) {
            printf(",\"cell_index\":"); print_fmpz_json_string(cell_floor);
        }
    } else {
        printf(",\"phase_interval\":null,\"cell_unique\":false");
    }

    printf("}\n");

    fmpz_clear(raw_floor); fmpz_clear(cell_floor);
    arb_clear(logp); arb_clear(pi); arb_clear(two_pi);
    arb_clear(raw_phase); arb_clear(phase); arb_clear(scaled_phase);
}

int main(int argc, char **argv)
{
    ulong count = 849;
    slong prec = 256;

    if (argc >= 2) count = strtoul(argv[1], NULL, 10);
    if (argc >= 3) prec = (slong) strtol(argv[2], NULL, 10);
    if (count == 0 || prec < 64) {
        fprintf(stderr, "usage: %s [positive-zero-count=849] [precision-bits>=64]\n", argv[0]);
        return 2;
    }

    printf("{\"type\":\"metadata\",\"schema_version\":\"1.0.0\"");
    printf(",\"producer\":\"FLINT acb_dirichlet + Arb\"");
    printf(",\"zero_method\":\"acb_dirichlet_hardy_z_zero\"");
    printf(",\"phase_formula\":\"frac(t*log(p)/(2*pi))\"");
    printf(",\"precision_bits\":%ld,\"zero_count\":%lu,\"wall_count\":%lu", (long) prec, count,
           (ulong)(sizeof(WALLS)/sizeof(WALLS[0])));
    printf(",\"external_producer_is_agda_proof\":false}\n");

    arb_t zero;
    arb_init(zero);
    fmpz_t index;
    fmpz_init(index);

    for (ulong n = 1; n <= count; n++) {
        fmpz_set_ui(index, n);
        acb_dirichlet_hardy_z_zero(zero, index, prec);
        for (ulong w = 0; w < (ulong)(sizeof(WALLS)/sizeof(WALLS[0])); w++)
            emit_row(n, zero, WALLS[w].prime, WALLS[w].exponent, prec);
    }

    fmpz_clear(index);
    arb_clear(zero);
    flint_cleanup_master();
    return 0;
}
