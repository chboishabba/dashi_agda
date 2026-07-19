# RSA 15SSP factor-fibre admissibility

## Status

This tranche tests the conjecture that the fifteen supersingular-prime lanes
provide a recursively compounding admissibility geometry capable of separating
the hidden factor fibre of an RSA-style semiprime.

The current result is fail-closed:

```text
15SSP local product compatibility
  = non-separating on nonzero residue fibres

15SSP empirical residue features on unbiased toy semiprimes
  = no observed factor signal

15SSP features on intentionally constrained prime sources
  = strong structured-source signal

admitted verdict
  = structured-source detector only
```

No general RSA break, factorisation algorithm, complexity improvement, security
advisory, or production authority is claimed.

## Formal seam

For a public product `n` and a candidate nonzero residue `x` in any
multiplicative residue group, define

```text
y = x^-1 * n.
```

Then

```text
x * y = x * (x^-1 * n) = (x * x^-1) * n = 1 * n = n.
```

Therefore the predicate

```text
"does candidate x admit some local complement y with x*y = n?"
```

is true for every unit candidate. It is a product-compatibility classifier, not
a factor separator. Repeating the same predicate over fifteen SSP lanes does
not change that theorem; it produces a direct product of non-separating local
fibres.

This theorem is encoded in:

- `DASHI/Crypto/RSAFactorFibreCompatibilityCore.agda`
- `DASHI/Crypto/RSA15SSPFibreAdmissibilityBoundary.agda`
- `DASHI/Crypto/RSA15SSPFibreAdmissibilityRegression.agda`

## Benchmark design

The benchmark is evaluation-only. It does not search for factors.

For each toy semiprime `n = p*q`:

1. `p` and `q` are retained only as positive labels for AUC calculation.
2. Negative labels are independently sampled same-size primes that do not
   divide `n`.
3. Scores receive only the candidate, the public product `n`, and a public
   residue basis.
4. SSP15 is compared with a fixed non-SSP basis and a random-prime basis.
5. A separate positive-control dataset intentionally constrains generated
   primes to `1 mod 3,5,7,11`.

Forbidden search paths are absent:

- trial division;
- ordering by distance from `sqrt(n)`;
- Pollard rho;
- ECM;
- GNFS;
- a private-factor oracle in scoring;
- structured prime generation in the unbiased dataset.

## Deterministic receipt

Seed: `20260518`

Semiprime bit sizes: `32,36,40,44,48`

Trials per size: `10`

Same-size prime nonfactors per semiprime: `150`

The aggregate SSP15 results are:

| Dataset | Low-defect AUC | Structured-source AUC | Product-compatibility AUC |
|---|---:|---:|---:|
| Unbiased | 0.5580 | 0.5407 | 0.5000 |
| Structured source | 0.8998 | 0.9995 | 0.5000 |

The unbiased departures from chance are small and not a demonstrated factor
signal. Product compatibility is exactly chance-level with zero observed
variance because every nonzero candidate residue has a compatible complement.
The structured-source positive control is detected strongly, as intended.

The machine-readable decision is:

```json
{
  "unbiased_factor_signal_observed": false,
  "structured_source_signal_observed": true,
  "general_rsa_break_promoted": false,
  "verdict": "structured-source-detector-only"
}
```

## Running the benchmark

```bash
python scripts/rsa_ssp_fibre_separation_benchmark.py \
  --bits 32,36,40,44,48 \
  --trials 10 \
  --distractors 150 \
  --seed 20260518
```

Run the focused tests with:

```bash
python -m pytest -q scripts/tests/test_rsa_ssp_fibre_separation.py
```

## Promotion gate

A future factor-separation claim must discharge all of the following:

1. A signal on independently generated unbiased semiprimes.
2. Superiority to non-SSP and random-prime controls.
3. A score and candidate path independent of hidden factors and `sqrt(n)`
   ordering.
4. Scaling beyond toy sizes with explicit recovered-factor witnesses.
5. A complexity argument competitive with or better than established
   factorisation methods.
6. Independent reproduction from source, seeds, and raw receipts.

Until every gate is discharged, the formal promotion bit remains false.
