# Moonshine Primes Object

This lane documents the precise object that produces the candidate primes observed in the moonshine-primes program, along with the minimal data schema required for proof work.

## 1. Quotient map

- **Source state**: algebraic factor vectors (15-d `GL.FactorVec`) extracted from `shiftPrimeEmbedding` or equivalent Hecke scan.
- **Observable**: the quotient map collapses each factor vector to its signature/projection (e.g., `HS.Sig15`), the basin label (from `ShiftBasin`), and the eigen profile (`PHEM.EigenProfile`).
- **Purpose**: this is the filter over which candidate primes are ranked; only invariants survive.

## 2. Spectrum and basin count

- **Spectrum**: the prime-indexed compatibility bits form a 15-bit spectrum (`HS.Sig15`). Its bin counts (Earth / Spoke / Hub) are the raw signature used for eigen profiles.
- **Basin count**: the `ShiftBasin` label counts how many basin seeds lead to the same coarse signature. The moonshine program looks only at basin-aggregated signature counts to spot plateau primes.

## 3. Factorization surface

- **Factor vector**: `GL.FactorVec` holds counts of each prime factor; the candidate primes correspond to support in specific coordinates (primes 47, 59, 71 etc.).
- **Surface**: the moonshine surface is the set of factor vectors with nonzero support in those primes, together with invariants `countBool`, `sigma` norms, and `HS.Sig15` compatibility.

## 4. Eigenvalue numerator/denominator

- **Numerator**: The `PHEM.EigenProfile` deriving from `shiftSignatureEigenProfile` gives integer counts of the Earth, Spoke, and Hub contributions; these are treated as numerators.
- **Denominator**: The same profile’s total count or MDL-level (count of nonzero trits via `shiftDeltaEigenProfile`) provides the normalization denominator.
- **Claim**: prime candidates satisfy an eigen ratio (score) that stays within bounded bands; this is the spectral lens interpreting moonshine primes.

## 5. Data schema for proof

- `MoonshinePrimeState = (ShiftGeoV, HS.Sig15, PHEM.EigenProfile, ShiftBasin, GL.FactorVec)`
- Minimal schema fields:
  * `carrier` − `ShiftGeoV` from the shift bridge.
  * `sigmaSignature` − signature vector `HS.Sig15`.
  * `eigenProfile` − profile `PHEM.EigenProfile`.
  * `basinLabel` − `ShiftBasin`.
  * `factorVector` − `GL.FactorVec`.
  * `mdlLevel` − natural MDL level (count of nonzero trits).

- `MoonshinePrimeObservable = (signature, eigen, basin, factorSupport)` with precise quotient law `factorSupport` = set of primes `p` with `factorVector` component >0.

### Executable schema contract

The first implementation surface for this note is deliberately narrow:

- one lane-local schema/normalization script,
- one JSON shape for `MoonshinePrimeState`,
- one normalized output shape for `MoonshinePrimeObservable`.

The executable schema should accept:

- `carrier`
  as a list of integer coordinates,
- `signature`
  as either a 15-bit boolean vector or a prime-keyed dictionary,
- `eigenProfile`
  as `earth`, `spoke`, `hub`,
- `basinLabel`
  as a string label,
- `factorVector`
  as either a 15-entry vector or a prime-keyed dictionary,
- `mdlLevel`
  as a natural number.

And it should emit:

- normalized `factorSupport`,
- sorted support primes,
- total support weight,
- eigen numerator/denominator summary,
- and a stable quotient object ready for null-model and prime-selection tests.

Auxiliary source-specific metadata may be attached to the input payload under
separate fields such as `provenance` or `traceReport`, but the normalized
observable currently ignores those fields unless and until a documented lift
into the quotient object is added.

### Principled lift
The new `scripts/moonshine_prime_from_twined_trace_shift.py` establishes exactly that lift: it consumes the report metadata (verdict counts, shift labels, twiner comparisons) and emits a `normalizedObservable` object containing the promoted `factorSupport`, eigen ratio summary, and report-derived counts described above. That bridge ensures the normalized observable retains tension between the finite report metadata and the `MoonshinePrimeObservable` schema, so the lane can now cite concrete data-driven inputs rather than only abstract metadata.

### First real-state adapter

After the schema exists, the next grounding step is to adapt an existing
repo-native emitted state into `MoonshinePrimeState` rather than hand-writing
JSON. The canonical first source is:

- [`scripts/examples/near_miss_state.json`](../scripts/examples/near_miss_state.json)
- and the companion emitter
  [`scripts/emit_shift_prototype_examples.py`](../scripts/emit_shift_prototype_examples.py)

The adapter should:

- map the emitted `delta` vector into the `carrier` field,
- derive a prime-indexed factor vector from quantized coordinates,
- derive a boolean signature from positive prime support,
- use the emitted `mdl_level`,
- and preserve the source provenance in the emitted artifact metadata.

## 6. Claim boundary

The formal object is *not* the full Monster or full moonshine module; it is the tuple above, together with the quotient/invariant data, that provides the candidate primes. Prize claims (47,59,71) emerge by filtering:

1. restrict to `factorSupport` containing the target primes,
2. require stable eigen ratios (numerator/denominator) within the observed plateau,
3. ensure the basin count is nonzero (the coarse/resonance path produces it).

This is the lane’s proof statement: the moonshine program enumerates `MoonshinePrimeState` tuples satisfying (1)-(3) and thus motivates the listed primes as candidate invariants.
