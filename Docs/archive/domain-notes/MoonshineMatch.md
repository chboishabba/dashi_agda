# Moonshine-match test surface

## Scope
Docs-only note under `Docs/`. Lane 5 formulates the precise inclusion/equality tests between Dashi’s Ogg/Monster prime witnesses and the Monster prime set after Lane 4 has provided the necessary signature machinery.

## Preconditions
- Lane 4 ensures `SSP` and `Sig15` infrastructure plus `shiftPrimeEmbedding`/`shiftPipeline` are in place.
- This note only becomes legal once the prime witness pipeline is implemented so we can assert equality/subset claims.
- The carrier-level comparison is now explicit and cheap:
  `Ontology/Hecke/MoonshinePrimeCarrierMatch.agda` proves that the current
  intrinsic `SSP` carrier is exactly the canonical 15-prime
  `2,3,5,7,11,13,17,19,23,29,31,41,47,59,71` list, and
  `scripts/check_monster_prime_carrier_match.py` checks the same equality on
  the Python side.
- This does **not** identify the saturated Hecke scalar
  `forcedStableCount = 15` with the Ogg/Monster prime set; it only validates
  the 15-lane prime carrier/catalog.

## Tests and proof forms
1. **Subset test (`PRxm ⊆ MonsterPrimes`)**
   - Claim: every prime flagged in `shiftPrimeEmbedding x` belongs to the canonical Monster set `SSP`.
   - Evidence: show `shiftPrimeEmbedding` only emits nonzero counts for primes in `SSP` (already by construction). The proof form is a simple enumeration lemma that `shiftCompat` returns `true` only for `p ∈ SSP`. Document the lemma reference and mention that the implementation-level guard serves as witness.
2. **Equality test (`Sig15(x) = Monster signature` equivalence)**
   - Claim: the `HS.Sig15` produced by `shiftSignatureEigenProfile` equals the Monster signature assigned to the same `x`.
   - Evidence: needs a mapping from the canonical Monster signature (e.g., `[HS.Sig15.b2 …]` tuple) to `shiftSignatureEigenProfile`. The proof form is pointwise equality of bit counts. Provide the structural lemma and state that verifying `HS.Sig15` equality reduces to matching five blocks of three prime groups.
3. **Boundary-case (near-miss primes)**
   - Claim: primes outside `SSP` must produce zero counts; otherwise, the signature change betrays a failure mode.
   - Evidence: formulate a guard lemma that `shiftCompat` returns `false` for primes not in `SSP` and the `resonance` residual stays trivial. Record the failure-mode action (raise `resonance` mismatch) if a prime tries to flip.

## Summary
This note keeps the legal proof forms explicit: subset/equality/boundary tests on Monster primes and the required evidence references. Future proof or testing lanes can cite these statements when verifying the moonshine match. 
