# Twin-prime / bounded-gap intake: exact reuse and remaining proof obligations

Date: 2026-10-28. Status: **finite Agda source written; no Agda kernel receipt**.

## Request and source identity

The user-supplied Veritasium transcript covers the twin-prime conjecture, Brun's sieve, Hardy–Littlewood pair heuristic, GPY weights, Zhang's smooth-modulus breakthrough, Maynard/Tao's multidimensional sieve, and Polymath8. It is **pedagogy**, not a substitute for the papers.

Primary theorem roots and distinct source ownership:

- G. H. Hardy and J. E. Littlewood, *Some Problems of 'Partitio Numerorum'; III*, Acta Mathematica 44 (1923). The prime-pair asymptotic is conjectural, not a lower bound.
- Viggo Brun, early twentieth-century sieve and almost-prime work. The Brun sieve does not prove infinite twin primes.
- D. A. Goldston, J. Pintz and C. Y. Yıldırım, *Primes in tuples I*, Annals of Mathematics 170 (2009). Small normalized gaps, not a finite absolute bound.
- Yitang Zhang, *Bounded gaps between primes*, Annals of Mathematics 179 (2014), 1121–1174, DOI [10.4007/annals.2014.179.3.7](https://doi.org/10.4007/annals.2014.179.3.7). Initial unconditional finite bound below 70,000,000.
- James Maynard, *Small gaps between primes*, Annals of Mathematics 181 (2015), 383–413, DOI [10.4007/annals.2015.181.1.7](https://doi.org/10.4007/annals.2015.181.1.7). H1 <= 600, Hm finite for every m; H1 <= 12 under Elliott–Halberstam.
- DHJ Polymath, *Variants of the Selberg sieve, and bounded intervals containing many primes*, Research in the Mathematical Sciences 1, 12 (2014), DOI [10.1186/s40687-014-0012-7](https://doi.org/10.1186/s40687-014-0012-7). H1 <= 246 unconditionally; H1 <= 6 under generalized Elliott–Halberstam.
- OpenAI, *Improved short gaps between primes*, preprint (30 August 2026), accompanying [PrimeGaps186](https://github.com/openai/PrimeGaps186). Reported H1 <= 186 via DHL[40,2] and an admissible 40-tuple of diameter 186. **Lean is conditional on three declared project axioms**: rank-three hyper-Kloosterman bound, rank-two Kloosterman correlation, and 104 outer/45 inner physical-integral inequalities plus three caps. The cited first two estimates have independent literature roots; the numerical package is checked separately. The source states self-assessed, not independent human semantic review.
- Julia Stadlmann, *Bounded gaps between primes*, preprint (31 August 2026), [arXiv:2608.31126](https://arxiv.org/abs/2608.31126). Independent H1 <= 240.
- [Axiom Math PrimeGapsLib](https://github.com/AxiomMath/PrimeGapsLib) provides substantial Lean prior art for the Maynard/Polymath8 machinery and separates theory from the finite numerical certificate. Its claims and proof status are its authors' responsibility.

The source chronology does **not** turn a conjecture into a theorem. H1 = 2, equivalently infinitely many twin-prime pairs, remains open.

## Existing DASHI source authority: use, do not duplicate

- [PR #128](https://github.com/chboishabba/dashi_agda/pull/128), merged: `DASHI.Analysis.PrimeCountingFunction`, `NatPrimeCountingInstance`, `PrimeCountingAlgorithms`, `PrimeCountingEstimateContracts`. These own finite decidable prime enumeration, exact counting, and clearly separated analytic contracts.
- `DASHI.Arithmetic.PrimeModSixSieveExact`: constructive prime >3 mod-6 dichotomy; source lineage Hardy–Wright.
- `DASHI.Arithmetic.SixWheelSieveCountExact`: finite six-residue carrier and exact survivor partition.
- `DASHI.Arithmetic.SixWheelCRTExact`: arithmetic residue map to moduli 2 and 3 and explicit excluded-class impossibility.
- `DASHI.Arithmetic.FinitePrimeProductSieveExact`: product-coordinate finite survivor counts, **not** mislabeled as full arithmetic CRT.
- Existing canonical `DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact` remains the original cross-domain governance/ownership source. No Monster 3B object or claim is changed.

No dedicated twin-prime theorem or Maynard bounded-gap machinery was located on searched current-master code paths, or in the targeted twin-prime PR search. Searches are not proof that no historical branch contains it.

## This branch: exact new scope

- `DASHI.Arithmetic.TwinPrimeSixWheelExact` defines the explicit +2 rotation of six residues.
- `shiftTwoThreeTimes` proves that applying the rotation three times returns the original residue.
- `PairWheelSurvivor` consumes *existing* CRT nonzero-residue witnesses at both offsets.
- `r5PairSurvives` and `pairSurvivorMustBeR5` prove the **finite exact** statement: a mod-6 starting residue allows both n and n+2 to avoid 2 and 3 exactly when the starting residue is 5.
- `primeAboveThreeWheelClass` reuses the prior constructive prime mod-6 result. A general arithmetic transport of `Nat` modular divisibility into `PairWheelSurvivor` is **not** established by this module.
- `TwinPrimeAt` and `TwinPrimesInfinitelyOften` are definitions/specifications, not witnesses.
- `BoundedPrimePair` counts two primes within a positive bounded shift, without asserting they are consecutive. `twinInfinitudeImpliesBoundedPairsTwo` proves an implication **from an assumed infinitude witness**. It neither creates that witness nor establishes the 186 theorem.
- `scripts/check_twin_prime_six_wheel_finite.py` verifies all six cases, repeated finite blocks, bounded twin pairs, and a concrete survivor that is composite (35). Exact integer computations do not establish infinitude.

This is intentionally an elementary finite sieve rather than an uncredited port of Lean or a synthetic analytic proof.

## Max-cut / Pareto / snowball / Ibrahim proof frontier

| Priority | Exact obligation | Existing source / reuse | Promotion gate |
|---|---|---|---|
| P0 | Prove finite +2 CRT pair classification | SixWheelCRTExact; SixWheelSieveCountExact | Type-check new Agda module |
| P1 | Connect `Nat` modulus to wheel and prime >3 | PrimeModSixSieveExact; NatPrimeCountingInstance | Actual transport theorem, not finite examples |
| P2 | Finite admissible k-tuples and CRT local-factor products | FinitePrimeProductSieveExact plus real CRT arithmetic | All-prime quantified admissibility and tuple certificate |
| P3 | Weighted >1 overlap lemma with nonnegative weights | PrimeCountingAlgorithms finite sums | Exact lemma and objective normalization |
| P4 | Bombieri–Vinogradov and distribution in progressions | PrimeCountingAnalyticBridge (contract only), AxiomMath prior art | Source theorem plus faithful Agda translation |
| P5 | Maynard/Polymath sieve, large-moduli refinements | AxiomMath PrimeGapsLib; OpenAI PrimeGaps186 | Recheck assumptions, dependence graph, parameter calculus, numerical certificate |
| P6 | Bridge two-prime k-tuple occurrence to bounded **consecutive** gap | explicit admissible tuple + bounded interval | Syntactically exact theorem; kernel receipt |

**Cut rule:** do not attempt P4–P6 by inventing generic postulates and presenting conditional corollaries as unconditional theorems. The finite sieve's ~1/6 survivor density is not a twin-prime density and supplies no infinite lower bound. In particular, 35 and 37 pass the mod-6 screen but 35 is composite.

**Attribution rule:** distinguish original historical mathematics, inherited Agda theorem ownership, source-written Agda, executed Python, externally published Lean with axioms, and this repository's kernel verification. Original 2026 claimed 186 bound belongs to OpenAI / GPT-6 Astra and cited mathematical predecessors, not DASHI. Keep the repository's Ibrahim Monster 3B claims in their original ownership lane. No numerical, spectral, moonshine, or Monster fingerprint is evidence for a same-object prime representation.

## Evidence and validation

- Local exact Python run on 2026-10-28: six/six wheel cases, five block sizes, 1,223 twin-pair starting positions in 4..100000, and composite survivor 35: **passed**. No random inputs.
- New Agda source was written through GitHub connector and should be checked using the pinned repository Agda toolchain. **Agda type-check not executed in this environment**.
- The new module is imported into the arithmetic aggregator and all three canonical TOE roots. No ESD surface, upstream theorem owner, or independent Lean file is edited.
- External 186 Lean checks and physical-integral computations were **not rerun**. Do not transfer their check status to this Agda branch.

Run on a checkout of this branch:

```sh
python3 scripts/check_twin_prime_six_wheel_finite.py
agda -i . -i <YOUR_PINNED_STANDARD_LIBRARY_PATH> DASHI/Arithmetic/TwinPrimeSixWheelExact.agda
```

The second command is illustrative: use the repository's pinned preflight/CI setup for the actual Agda invocation. A syntax/preflight check or Python success does not replace the Agda kernel.
