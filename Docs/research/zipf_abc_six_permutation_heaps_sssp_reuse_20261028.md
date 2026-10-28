# Six ABC permutations → complete Heaps information loss: SSSP source reuse

**Date:** 28 October 2026. **Scope:** DASHI Zipf-family original 27 topics / PR #1275. New construction is an adapter over pre-existing Agda owners; not a new law, duplicate S3, C6 or Monster representation.

## Original repository proof ownership (verified Git history)

These are **earlier repository-owned mathematical and compiler modules**, authored by the original repository contributor (GitHub login `chboishabba`) and **not** by this adapter:

- 1 September 2026, commit [a663a6c](https://github.com/chboishabba/dashi_agda/commit/a663a6c2a34ab5e5c52a65ddb4161c5dd3abbec3): `DASHI/Computation/SSSPThreeFrontierLinearExtensionQuotientBidiExact.agda`, six `LinearOrder3` constructors, signed 3×3 relation sheet, and `abc/acb` observation quotient.
- 1 September 2026, commit [8196d10](https://github.com/chboishabba/dashi_agda/commit/8196d1065314d3476a48232afede901e4d9cd7f1): `SSSPThreeFrontierMinimumOrbitQuotientExact.agda`, explicit minimum-only 6→3 quotient, with two tail orientations per minimum. Subsequent commit [e3993a1](https://github.com/chboishabba/dashi_agda/commit/e3993a1832f7694f0872e8d0bfdfd4ae9d89022d) strengthened its boundary.
- 1 September 2026, commit [d98933b](https://github.com/chboishabba/dashi_agda/commit/d98933be310813940366cb74c26a7626a4cd72dc): `SSSPThreeFrontierBinaryTernaryFactorExact.agda`, already proves the reversible order↔(minimum,tail) 3×2 chart and canonical minimum compatibility.

This new adapter is **source-written 28 October 2026 under Johl Brown's direction, with OpenAI ChatGPT assistance**. Earlier independent mathematics in the Heaps/Herdan, Zimmerlin–Louail–Moussallam–Barthelemy (2026, https://doi.org/10.1103/543d-frbq) and novelty-avalanche Santoro–Petri–Tria (2026, https://doi.org/10.1103/shhp-4dht) research retains original priority. The general six-element permutation group is classical. Neither the existing SSSP carrier nor its 3×2 *set chart* is identified with the cyclic group C6, Base369 HexTruth or prior **Ibrahim Monster 3B** representation. S3 is nonabelian while C6 is abelian: see https://mathweb.ucsd.edu/~atparris/small_groups.html. The user's requested Pareto/Snowball/Ibrahim rule is **reuse before extension, original owner attribution, evidence nonpromotion**.

## O/R/C/S/L/P/G/F

- **O:** Make exact the strongest finite chronology-loss example: all six unique-type ABC orderings have identical entire Heaps curves. Then advance one repeated-token step to obtain a nontrivial exact distribution.
- **R:** Import `SSSPThreeFrontierLinearExtensionQuotientBidiExact`, `SSSPThreeFrontierMinimumOrbitQuotientExact`, `SSSPThreeFrontierBinaryTernaryFactorExact`; reuse `ZipfFullHeapsCurveIdentityNoGoExact` for token histories and `ZipfNoveltyCurveInjectiveExact` for novelty flags.
- **C:** New `DASHI/Statistics/ZipfABC6OrderHeapsQuotientExact.agda` and `scripts/zipf_abc_six_order_receipt.py` with a narrow SSSP→statistics interpretation `vertexAsLetter` and `orderAsWord`. Source-owned SSSP types and round-trips are consumed; no new six-case group or predicate universe.
- **S:** Exactly one of each A, B, C gives six temporal orders `ABC ACB BAC BCA CAB CBA`. The `Hist.fullHeapsCurve` of each is exactly `(0,1,2,3)`. The terminal histogram is `(1,1,1)`. All three novelty flags are true.
- **L:** The Heaps curve quotient has ONE fibre of cardinality 6; the existing minimum-only quotient has THREE fibres each of cardinality 2; the existing reversible minimum×tail codec has SIX separate outcomes. Distinct full relation sheets distinguish all six orders. **No uniform probability claim is implicit in these counts**.
- **P:** `allSixFullHeapsCurvesCoincide`, `allSixTerminalHistogramsCoincide`, `allSixAreSameFlagCurve`, `firstMatchesSSSPMinimum`, `noFirstLabelRecoveryFromFullHeapsCurve`, `noTailRecoveryFromFullHeapsCurve`. Already owned codec theorem `Code.orderRoundTrip` and `Code.codeRoundTrip` are directly reexported.
- **G:** Even the *complete* exact novelty-event history cannot reconstruct the **first named type** if labels are erased, much less the exact six-order permutation or repeated identities. The full relation sheet still can. This strengthens H15 without claiming Hilberg, same-object Fourier phase, NS pressure or Monster 3B representation identity.
- **F:** All added Agda terms are **source-written/kernel-pending**. The new Python test module `tests/test_zipf_abc_six_order_receipt.py` is registered in `scripts/check_zipf_family_acceptance.sh`. The concrete six-order and 12-order sample spaces were **independently enumerated in local Python** using `itertools.permutations` and `Fraction`; the newly committed GitHub Python module has not been executed as part of a complete exact-head checkout. CI was not prioritized at user's instruction.

## Sharp (2,1,1) repeated-type Heaps law

Add one more A token while retaining one B and one C. The distinct chronological words number `4!/2!=12`. Under the **separately declared uniform random permutation of the fixed multiset AABC**, and only under that sampling model, the full Heaps curve distribution is:

| Full prefix diversity curve | Number of distinct source words | Exact probability |
|---|---:|---:|
| `(0,1,1,2,3)` | 2 | 1/6 |
| `(0,1,2,2,3)` | 4 | 1/3 |
| `(0,1,2,3,3)` | 6 | 1/2 |

Thus E[V_0..V_4] = `(0, 1, 11/6, 5/2, 3)`, with lower and upper *simultaneously attainable* curves `(0,1,1,2,3)` and `(0,1,2,3,3)`; the exact area gap is `(2-1)+(3-2)=2`. This reuses the existing `zipf_heaps_bridge.multiset_heaps_extremal_profiles`, `multiset_heaps_area_gap` and `expected_permutation_vocabulary` functions; no duplicate expected-vocabulary formula.

The Agda module now contains literal `aRepeatedEarly = AABC` and `aRepeatedLate = ABCA` witness words with same histogram `(2,1,1)`, extremal profiles and distinct full curves. This is a **specific H08 witness**, not a proof of the general majorization/extremal envelope for all K,N.

Sampling **IID with replacement** from masses (1/2,1/4,1/4) is a *different* random process. It does not force exactly one of each or four draws. Do not silently substitute IID expectations or draw-word probabilities for these permutation results.

## What this does not prove

This is one finite mathematical bridge from a pre-existing sorting quotient to a language discovery statistic. The SSSP owners did **not** originate the general statistical principle that the entire Heaps curve cannot identify token labels. Conversely, this adapter does **not** prove that an algorithmic SSSP frontier is a natural language corpus, that a Heaps exponent identifies syntax, that the six labels form a cyclic group, or that Zipf rank spectra recover arbitrary pressure, phases, physical triads, Hilberg exponents or Monster 3B objects.

The original 27-topic taxonomy remains unchanged and the protected ESD surfaces remain untouched. Follow-up P0 for rigorous formal certification is a compatible Agda kernel typecheck of the existing original import chain plus this adapter. Follow-up mathematical Pareto cut is to upgrade **H08** from this exact size-4 witness to all-count constructive extremal histories, and then bridge existing S23/S24 stochastic/path couplings without a duplicate probability carrier. Keep `ConcreteAddLaw` F13b unfinished until its actual nonzero-denominator rational addition proof is supplied.
