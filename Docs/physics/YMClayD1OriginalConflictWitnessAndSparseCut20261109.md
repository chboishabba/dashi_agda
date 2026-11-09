# D1 finite conflict witness: exact native owner and remaining physical cut

2026-11-09. Source: `YMClayD1OriginalPlaquetteSupportDecisionExact` and `YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact`.

## Implemented source declarations

`YMClayD1OriginalConflictPlaquetteWitnessExact.agda` gives:
- `sharedOrDisjointOn`: exhaustive constructive decision on the complete original link-star list, returning either a concrete common plaquette or an actual disjointness proof.
- `originalConflictExhibitsSharedPlaquette`: converts the negative conflict emitted by the original greedy-maximality code into a positive, native shared plaquette.
- `originalSharedPlaquetteHasBothNativeBonds`: uses the established original incidence soundness to produce membership certificates for both native positive link variables in the actual source plaquette's four-link boundary.
- `originalNegativeConflictHasLiteralFourBondWitness`: combined finite certificate, with no postulates.

This is a stronger finite witness than merely counting links or asserting `¬ disjoint`. It supplies the actual source plaquette needed to charge conflicts or define local contour adjacency. It does **not** establish the number of distinct neighbours (18) or perform Haar disintegration. No native Agda compiler was available for an exact-head check in this session; commit/readback is not kernel acceptance.

## Quantitative original-Wilson D1 remaining cut

1. **D1-GEO-18** — For original 4D periodic link stars on side ≥3, prove the six actual incident plaquettes and an at-most-18 bound on distinct conflicting positive links. Degenerate small tori must be handled without silently assuming the geometric degree.
2. **D1-GEO-19** — Convert the source-native greedy maximality and D1-GEO-18 into `19 * length(selected) ≥ length(marked)` for distinct marked links, taking care of duplicates and counting witnesses.
3. **D1-HAAR-T** — Source-specific finite Fubini/disintegration and conditional factorization for conflict-free sets on the full original Wilson measure, using exact signed plaquette words.
4. **D1-FRU-SPARSE** — Cutoff/volume-uniform joint estimate for specified sparse **frustrated** supports. A total energy/density large-deviation bound cannot substitute for it.
5. **D1-MIXED** — A source-true decomposition of mixed coherent/frustrated contours with entropy-correct activities at fixed physical scale, leading to the original covariance bound, not to a surrogate law.
6. **E1-CONV / D2-OS / N1-SCALE / G1-ALL** — Continue independent physical gates: interacting \(\mathbb R^4\) limit, the same reconstructed OS Hamiltonian and full spectral sector, surviving fixed-support renormalized observables, all compact simple groups.

## Gate discipline

No Clay continuum theorem or full Wilson covariance decay is claimed. In particular, neither an original six-star incidence witness nor the original coherent-only polymer tail can infer sparse frustrated contour suppression. The finite witness theorem is a reusable producer, not the physical estimate.


## 2026-11-09 continuation: quantified finite precursor and actual greedy witness

The existing original link-star greedy maximality theorem has now been composed with its **actual** source plaquette-conflict witness:

- `OriginalLiteralGreedyCoverage` is a proof-relevant statement about every marked original positive bond.
- `originalGreedyMaximalityHasNativePlaquetteCoverage` produces either membership in the selected conflict-free greedy set or (i) a selected original positive bond and (ii) an original four-bond plaquette containing **both** the selected link and marked link.
- The theorem has no new analytic source or postulate: it consumes `greedyOriginalDisjointStarsMaximal` and `originalNegativeConflictHasLiteralFourBondWitness`.

Independent executable regression `scripts/check_ym_original_star_6_18_19.py` passed on L=3,4,5 torus carriers, with (links,plaquettes,max conflict degree) equal to (324,486,18), (1024,1536,18), (2500,3750,18). Each original positive link had six incident plaquettes, and 16 test marked lists per volume satisfied the 19-packing, maximality and independence assertions. This checks the intended finite combinatorics, not a native Agda cardinal bound.

**Precise remaining finite Agda proof:** `originalNativeConflictDegreeAtMost18` and its list-cardinality corollary `originalGreedy19Packing`, with distinct-marked/no-duplicate input. The independent regression does not discharge these declarations.

**Decisive physical leaf unchanged:** source-proved original R445/CMP116 `chargeSumBelowPhysicalRootedShell`, for actual cutoff-uniform sparse frustrated/mixed activities. The mathematical source field is present in `BalabanLiteralTwoWilsonCMP116ConnectingTailExact`; it must be inhabited, not repeated under a different name. Subsequent physical obligations are selected UV/IR continuum convergence, same-family OS reconstruction and spectral decay, observable noncollapse, and all compact simple groups.

**Verification:** GitHub contents write/readback only for the new Agda declaration. Agda 2.9 was not installed in this execution container, so kernel acceptance and a transitive safe import check are not claimed.


## 2026-11-09 native list-cardinality continuation (precise non-promotion)

`YMClayD1OriginalGreedy19CountingExact.agda` is source-written and imported by `YMClayOriginalWilsonPhysicalRegression.agda`.

Concrete declarations:
- `DistinctMarked`: recursive proof that no original positive bond occurs twice in the marked list.
- `filterOriginalStarFreePreservesDistinct` and `filterOriginalStarFreeKeepsSelectedHeadDistinct`: the literal original conflict-free filter preserves the correct nonduplicate premise.
- `nineteenTimes`: primitive recursive cardinality coefficient, not a chosen phantom bound.
- `originalGreedy19PackingFromNativeDegree18`: **actual Agda proof expression** of
  `length marked ≤ nineteenTimes (length (greedyOriginalDisjointStars marked))`
  for every distinct original marked-link list, derived inductively using
  `Data.Nat.Properties.≤-trans`, `+-mono-≤`, and `s≤s`.

The geometry leaf is transparently a field of `OriginalStar18RemovalBound`:
`originalDistinctStarRemovalBound : length as ≤ 18 + length (filterOriginalStarFree a as)`,
for `DistinctMarked (a ∷ as)`. No instance is manufactured. The degree proof must use the **actual** plaquette-star incidence, not a generic graph with degree chosen as a parameter.

Status split: greedy arithmetic and duplicate preservation **source-written, kernel verification pending**; literal degree-18 removal field **uninhabited**. All physical D1, E1, D2, N1, G1 analytic obligations remain open; no Yang--Mills Clay closure claimed.
