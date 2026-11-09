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
