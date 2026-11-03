# Native blocked SU(2) R445 + correlated TSVF P01 — exact max-cut, 3 November 2026

## Scope and provenance

The current downstream Lorentz/TSVF/KK [PR #1460](https://github.com/chboishabba/dashi_agda/pull/1460) is based on but **not identical to** the actively developing YM [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). This tranche selectively synchronizes six actual YM owner files from #1444 at `5e81c4f5bd5041fc7fa6259b915a6f2ce0c42261`, plus its exact 219-field inventory, exact-lemma ledger and reference scripts. All source donors retain original credit and unchanged source contents. This is **not** a full branch merge, a transitive --safe repair or a Clay theorem.

**Original physics/mathematics**: Wilson; Bałaban; compact-group Haar; Osterwalder–Schrader; Aharonov–Bergmann–Lebowitz; Aharonov/Vaidman; Aharonov–Cohen–Landsberger (2017). New code consumes the original DASHI SU(2) rational quaternion group laws, periodic predecessor/successor theorem, signed-path gauge cancellation, native bond enumeration and blocked bond codec; it does **not** rename those theorems as newly discovered.

## New original-source mathematical join

[YMClayNativeBlockedSU2PathHolonomyGaugeExact.agda](../../DASHI/Physics/YangMills/YMClayNativeBlockedSU2PathHolonomyGaugeExact.agda) closes the following *finite* composition:

```text
Original positive-bond SU(2) link field + source site-gauge function
  -> existing constructed positive/negative oriented-link gauge proof
  -> original signed path holonomy with L actual fine axial steps
  -> exact native cyclic torus <-> Fin blocked-coordinate transport
  -> actual SU(2)-valued blocked path link
  -> same original pathSiteGaugeCancellation theorem
  -> blocked gauge covariance at reblocked walked endpoint
```

Precise hypothesis: the original path group owner uses side `suc n`, the Bałaban block codec uses `M*L`. The input equality `suc n ≡ M*L` is **the physically necessary size identification**, not an arbitrary second lattice. The generic source theorem `nativeBlockedPathGaugeCovariant` is instantiated with the original, fully constructed rational SU(2) exact group and the existing original `PeriodicStepInverseLaws` to obtain `rationalSU2BlockedPathGaugeCovariant`. A separate `nativeBlockedOneStepExactlyOriginal` checks L=1 returns precisely the source-native positive bond.

**IMPORTANT**: A true physical coarse neighbour for arbitrary offset needs a further theorem identifying the computed reblocked walked endpoint with the canonical coarse-axis step; an L-step path and a gauge-covariant endpoint alone do not establish Wilson-action blocking, reflection positivity, Haar disintegration or RG compatibility. The source remains **non-Golden** because some historical path/geometry imports do not provide audited transitive `--safe`. Source-written means GitHub file readback, not compiler acceptance.

## P01 correlated-state / independence falsifier

[TSVF2017CorrelatedEnvironmentMarginalNoGoExact.agda](../../DASHI/Quantum/TSVF2017CorrelatedEnvironmentMarginalNoGoExact.agda) is a new Golden `--safe` *source-written* finite theorem using the original rational-complex carrier. In the standard `|00>,|01>,|10>,|11>` basis let `B_+ = |00>+|11>`, `B_- = |00>-|11>`. Both have raw norm square 2, both *complete* one-site reduced-density matrices equal `I` at both sites, but their global Hermitian inner product and Born overlap vanish. With common normalization, each local reduced density is `I/2`, while the global states remain orthogonal. `noLocalMarginalDecoder` proves no deterministic reconstruction of both global vectors from their common pair of complete reduced matrices.

This prevents promoting the heterogeneous independent-site formula to correlated environments on the basis of *marginal evidence alone*. It does not contradict the earlier tensor-product theorem, which is correct for actual product records; instead it makes the missing hypothesis mathematically testable. Physical 2017 apparatus dynamics and correlations remain open.

## Independent exact reference and negative controls

[check_ym_blocked_su2_tsvf_bell_maxcut.py](../../scripts/check_ym_blocked_su2_tsvf_bell_maxcut.py) was committed. An equivalent **executed local Python implementation** passed **11,784** exact Q8 (a noncommutative finite subgroup of SU(2)) positive-bond checks across `(M,L) = (1,1),(2,1),(1,3),(2,2),(2,3),(3,2)`, covering native block/unblock, L-step holonomy, transformed-link cancellation, correct coarse coordinate and offset, all one-step L=1 identities, and an explicit noncommutative wrong-order counterexample `ij=k` versus `ji=-k`. The Bell full-marginal/globally-orthogonal fixture passed with exact fractions. **The committed script itself has not been run through a checkout**, nor is Q8 testing a continuous Haar proof.

## Exact remaining max-cut by original lemma ID

| Gate | Source-paid in this tranche | Still literally open |
|---|---|---|
| P00.L02--04 | Six #1444 source files and current exact 219 inventory+ledger copied, all provenance pinned | Full conflict-aware branch reconciliation and exact-head/transitive Agda check |
| P01.L13 | Finite complete-local-density/no-global-decoder counterexample | Actual many-body source, product/correlation error theorem and final state |
| P01.L14--16 | Existing original-ABL finite theorem plus new rigorous factorization limitation | Actual physical gamma amplitudes, postselection, uniform robustness |
| P05.L03--05 (R443.F01--F07) | Native finite cyclic/Fin and function/Vec reindexing synced; C3 conditional one-vector reduction reused | Concrete adjacent-swap program/canonical label equality; physical compact Haar and CMP119 |
| P06.L01--02 (R445.F02/F03/P01/P02) | Native M*L site/bond bridge, *constructed* original SU(2) ordered L-step blocking + derived gauge covariance | Native coarse-endpoint identity, gauge-covariant coarse plaquette/Wilson-action map, physical RG kernel/disintegration and cutoff estimates |
| P06.L05--18 / R320 / R333 | No physical analytic theorem completed here | Uniform physical tails/marked-J decay, OS source/limit and positive same-H spectral gap/H6 |
| P07.L01--08,L15--16 | Existing conditional finite OS-clock commuting retains its original owner | Physical strongly continuous unitary and self-adjoint generator-domain/spectral equivalence |
| P08--P11 | Earlier 5D/KK/3+1/gravity steelman unchanged | Literal 5D action/reduction, same metric/stress, physical comparisons, terminal acceptance |

**219-field inventory is an inventory, NOT 219 discharged lemmas**; Clay has a distinct independent endpoint, research-cut A--D, and R443/R445/R320/R333 producer dependency gates. None is automatically solved by the finite SU(2) computation.

## Trust record

- GitHub source copies and new files: source-written, with precise donor commit; no evidence of Agda kernel acceptance.
- New `TSVF2017CorrelatedEnvironmentMarginalNoGoExact.agda`: declares Golden `--safe` and contains no local postulates or bypass pragmas.
- New blocked SU(2) source: intentionally omits Golden `--safe` due to older dependency chain; still no new local postulate.
- Exact reference script: independent computation; not a proof of real Haar, RG, OS, or Clay.
- Physically populated R443/R445/R320/R333/H6: **OPEN**.
- Selected-observer same-H and emergent (3,1)/KK: **OPEN**.

**Next maximal dependency cut**: prove the literal coarse endpoint/path transport at every M,L and transport the same native SU(2) Wilson plaquette into a reflection-compatible blocked observable; then join to the real one-link compact Haar/test algebra, R124/CMP119 beta/counterterms and true blocked probability kernel. In parallel, turn the product-vs-correlated Bell falsifier into an exact physical environment-correlation bound for the chosen 2017 pointer dynamics, and construct P07 physical Stone/OS equivalence.
