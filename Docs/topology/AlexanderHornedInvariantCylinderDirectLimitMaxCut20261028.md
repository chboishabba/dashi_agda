# Native ternary invariant-cylinder filtered direct limit: constructive algebraic closure

Date: 2026-10-28. Canonical owner [PR #1244](https://github.com/chboishabba/dashi_agda/pull/1244). Based on the CURRENT original owners **NativeBalancedTernaryEndTowerExact**, **NativeTernaryFibreActionExact**, **DepthTwoFiveOrbitFibreExact**, **EverythingTOESymmetryResolved369**. Adjacent independent [#1414](https://github.com/chboishabba/dashi_agda/pull/1414) (polynomial root monodromy/quaternion) and [#1275](https://github.com/chboishabba/dashi_agda/pull/1275) (finite Zipf/Heaps). No ESD changes, no source copied from unrelated PRs, no group/Monster/physical identification by identical numbers.

## New actual finite-to-infinite algebraic theorem interface

Let `T={−1,0,+1}`, and retain the original native prefix tower

```
X_n = C3_sector × T^n
p_n : X_(n+1) → X_n
A_n = Map(X_n,C3_phase)
H = C3_sector × C2_sign.
```

**Source-owned:** The original `Fibre.SectorSignInvariant f` and `Fibre.invariantsPullback` prove that `A_n^H → A_(n+1)^H` by precomposition preserves both exact symmetries. The original `DepthTwoFiveOrbitFibreExact` proves `A_2^H` reduces to FIVE components with cardinality `3^5=243`, **not** the whole local gauge `A_2` with `3^27` components. The optional sixth independent phase produces `3^6=729` states, which is not entailed by the five-field group itself.

**New:** `DASHI/Mathematics/Topology/AlexanderHornedInvariantCylinderDirectLimitExact.agda` is a source-written algebraic **setoid** model of the *filtered direct limit of the invariant fields*. It does **not** introduce a replacement definition of `A_n`, `H`, or their existing actions.

1. `Lift n m`: constructor-level evidence of finite chronological refinement. `liftField` composes ORIGINAL `Fibre.pullback`, and `liftInvariant` composes ORIGINAL `Fibre.invariantsPullback`. `liftEval` shows pointwise evaluation on a genuine coherent `BalancedEndPoint` survives any finite chain of refinements.
2. `commonDepth n m`: a CONSTRUCTIVE common finite stage for any two depths, not an unspecified abstract colimit operation. Its `CommonDepth` contains both explicit lift witnesses.
3. `InvariantCylinder`: a package of original finite `A_n` field and source-owned sector/sign-invariance witness; `SameOnEnds` compares its evaluations on the ORIGINAL inverse-limit coherent endpoints, not on a synthetic sample.
4. `combineCylinder`: lifts two independent representatives to one common stage, then uses ORIGINAL `Fibre.combine`. `unitCylinder` and `inverseCylinder` reuse original identity/inverse. `evaluateCombine` and `evaluateInverse` connect operations to original `C3`.
5. `combineCongruence`, `inverseCongruence`, `combineAssociativeOnEnds`, `combineLeftUnitOnEnds`, `combineRightUnitOnEnds` and both inverse laws source-write the **group object in the explicit SameOnEnds setoid**. This is not an intensional-equality theorem over Agda function types and makes no hidden use of function extensionality.
6. `overlay` a fixed finite prefix onto the source-owned all-zero suffix. `overlayDropLast` and `overlaySameLength` construct, for EVERY real finite `x∈X_n`, a coherent **actual infinite end** `extendEnd n x` whose level-n projection is exactly x (`extendEndAt`). This is the essential separation witness; no appeal to a merely hypothetical surjective projection.
7. `EventuallyEqual`: two finite invariant fields are related if some explicit common later stage has their lifted fields pointwise equal. **`eventualImpliesSameOnEnds` and `sameOnEndsImpliesEventual` establish EQUIVALENCE** of common-refinement equality and agreement on ALL coherent ends, using `extendEnd`. Thus this is the desired *algebraic direct-limit equivalence relation* and its connection to the already-defined inverse-limit underlying SET.
8. **Split injectivity:** the original `Fibre.section` (append a zero trit) induces `restrictToZeroChild`. The source-written `mapSnoc`, `zeroChildSectorSquare` and `zeroChildSignSquare` prove the retraction preserves BOTH invariance conditions; `restrictPullbackIsIdentityAt` proves `restrict∘pullback=id` pointwise, and `restrictPreservesCombine` is the exact group homomorphism theorem. This is more informative than raw injection: each refinement is a split injection of finite H-invariant C3 groups.

### Precise general rank and phase counts

Classical Burnside/orbit counting on simultaneous negation of the full n-trit word gives

```
r_n = (3^n+1)/2             -- number of H-orbits on X_n
|A_n^H| = 3^(r_n)           -- number of H-invariant field configurations
r_(n+1)-r_n = 3^n           -- NEW independent phase coordinates per step
[A_(n+1)^H : pullback(A_n^H)] = 3^(3^n)
```

The unique fixed trit word is the all-zero prefix. The other `3^n−1` words split into two-element sign orbits after the external C3 sector quotient. The source builds actual split pullbacks/restrictions, while the **closed-form all-depth orbit-count proof is not yet kernel discharged**; do not promote it based on the Python check alone.

| n | address cells | H-orbits | invariant phase fields |
|---|---:|---:|---:|
| 0 | 3 | 1 | 3 |
| 1 | 9 | 2 | 9 |
| 2 | 27 | 5 | 243 |
| 3 | 81 | 14 | 3^14 |
| 4 | 243 | 41 | 3^41 |
| 5 | 729 | 122 | 3^122 |
| 6 | 2187 | 365 | 3^365 |

**Genuine numerology/representation boundary:** The 41 H-orbits at n=4 are **not** the same thing as the unrelated 41 set-partition/RGS equality-pattern classes of length five with three labels in #1275. Both 41 results are real, but neither supplies a canonical action-compatible bijection, an empirical Zipf law, or an operator equality. By contrast, the 27→9→5 quotient followed by **Map(five orbit classes, C3)** is an actual, source-typed connection that yields 243. The 729 result requires the specified independent extra C3 mode.

### Reproducible exact finite evidence

A **local independent** integer/tuple Python oracle checked the orbit-rank formula through n=6, all 255 invariant field tables for depths n=0,1,2 against zero-child restriction after refinement, and 2,000 random deterministic cross-depth common-stage operations/evaluation cases with exact arithmetic. It passed. The committed `scripts/alexander_horned_invariant_cylinder_direct_limit_exact.py` independently defines its own canonical sign orbit representation for the finite tests and the accompanying `tests/test_alexander_horned_invariant_cylinder_direct_limit_exact.py` registers the exact group/setoid boundary. They were **committed but not executed as an exact checked-out blob** in the accessible container. The source-written Agda module was NOT compiled; no kernel verification is claimed. Do not confuse Python tuple normalization with an Agda/Lean kernel receipt.

### The remaining true topology wall

This **does pay the algebraic identification** of eventual common-depth equality with equality on all coherent infinite end addresses, and group laws in the corresponding explicit setoid.

The following two further claims are not yet paid:

- Construct a proper quotient *type* (or use the setoid category explicitly) and its topological universal property. The setoid algebra is already complete at the source-term level, but the full packaged quotient interface remains separate.
- Equip the exact inverse-limit end type with the compact zero-dimensional topology and prove **every continuous map** `K3→C3_discrete` factors through a finite address level. Once this result is kernel checked, the inclusion of finite-cylinder fields can be identified as the **entire** continuous function group `C(K3,C3)`. A map from an arbitrary infinite end space to C3 is not necessarily continuous, and arbitrary maps DO NOT factor through finite levels.

Standard source: *Stacks Project* §5.22 [Tag 08ZW, Profinite spaces](https://stacks.math.columbia.edu/tag/08ZW). David Speyer's explicit finite-cover construction on [MathOverflow 27461 (2010)](https://mathoverflow.net/questions/27461/profinite-spaces-are-the-pro-completion-of-finite-sets) is a useful explanation, not replacement for a kernel proof.

Last, the original Alexander (1924) wild sphere and Hatcher's **binary** horned group are not proved to be the user's newly chosen balanced-ternary embedded wild handlebody. The original perfect horned group cannot be given a nontrivial homomorphism into an abelian phase quotient; it must not be silently represented by `A_n^H`. PR #1414 polynomial S3/spin quaternion and original Ibrahim Monster 3B retain separate object identity and author attribution. No ESD changes, no fabricated same-object RH/NS/Spin/Monster proof.

Historical attribution: Alexander (1924); Hatcher's Algebraic Topology; Cauchy/Frobenius/Burnside orbit counting; classical directed colimits, profinite compactness, permutation-group actions. Earlier repository/source owners #1244's original `FibreAction`, `SectorSignInvariant` and `DepthTwoFiveOrbitFibreExact`; independent #1407 13/27/5/9 Fourier orbit results, #1414 polynomial/quaternion construction, #1275 Zipf-Heaps owner, original Ibrahim Monster 3B owner. The newly composed typed direct-limit algebra/ledger is Johl Brown-directed with OpenAI ChatGPT assistance, 28 Oct 2026.
