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

**Genuine cross-PR refinement:** A later explicit anchored-normalization transport (see the next section) proves that the **orbit sets** T^(n+1)/global-value-S3 and T^n/simultaneous-sign-C2 are equivalent. Thus the equal counts 5,14,41,122,365 have a canonical explanation after choosing the first token as anchor. This does **not** equate the raw sequence and address carriers, their measures, the wild-exterior fundamental group, or the local gauge and full S3 group actions. The independent sixth C3 phase needed for 729 is unchanged.

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


## Subsequent alpha cut: the `41=41` match DOES have an action-level transport

Previous documentation described the equality of the two 41-count sequences as a bare coincidence. This was too weak. A **specific orbit-set isomorphism** is now constructed by the new source-written `AlexanderHornedS3WordSignOrbitTransportExact.agda` and its exhaustive independent Python oracle:

```
global value-S3 orbits on words of n+1 trit symbols
    -> fix first symbol as anchor by a global C3 translation
relative n trits (second-first, third-first, ...)
    -> quotient by the residual reflection C2
simultaneous sign orbits on n trit coordinates
```

Concretely, for `w=(a0,a1,...,an)`, normalize to differences `δ_i=a_i−a0 mod3`. Every global translation `a_i↦a_i+t` leaves all `δ_i` unchanged. Reflection `a_i↦−a_i` sends all `δ_i↦−δ_i`. Conversely, if the relative coordinates of two named words agree up to a common sign `s=±1`, choose `t=b0−s*a0`; the affine permutation `a_i↦s*a_i+t` sends the entire first word to the second. For three labels, **these six affine transformations are precisely the original S3 value permutations**. This is an honest two-way orbit transport, not a same-count identity.

The new Agda source explicitly imports the prior #1244 signed-trit↔C3 phase chart. It provides `normalise`, `normaliseTranslate`, `normaliseReflection`, `signedRelativeTranslationInvariant`, `signedRelativeReflection`, a canonical anchored `wordFromDifferences`, `signedRelativeSection`, and `normaliseViaTranslation`. The Python check exhaustively compared restricted-growth equality-pattern representatives and actual sign-orbit representatives for **9,840** named words through length eight, and verified all **59,040** S3 actions, with no mismatches. This is source-written/independent finite evidence, **not Agda kernel verification**.

Therefore the classical identity is structural:

```
r_n = # (T^n / C2_sign)
    = # (T^(n+1) / S3_value)
    = Σ_(k=1..min(3,n+1)) S(n+1,k)
    = (3^n+1)/2.
```

This genuinely cross-pollinates #1244's invariant phase-field ORBIT DOMAIN with #1275's equality-pattern ORBIT DOMAIN. It does **not** identify the corresponding probability laws: uniform named words induce nonuniform orbit masses (different orbit sizes), and an IID nonuniform Zipf measure is not invariant under arbitrary value-S3 relabeling. It also does not equate `C3^5` local invariant fields with the five-pattern set itself, or the #1414 `5^3` modes.

Earlier original SSSP permutations/ZIPF-Heaps, Hatcher/Alexander, #1407 Fourier and #1414 monodromy/quaternion ownership retain distinct proof provenance; any future operator transport must declare the relevant functor and source action.


## Further Pareto consumer: source-owned five-orbit wave operators on named words

The native original `AlexanderHornedFiveOrbitWaveOperatorExact.agda` already owns **five genuinely different wave operators** indexed by the actual #1244 H-orbit carrier `Five.FiveOrbit`; its `inflateEvolutionSquare` proves operator/field evolution on 27 addresses reduces pointwise to the five orbit entries. The independent physical `ShiftDiscreteWaveStep` and the original #1405 Sonic Warfare wave-transport work retain distinct mathematical ownership.

New `AlexanderHornedFiveOrbitNamedWordWaveTransportExact.agda` reuses that five-orbit operator type, **and** the actual newly proved anchored S3/C2 word normalizer. It derives an actual named-word-to-five-orbit chart, with the five explicit source-readable constructors:

| Global S3 named equality pattern | Normalized signed n=2 relative coordinates | Canonical original FiveOrbit |
|---|---|---|
| AAA | (0,0) | origin |
| AAB | (0,+) | axisSecond |
| ABA | (+,0) | axisFirst |
| ABB | (+,+) | diagonal |
| ABC | (+,−) | antiDiagonal |

The Agda module source-writes all five `refl` slot witnesses, a translated-word `wordOrbitTranslationInvariant`, a reflected-word `wordOrbitReflectionInvariant`, and two actual operator/field evolution invariance lemmas under global value-S3. Its `namedEvolutionFactor` is a commuting equation between **the ORIGINAL five-orbit operator** and named-word evaluation through the **actual quotient map**. No new wave ontology or source operator type is constructed.

Its independent local integer-mod-three Python check processed ALL 243 five-orbit field assignments, 27 three-token named words and six affine global S3 transformations, namely **39,366** exact operator/equality cases, using *five deliberately heterogeneous* affine orbit-dependent operators. The committed `scripts/alexander_horned_five_orbit_named_wave_transport_exact.py` and focused test are replayable. **This is source-written and finite computational evidence, not Agda-verified nor experimental acoustics.**

This is a legitimate consumer of the 27→5 invariant address orbit geometry and #1275 equality-pattern *observation* map. The operator's input remains a finite five-orbit wave-value field. Statistical word probabilities, time-ordered Heaps novelty, original Alexander–Hatcher wild π₁, #1414 polynomial root monodromy/quaternion spin, #1407 signed Fourier convolution, #1405 measured sound propagation and original Ibrahim Monster 3B all require distinct typed transports. No same-object proof follows from the orbit-domain correspondence alone.
