# Native balanced-ternary local C3 gauge: finite action, pullback, and true limit boundary

**Date:** 2026-10-28. **Canonical source/code owner:** [Alexander horned native ternary #1244](https://github.com/chboishabba/dashi_agda/pull/1244). **Neighbor original owners:** [#1414](https://github.com/chboishabba/dashi_agda/pull/1414) polynomial monodromy and quaternion; [#1275](https://github.com/chboishabba/dashi_agda/pull/1275) full Heaps / value-S3 observation; [#1407](https://github.com/chboishabba/dashi_agda/pull/1407) signed Fourier 27×729. **No shared object is inferred from a shared cardinality.** No protected ESD edits. Source-written Agda has **not** been kernel checked.

## Original historical and prior repository ownership

- Original **J. W. Alexander (1924)** wild horned sphere and **Allen Hatcher, Algebraic Topology, Example 2B.2** BINARY horn construction are not modified or promoted into a native ternary wild embedding by this work.
- Classical finite product groups, semidirect products and permutation wreath products. Sources include **M. Krasner and L. Kaloujnine, 1950–1951**, *Produit complet des groupes de permutations et problème d’extension de groupes* I/II (Acta Sci. Math. Szeged), and the Encyclopedia of Mathematics “Wreath product”: https://encyclopediaofmath.org/wiki/Wreath_product ; they retain group-theory priority.
- Original repository **FiniteC3OrbitStabilizerExact.C3** and its multiplication/inverse/group theorems, **BalancedTernary.Trit**, **RecursiveFibreTower.FibreTower/InverseLimitPoint**, and #1244's prior **AlexanderHornedNativeBalancedTernaryEndTowerExact** and balanced projection/sector rotation are imported and reused unchanged. Earlier #1254 binary prefix code, #1414 original polynomial S3/C3 and spin, #1275 finite equality-pattern/Heaps proof, and independent original **Ibrahim Monster 3B** representation ownership remain independent.
- The following *specific composition* is source-written by Johl Brown direction with OpenAI ChatGPT assistance, 28 October 2026. The classical theorem is not claimed to be newly discovered. Source code/test checks are not Agda kernel receipts.

## Actual finite carriers and types (no number welding)

For balanced trits `T={−1,0,+1}`, reuse the existing address system

```
X_n = C3_sector × T^n
p_n : X_(n+1) → X_n              -- original drop-last map
G_n = X_n → C3_phase             -- actual local phase field functions
```

The original #1244 module `AlexanderHornedNativeTernaryFibreActionExact.agda` **already owns** `FibreAction = Map(X_n,C3)`, pointwise `combine`, `act`, `inverseAction`, `pullback`, `pullbackInjective`, `transitiveAction`, and the inverse-limit `LocalFibreAction/evalLocal`. The new module **imports and reuses those exact definitions**, adding only an explicit trit↔C3 chart, a true semidirect product, cylinder setoid laws and an invariant-observation no-go. This avoids a duplicate local-gauge group or inverse-limit carrier.

There are `|X_n|=3^(n+1)` finite clopen cylinders. Classical finite function counting gives `|G_n|=3^(3^(n+1))`. At depth 2, `|X_2|=27`, `|G_2|=3^27=7,625,597,484,987`. The exact source already owns `Native.ternaryConfigurationTetration` and proves the numerical identification `3^27=3↑↑3`. **The 27 address cells are not 27 time samples, 27 Fourier modes, 27 physical horns or 27 Monster dimensions.** Any such identification needs a typed map and its desired invariance property.

## Exact finite pullback / section / injection theorem

Original `balancedProjection` sends a prefix (sector, trit-vector including one new digit) to its chronological parent. Its induced phase pullback is

```
p_n^*(f)(x) = f(p_n(x)).
```

The original owner already source-writes `pullbackMultiplication` and `pullbackInverse`; the extension imports those without copying them, and adds `refineRotationSquare` and twisted-product equivariance.

More strongly, the original `End.snoc` and `dropLastSnoc` already construct a section `section_n(x)=(sector, prefix++[0])` with `p_n(section_n(x))=x`; the ORIGINAL owner proves it in `sectionProjection`. Consequently

```
(∀y ∈ X_(n+1), p_n^* f(y) = p_n^* g(y))
    ⇒ (∀x ∈ X_n, f(x)=g(x)).
```

This is exactly the EXISTING source-written `Fibre.pullbackInjective`. The new extension reuses that theorem; it does not claim its original proof ownership. It does not require function extensionality, an infinite compactness principle, or a count coincidence. Injectivity here is in the **pointwise function-setoid**.

## External sector rotation and real finite semidirect action

The user distinguishes two C3 operations:
1. The external C3 rotates the three root SECTORS of the address and leaves all internal trits fixed.
2. The independent `G_n` rotates the PHASE at each address without moving the address.

Define `R_a^{-1}(sector,prefix)=(sector−a,prefix)`, acting on fields by pullback `(a·f)(x)=f(R_a^{-1}(x))`. The new source proves `shiftAddressCompose` (27 explicit sector-action table clauses), `shiftFieldComposeAt`, `shiftFieldAddAt`, and the exact pullback-equivariance square `refineRotationSquare`:

```
p_n^*(a·f) = a·(p_n^* f)   -- pointwise on every finer address.
```

The `TwistedPhase(n)` record uses the original C3 and existing phase function:

```
(f,a)·(g,b) = (f + (a·g), a+b).
```

It has source-written componentwise unit, associativity and inverse terms including `twistedAssociativeGaugeAt`, `twistedInverseLeftGaugeAt`, `twistedInverseRightGaugeAt`, `twistedInverseLeftSector` and `twistedInverseRightSector`. Refinement respects the twisted multiplication (`refineTwistedGaugeHomomorphismAt`) and sector component.

This gives a correct **finite semidirect group law** `G_n⋊C3` at source-term level and independently tested finite arithmetic. At n=2, classical finite function counting gives `|G_2⋊C3|=3^28=22,876,792,454,961`. It is a *permutation wreath-product-type* action. It is **NOT** the wild-exterior geometric orbifold group `(G_A*G_A*G_A)⋊C3`; the two carriers and their actions are different.

## Inverse-limit cylinder field — actual positive lemma and remaining topology wall

The ORIGINAL #1244 owner provides `LocalFibreAction`, `evalLocal`, and `refinementEvaluation` on the existing inverse-limit endpoints. The new extension uses those exact carriers, adds `shiftEnd` (a coherent inverse sector-shift of an end) and `evalRotationSquare` (cylinder-value equivariance), without making a second `CylinderPhase` or equality-on-function assumption.

More, `SameOnEnds` is the **pointwise equivalence relation** on cylinder representatives induced by all coherent infinite ends. Its reflexive/symmetric/transitive lemmas, one-step refinement invariance and sector-rotation congruence are source-written. This supplies the quotient's **setoid equality interface**; it does *not* pretend to have constructed a higher-inductive quotient type or a full topological compactness theorem.

A complete abstract identification

```
colim_n Map(X_n,C3)  ≅  C_loc(K3,C3)
```

still requires **(a)** quotienting representatives by an appropriate eventual-equivalence relation and proving the group law well-defined at common refinement, **(b)** equivalence of that relation with equality on all ends, and **(c)** defining topology on the inverse-limit end space and showing every continuous map to finite-discrete C3 factors through a single finite clopen cylinder partition. This final surjectivity uses classical compactness plus zero-dimensionality but is **not kernel discharged** here.

## Strong actual information-loss/no-weld consequence

For any two local fields `f,h:X_n→C3`, the **ORIGINAL** `Fibre.difference` and `Fibre.transitiveAction` prove `Fibre.act (Fibre.difference f h) f(x)=h(x)` at every address. The extension then proves **any pointwise-extensional observable invariant under the FULL local `G_n` action is constant** in `gaugeInvariantObservableConstant`. Its observation-extensionality hypothesis is explicit; the original transitivity proof retains ownership.

This is the precise cross-pollination with #1275's five-equality-pattern and four-Heaps observations: they are invariant under a *global diagonal* relabeling `S3` (and hence C3), but **not** under an arbitrary local translation. For three root-sector positions, `f=(0,0,0)` has Heaps prefix counts `(0,1,1,1)`. A local phase change `g=(0,1,0)` gives `(0,1,2,2)`; global addition of a single constant preserves the first curve. Thus local gauge observables cannot be confused with the previously proved original symmetry quotient. The choice to interpret three sector values as chronological observations is an explicit **statistical chart**, not intrinsic geometry.

## Executed finite oracle and verification ceiling

- A local, mathematically equivalent Python oracle independently checked the finite (X_n) and all external sector actions; **1,080 exact shift-composition cases** at depths 0–3.
- It exhaustively checked **all 81³ = 531,441** semidirect triple associativity cases at depth 0 and both inverse/unit sides for all 81 elements. Depths 0–3 had **1,200 deterministic seeded** additional semidirect action/inverse/pullback checks, including child-injection and rotation-equivariance. The depth-two cardinalities above were checked with Python integers.
- The standalone executable `scripts/alexander_horned_native_ternary_local_phase_action_exact.py` and its companion regression were committed, and the source uses only exact integer modular arithmetic. The local source-equivalent oracle ran; the full GitHub branch's exact checkout Python tests and Agda kernel **were not executed**.
- New Agda module was read/written on #1244 and imported into its original TOE symmetry receiver. No new `postulate`, hole, unsafe termination pragma, or protected ESD modification was introduced.

## Next max-cut, ordered with no fake walls

P0. Obtain compatible Agda compiler and stdlib. Typecheck the source-written local phase module and full #1244 import closure, then resolve any actual kernel errors. No CI required.
P1. Formalize the cylinder setoid quotient and a common-refinement product. Prove equality-on-ends equals eventual equality using actual extension of every finite prefix to an end.
P2. Define the finite discrete topological target and the original inverse-limit clopen basis. Prove compactness and the **all-continuous-maps finite-factorization theorem**; then identify the direct limit with locally constant `C3`-valued functions.
P3. If and only if a source-selected wild ternary embedded handlebody tower exists, define meridian/relative collar and representation-compatible geometric action. Nothing about an abstract Cantor homeomorphism proves it.
P4. If connecting to #1414 root monodromy, #1407 Fourier phase or original Ibrahim Monster 3B, require actual same-object transport morphisms with group-action compatibility; do not reuse numeric `3^27` or `S3` labels as a proof.

This file is deliberately a **finite group/action completion and infinite/topology gap ledger**, not a physical claim or a claimed Agda-verified release.


## De-duplication audit (final 2026-10-28)

The repository already had `AlexanderHornedNativeTernaryFibreActionExact.agda`, committed on the canonical #1244 branch. A static review found that repeating its `Map(X_n,C3)` carrier would violate reuse-first and risk a duplicate ontology. The extension `AlexanderHornedNativeTernaryLocalPhaseActionExact.agda` was therefore rewritten to **import** the original `FibreAction`, `combine`, `inverseAction`, `act`, `pullback`, `pullbackInjective`, `difference`, `transitiveAction`, `LocalFibreAction`, and `evalLocal`. It now contains only nonduplicate typed additions: signed-trit ↔ C3 chart, inverse-sector pullback action, twisted group multiplication/inverse, equivariant refinement, SameOnEnds equivalence and its rotation congruence, and full-local-gauge invariant-observation no-go. The original owner remains the canonical group/fibre tower and the extension stays a smaller additive module.


## 28 October: additional video/PR max-cut, beyond the local C3 action

The canonical native 27/trialectic chart and five-orbit phase module were ALREADY OWNED in #1244. An initial duplicate chart was removed, and only its new third-predicate transport was added to the original owner. The following new proof terms are source-written and Agda kernel-PENDING.

### 1. Recursively compatible Hatcher meridians cannot have nontrivial S3 image

AlexanderHornedS3DerivedMonodromyNoGoExact.agda imports the original six-element S3 multiplication and the ORIGINAL generic HornedProPSolvableBlindExact.SolvableCommutatorTarget theorem. It supplies concrete derived levels S3 -> C3 -> 1 (36 finite S3 commutator cases, then 9 C3 cases). Consequently every S3-valued meridian assignment respecting Hatcher's full recursive COMMUTATOR relations is the identity. This is **not** a statement about arbitrary cubic-polynomial monodromy, which acts on a different source group. A5 and binary-icosahedral 2I remain different PERFECT target groups not excluded by solvability.

### 2. Two 27-state reflection actions admit no equivariant injection

AlexanderHornedTernaryTwentySevenInvolutionNoGoExact.agda uses one common depth-two carrier, C3_sector × Trit². Reflecting ALL three signed coordinates fixes one central address (13 pairs + 1 fixed = 14 orbits); reflecting only the two INTERNAL trits fixes one address per sector (12 pairs + 3 fixed = 15 orbits). There is a constructive proof that NO injection intertwines the second action with the first. Any such injection would send two distinct fixed inputs to the uniquely fixed output. Thus 13/27, 5/9 and a common cardinality 27 cannot force an equivariant object identity.

### 3. Full S3 sector-label symmetry with a geometric boundary

AlexanderHornedSectorDihedralS3EndExact.agda imports exact prior S3 and original native end tower. All six ABC permutations act on the external sector coordinate; group action law and inverse are established from existing S3; every projection square commutes. The even 3-cycle is the original horn sector rotation, and the chosen reflection s satisfies s*r*s=r^-1. This gives genuine intrinsic S3=D3 label symmetry, NOT an ambient reflection of an actual wild ball and NOT analytic root monodromy.

### 4. Tetration by actual function-space isomorphism, not an arithmetic analogy

The ORIGINAL AlexanderHornedNativeTernaryTrialectic27ChartExact.agda already supplies the 27-address ↔ 27-trialectic-code bijection and its local phase-field group chart. This continuation adds a genuine two-sided pointwise equivalence between Map(C3×Trit²,C3) and Map(SynthesisChoice27,TriTruth). It identifies the finite third-level predicate-table *carrier* underpinning the count 3^27=3↑↑3. A fourth **function-space** application gives 3^(3^27), whereas the next **spatial prefix** step has only 81 addresses and 3^81 local phase fields. Both axes remain distinct.

### 5. The 3^5 versus 5^3 duality is now an evaluation/non-descent theorem

The ORIGINAL AlexanderHornedDepthTwoFiveOrbitFibreExact.agda had already quotiented the nine two-trit choices by simultaneous sign reversal into FIVE deterministic orbit types. It also source-wrote a group of 3^5=243 phase fields invariant under that sign action AND the external sector rotation. We extended the SAME module with the different 5^3=125 set of three-sector ORBIT LABEL choices. The actual relationship is composition:

  Map(FiveOrbit,C3_phase) × Map(C3_sector,FiveOrbit) -> Map(C3_sector,C3_phase).

The source now constructs a chosen 3-orbit selector and a section: EVERY three-sector phase table has an origin in a five-orbit phase field. It also proves NO universal recovery of an original five-orbit field from its selected three-sector code, using two different fields with identical output. Two independent orbit-phase coordinates are unseen. The SAME original module now supplies a complete TWO-SIDED kernel normal form: every neutral-readout five-orbit field is uniquely determined pointwise by its (diagonal, antiDiagonal) pair in C3×C3. All 9 possibilities are independently enumerated by the finite Python oracle. This strengthens the earlier collision-only result; the finite source remains Agda kernel-pending. FiveOrbit is a 5-element SET, not automatically C5; thus 243 and 125 are NOT isomorphic groups or interchangeable carriers.

### 6. Actual diagonal/global S3 versus local S3 and Heaps

The original AlexanderHornedNativeTernaryS3LocalValuesExact.agda was extended with 54 constructor cases showing any diagonal/global S3 relabelling preserves pairwise equality of three-valued labels. A chosen local reflection changes the first-two-sector distinct-label count from 1 to 2. Hence the #1275 Heaps/equality-pattern observables are invariant under global S3, NOT under arbitrary local S3 gauge. The original #1275 statistical owner's proof and attribution remain unchanged.

### 7. B3 full twist versus S3 endpoint and spin lifts

In independently-owned PR #1414, PolynomialBraidFullTwistSevenWitnessExact.agda now builds a C7 signed-crossing observer on the actual four Artin generators (two crossings, two inverses), verifies the braid relation and both cancellation directions, and proves (sigma1*sigma2)^3 has identity S3 image but C7 residue 6. This is a genuine presentation-compatible obstruction to reconstructing full braid history from endpoint permutation. Original Artin (1925), Birman (1974), Kassel--Turaev and Jenny Wilson's braid lecture notes retain priority: https://dept.math.lsa.umich.edu/~jchw/RTG-Braids.pdf. B3 central infinite twist, q^3=-1 SU2 sign, and external horn sector C3 are three DIFFERENT group phenomena.

### Executed checks and outstanding max-cut

Independent exact Python PASS: S3 derived 6->3->1; sector D3 reflection; 27-state involution counts and 14-versus-15 orbit partitions; local/global Heaps witness; 3^27 and native chart; original binary 3*2^n versus native ternary 3*3^n; positive full twist S3 identity versus exponent 6 modulo7. New source script: scripts/alexander_horned_polynomial_video_crosspollination_exact.py (committed but NOT executed from the exact pushed blob).

Agda is unavailable here; no successful exact-head Agda kernel receipt, CI check, analytic polynomial-monodromy covering, actual supported wild-embedding same-object group identification, 2I/Monster 3B representation identification, RH theorem or Pickover radian sine sign is claimed. The remaining real cut is Hatcher's selected relative-collar/van Kampen geometry, formal compact-clopen locally constant end-limit theorem, and exact-head kernel checks. Original Ibrahim Monster 3B ownership and prior theorems are retained; no protected ESD edits.
