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

The new `AlexanderHornedNativeTernaryLocalPhaseActionExact.agda` **explicitly** defines trit↔C3 value charts, two inverse round-trip proofs, and the original (pointwise) group operations on `G_n`. Its `translate g f` is `x↦g(x)+f(x) mod3`. All action/group laws are supplied as **pointwise propositional equalities**; this avoids inventing global function extensionality or a postulate.

There are `|X_n|=3^(n+1)` finite clopen cylinders. Classical finite function counting gives `|G_n|=3^(3^(n+1))`. At depth 2, `|X_2|=27`, `|G_2|=3^27=7,625,597,484,987`. The exact source already owns `Native.ternaryConfigurationTetration` and proves the numerical identification `3^27=3↑↑3`. **The 27 address cells are not 27 time samples, 27 Fourier modes, 27 physical horns or 27 Monster dimensions.** Any such identification needs a typed map and its desired invariance property.

## Exact finite pullback / section / injection theorem

Original `balancedProjection` sends a prefix (sector, trit-vector including one new digit) to its chronological parent. Its induced phase pullback is

```
p_n^*(f)(x) = f(p_n(x)).
```

The module source-writes `refineHomomorphismAt`, `refineInverseAt`, and `refineTranslationAt` directly on original carriers.

More strongly, the original `Native.snoc` and `dropLastSnoc` construct an **actual section** `child_n(x)=(sector, prefix++[-1])`. Its proof `childSection` satisfies `p_n(child_n(x))=x`. Consequently

```
(∀y ∈ X_(n+1), p_n^* f(y) = p_n^* g(y))
    ⇒ (∀x ∈ X_n, f(x)=g(x)).
```

This is exactly the source-written `refineReflectsEquality`. It does not require function extensionality, an infinite compactness principle, or a count coincidence. Injectivity here is in the **pointwise function-setoid**.

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

The same module provides `CylinderPhase`: an actual finite resolution n paired with a phase function `f:X_n→C3`. It evaluates a field on an ORIGINAL `Native.BalancedEndPoint` via `f(Tower.stateAt(point,n))`. The typed proof `refinementPreservesEndValue` follows from the existing `InverseLimitPoint.coherent` equation. The `shiftEnd` construction produces an actual coherent rotated infinite end. The theorem `endRotationValueSquare` identifies evaluating an externally rotated field with evaluating the original field at the inverse-rotated end.

More, `SameOnEnds` is the **pointwise equivalence relation** on cylinder representatives induced by all coherent infinite ends. Its reflexive/symmetric/transitive lemmas, one-step refinement invariance and sector-rotation congruence are source-written. This supplies the quotient's **setoid equality interface**; it does *not* pretend to have constructed a higher-inductive quotient type or a full topological compactness theorem.

A complete abstract identification

```
colim_n Map(X_n,C3)  ≅  C_loc(K3,C3)
```

still requires **(a)** quotienting representatives by an appropriate eventual-equivalence relation and proving the group law well-defined at common refinement, **(b)** equivalence of that relation with equality on all ends, and **(c)** defining topology on the inverse-limit end space and showing every continuous map to finite-discrete C3 factors through a single finite clopen cylinder partition. This final surjectivity uses classical compactness plus zero-dimensionality but is **not kernel discharged** here.

## Strong actual information-loss/no-weld consequence

For any two local fields `f,h:X_n→C3`, the difference field `g(x)=h(x)−f(x)` satisfies `translate g f(x)=h(x)` **at every address**. The module source-writes `gaugeFromTo` and `gaugeTranslationTransitiveAt`, using the ORIGINAL C3 inverse and associativity. Therefore **any pointwise-extensional observable invariant under the FULL local `G_n` action is constant**. The source-written `gaugeInvariantObservableConstant` makes the extensionality hypothesis explicit rather than smuggling in function equality.

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
