# Yang–Mills Paper Audit and Highest-Alpha Path — Round 33

Parent index: [Yang–Mills Reference Index](./YangMillsReferenceIndex.md)

Formal owners:

- [Claim audit carrier](../../../DASHI/Physics/YangMills/YangMillsPaperClaimAuditCarrierExact.agda)
- [Adversarial claim atlas](../../../DASHI/Physics/YangMills/YangMillsAdversarialClaimAtlasExact.agda)
- [Claim-family bridge obligations](../../../DASHI/Physics/YangMills/YangMillsClaimFamilyBridgeObligationsExact.agda)
- [Compact-simple group promotion guard](../../../DASHI/Physics/YangMills/YangMillsCompactSimpleGroupPromotionExact.agda)
- [Fixed-spacing gap scaling counterexample](../../../DASHI/Physics/YangMills/YangMillsFixedSpacingGapScaleCounterexampleExact.agda)
- [Selected-background variational/chart bridge](../../../DASHI/Physics/YangMills/BalabanSelectedBackgroundVariationalChartBridgeExact.agda)
- [Cumulative validation root](../../../DASHI/Physics/YangMills/BalabanClayHighestAlphaRound33PaperAuditAllGroupsValidation.agda)

## Decision

Every paper is admissible as an object of study. No paper is admissible as a theorem receipt.

A source record now separates:

- bibliographic status;
- theory signature;
- claimed operator;
- evidence kind;
- assumptions;
- required bridge obligations;
- first open dependency;
- audit outcome.

The supported outcomes are checked theorem, conditional theorem, counterexample to an inference, different-theory statement, first dependency open, and withdrawn claim.

## Audited claim families

The formal atlas currently covers:

1. Nielsen–Semita topological/Hopf-fibration arguments;
2. Toupin celestial holography and Haar measure;
3. Rietz UIDT and its additional scalar;
4. Jacobsen’s five-dimensional orbifold regulator;
5. Agawa’s nonlocal holonomy proposal;
6. Agawa’s retracted addendum;
7. Katayama’s continuum log-Sobolev route;
8. Randolph’s cascade/transfer argument;
9. Watt et al.’s all-beta multiscale proof sketch.

Each source has a complete bridge list. The list does not certify the source; it defines what must be proved before the claim may feed the Clay path.

## Promotion invariants

### Same theory

A topological, celestial, five-dimensional, scalar-extended, nonlocal, fixed-spacing, noncommutative, or effective Polyakov-loop theory does not become pure four-dimensional Yang–Mills without an explicit equivalence theorem.

### Same operator

A Beltrami operator, conformal weight, stochastic generator, regulator Sturm–Liouville operator, FRG linearization or return map is not the reconstructed physical Hamiltonian without a domain-preserving intertwiner and vacuum-compatible reconstruction.

### Scale

Fixed-spacing positivity does not imply a physical mass. Round 33 proves the exact rational example

```text
Delta_latt(a) = a^2,
Delta_phys(a) = a^-1 Delta_latt(a) = a.
```

At `a=1/2`, the physical value is `1/2`; at `a=1/4`, it is `1/4`. Both lattice gaps are strictly positive, but one refinement halves the physical value.

The required continuum invariant remains

```text
Delta_latt(beta(a)) >= m_* a
```

for one `m_*>0` independent of the cutoff.

### No circularity

The target gap, equivalent exponential clustering, positive continuum correlation length, isolated transfer spectrum, or the required uniform RG contraction cannot appear among accepted inputs.

### Every compact simple group

The final group carrier requires root data, compact real form, normalized invariant inner product, faithful unitary representation, Haar probability measure, Casimir and dual-Coxeter data, injectivity radius, structure-constant bounds, Ricci bounds, heat-kernel/character bounds and a group-specific BCH/principal-log radius.

The exceptional dual Coxeter table is recorded exactly:

```text
G2 = 4, F4 = 9, E6 = 12, E7 = 18, E8 = 30.
```

Coverage of `SU(N)` is proved distinct from coverage of all classical families and from coverage of all compact simple groups.

## Concrete Gate-I progress

The new selected-background bridge composes existing in-repository mathematics:

```text
Bałaban constrained variational background
+ exact identification of the physical defect/order convention
+ published fine-bond upper bound below the principal chart cut
-> selected background exists and is unique in regular gauge
-> every selected bond lies in the principal-log image
-> inverse orientation has the exact negative principal logarithm.
```

This is not a new assumed endpoint. It makes the remaining physical seam explicit:

1. identify the repository selected action, constraint and regular gauge with the cited variational theorem;
2. identify the physical bond deviation with the SU(2) chart defect;
3. prove the scalar source upper bound is below the selected chart radius.

Once those inputs are supplied, existence/uniqueness and principal-log admission are produced by the same selected background.

## Current highest-alpha order

1. observe Agda kernel acceptance of the cumulative root;
2. instantiate the selected-background variational/chart bridge physically;
3. prove the selected-background curvature and correlated sixteen-atom Wilson lower bound;
4. derive the existing `10739/196608 > 1/32` terminal Hessian theorem;
5. construct the literal Hessian matrix, stencil, row/column mass and inverse;
6. instantiate finite Combes–Thomas;
7. prove the differentiated physical Schur identity and a scale-uniform RG step;
8. prove large-field/polymer convergence and construct the interacting measure;
9. take thermodynamic and changing-spacing limits with OS axioms and nontriviality;
10. construct local curvature operators, asymptotic-freedom matching, stress tensor and OPE;
11. reconstruct the Hamiltonian, exclude spectral pollution and prove the positive gap;
12. instantiate the complete construction for every compact simple group.

## Verification

Run:

```bash
AGDA_JOBS=1 bash scripts/check_yang_mills_clay_highest_alpha_round33.sh
```

The checker must cascade through Round 32, reject holes and proof escapes, verify all source identifiers and audit guards, verify the exact scaling arithmetic and exceptional table, check the documentation link graph, and invoke the pinned Agda 2.9 cumulative root.

A static audit is not a kernel result. The branch remains draft until the dedicated workflow reports success.
