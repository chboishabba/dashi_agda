# Paper 4: Physical Hilbert Space Construction Route

Date: `2026-05-29`
Status: substantive non-promoting draft; fail-closed at infinite-dimensional and
physical-completion boundaries

This paper records the current Gate 5 physical-Hilbert construction route.  The
positive content is a typed finite and receipt-backed construction program:
depth-indexed Hilbert carriers, isometric depth embeddings, finite quotient
Hilbert staging, one-point Stone data, finite traversal and strong-continuity
witnesses, GNS quotient targets, and a physical Hilbert colimit obligation
surface.  The paper does not claim a completed noncollapsed physical Hilbert
space, an accepted infinite-depth Hilbert completion, a physical strongly
continuous traversal group, a self-adjoint physical colimit generator, a GNS
Hilbert-space construction, or a Born-rule theorem.  Those promotion boundaries
are fixed false in the cited receipt modules.

## 1. Scope And Claim

The construction starts from depth carriers rather than from an assumed
continuum Hilbert space.  `DASHI.Quantum.Stone` defines
`HilbertInductiveLimitTransitionSystem`, whose fields `H_d`, `U_d`, `iota_d`,
`iota_d-isometry`, and `iota_d-U-compatible` specify a depth-indexed Hilbert
carrier, a real-parameter depth action, and isometric compatibility of the
embedding with that action.  The discrete finite route is exposed by
`DASHI.Quantum.Stone.DiscreteTimeHilbertDepthEmbeddingSystem`, with `H_d`,
`Ustep_d`, `iota_d`, `iota_d-isometry`, `Ustep-zero`, and
`iota_d-Ustep-compatible`.

The current result is a construction route, not a completed physical object.
`DASHI.Physics.Closure.PhysicalHilbertColimitObligation.canonicalPhysicalHilbertColimitObligationReceipt`
records finite quotient Hilbert/Stone data as bound, while keeping
`acceptedInfiniteDepthPhysicalHilbertCompletionSupplied`,
`physicalFilteredColimitHilbertPromoted`,
`physicalStrongContinuityOnCompletionPromoted`, and
`selfAdjointPhysicalColimitGeneratorPromoted` equal to `false`.

## 2. Depth States And Isometric Inclusion

The depth state at depth `d` is the carrier
`HilbertSpace.H (H_d d)` from
`DASHI.Quantum.Stone.DiscreteTimeHilbertDepthEmbeddingSystem`.  The depth
transition is `iota_d : H_d d -> H_d (suc d)`, and its admissible Hilbert
content is exactly the inner-product preservation field `iota_d-isometry` in
the same record.  The one-point concrete witness is
`DASHI.Quantum.Stone.onePointDiscreteIdentityDepthSystem`, whose embedding is
`onePointZeroExtensionIota` and whose isometry proof is
`onePointZeroExtensionIota-isometry`.

Finite support is represented by
`DASHI.Quantum.Stone.FinitelySupportedDepthColimitDomain`.  Its fields
`supportDepth`, `supportVector`, `successorShadow`, and `successorShadowIsIota`
record a vector with a chosen finite support depth and its successor image.
The concrete one-point witness is
`DASHI.Quantum.Stone.onePointFiniteSupportColimitDomain`; the selected finite
quotient route packages its own depth-0 witness through
`DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt.selectedFiniteQuotientProjectionDiscreteTimeHilbertDepthStoneReceipt`.

The finite domain witness is not physical completion.  In
`DASHI.Quantum.Stone.DiscreteTimeHilbertDepthStoneReceipt`,
`continuousL2CompletionPromoted`, `finiteSupportColimitDomainPromoted`, and
`selfAdjointColimitGeneratorPromoted` are receipt fields, and the selected
finite quotient receipt fixes all three to `false` in
`selectedFiniteQuotientProjectionDiscreteTimeHilbertDepthStoneReceipt`.

## 3. Finite Quotient Hilbert Staging

The selected finite quotient lane is more than a name: it has a discrete
Hilbert/Stone receipt.  `selectedFiniteQuotientProjectionDiscreteTimeHilbertDepthStoneReceipt`
in `DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt` packages
`selectedFiniteQuotientProjectionDiscreteDepthSystem`,
`selectedFiniteQuotientProjectionFiniteSupportColimitDomain 0`,
`selectedFiniteQuotientProjectionDiscreteGeneratorDomainTarget`, and
`selectedFiniteQuotientProjectionDiscreteSymmetricGeneratorDomainTarget`.
The same receipt records `discreteStrongContinuityIsIdentityAtZero = true` for
the finite identity system.

The finite quotient staging also records a formal Stone attempt.  The record
`DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt.SelectedFiniteQuotientStoneAttempt`
contains `formalStoneBundle`, `formalStoneRoute`,
`hilbertInductiveLimitTransitions`, and
`stoneHilbertInductiveLimitTransitions`.  Its canonical value
`selectedFiniteQuotientStoneAttempt` sets
`finiteSelectedQuotientAvailable`, `formalBundleConstructedByStoneRecord`,
`formalIotaIsometryConstructed`, and `formalIotaUCompatibilityConstructed` to
`true`, while `formalBundlePromotesPhysicalHilbertStructure`,
`formalBundlePromotesPhysicalUnitaryEvolution`,
`formalBundlePromotesSchrodingerClosure`, and
`realStoneBundleConstructedFromCurrentData` remain `false`.

This makes the finite quotient lane a typed staging surface: it records
projection-level finite progress and a formal Stone record, but it does not
promote the selected coordinate quotient into a nondegenerate physical Hilbert
carrier.

## 4. Traversal Data At Finite Depth

The traversal interface is supplied at the level of depth data.
`DASHI.Quantum.Stone.TraversalUnitaryDepthData` requires a depth Hamiltonian
`Hamiltonian_d`, unitarity of `U_d` through `U_d-unitary`, and block-diagonal
depth compatibility through `hamiltonianBlockDiagonalDepthCondition`.  The
one-point inhabitant is `DASHI.Quantum.Stone.onePointTraversalUnitaryDepthData`,
which uses `onePointDepthHamiltonian`,
`onePointDepthTraversalUnitary`, and
`onePointDepthHamiltonianBlockDiagonal`.

`DASHI.Physics.Closure.TraversalGroupStrongContinuity.canonicalGate5FiniteTraversalGroupStrongContinuityReceipt`
threads this finite data through Gate 5.  It records
`finiteTraversalDepthData = Stone.onePointTraversalUnitaryDepthData`,
`finiteTraversalGroup = Stone.onePointFiniteUnitaryGroup`,
`finiteTraversalGroupConstructed = true`, and
`finiteStrongContinuityConstructed = true`.  The same receipt keeps
`physicalHilbertCompletionPromoted`, `physicalStrongContinuityPromoted`, and
`traversalDerivedPhysicalStoneBundlePromoted` equal to `false`.

The selected finite quotient traversal is weaker.  `DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt.SelectedQuotientStrongContinuitySocket`
records the current finite advance as `finiteAdvanceTraversal`, but its
boundary says the advance is semigroup-only because `shiftStartPoint` has no
preimage.  The same socket fixes `strongContinuityForPhysicalTraversalSupplied`
and `traversalDerivedStoneBundleSupplied` to `false`.

## 5. Strong Continuity: Constructed Witness And Physical Boundary

The constructed continuity witness is the one-point Stone witness.
`DASHI.Quantum.Stone.StoneContinuity` defines the epsilon-delta surface for a
map `U : Real -> S -> S` and distance `dist`.  The concrete inhabitant is
`DASHI.Quantum.Stone.onePointFiniteStrongContinuity`, using
`onePointFiniteDistance` and the one-point lift
`onePointFiniteLift`.

`DASHI.Quantum.StrongContinuity.canonicalStrongContinuityWitness` packages
`canonicalGNSUniversalPropertyWitness`,
`canonicalSelfAdjointColimitGeneratorWitness`,
`onePointFiniteStoneBundle`, `onePointFiniteStrongContinuity`, and
`Stone-theorem onePointFiniteStoneBundle`.  This is a finite one-point Stone
continuity receipt.  The physical strong-continuity upgrade remains closed by
`DASHI.Physics.Closure.TraversalGroupStrongContinuity.canonicalGate5FiniteTraversalGroupStrongContinuityReceipt`,
where `physicalStrongContinuityPromoted = false`, and by
`DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt.SelectedQuotientStrongContinuitySocket`,
where `strongContinuityForPhysicalTraversalSupplied = false`.

The exact missing physical content is named by
`DASHI.Quantum.Stone.PhysicalStrongContinuityOnGNSHilbertCompletionBlocker`
as `missingPhysicalStrongContinuityOnGNSHilbertCompletion`, and by
`DASHI.Physics.Closure.TraversalGroupStrongContinuity.canonicalGate5TraversalStrongContinuityBlockers`
as missing noncollapsed completion, missing GNS-to-DASHI Hilbert bridge,
missing physical traversal unitary group, missing physical strong continuity,
and missing traversal-derived physical Stone bundle.

## 6. Stone Theorem Carrier Receipt

`DASHI.Quantum.Stone` defines the local Stone package.  `StoneBundle` contains
`lift`, `generator`, `distance`, `self-adjoint`, `stone-group`, and
`strong-continuity`; `Stone-theorem` turns an already supplied `StoneBundle`
into `StoneConsequences` containing the same group, continuity, and
self-adjointness consequences.  Thus the internal Stone theorem surface is a
bundle-consuming theorem, not an external magic import.

The finite concrete bundle is
`DASHI.Quantum.Stone.onePointFiniteStoneBundle`.  It uses
`onePointFiniteHamiltonian`, `onePointFiniteHamiltonianSelfAdjoint`,
`onePointFiniteUnitaryGroup`, and `onePointFiniteStrongContinuity`.  The
structured data record
`DASHI.Quantum.Stone.onePointFiniteSelfAdjointHamiltonianStoneData` sets
`finiteOnly = true` and `physicalHilbertTowerPromoted = false`.

`DASHI.Physics.Closure.StoneTheoremCarrierReceipt.canonicalStoneTheoremCarrierReceipt`
records this at Gate 5.  It marks `stoneGatesWitnessBundleAvailable = true`,
`strongContinuityWitnessAvailable = true`,
`finiteStoneCarrierRecorded = true`, and
`physicalStoneCarrierPromoted = false`.  Its nested
`canonicalFiniteDepthStoneSelfAdjointGeneratorReceipt` records
`finiteDepthSelfAdjointGeneratorExists = true` by using
`Stone.Stone-theorem Stone.onePointFiniteStoneBundle` and
`Stone.onePointFiniteHamiltonianSelfAdjoint`.

The Stone carrier receipt therefore authorizes only a finite one-point Stone
carrier and finite-depth self-adjoint generator record.  It also records the
blockers `finiteOnePointCarrierOnly`,
`missingNoncollapsedPhysicalHilbertColimit`,
`missingPhysicalTraversalUnitaryPromotion`,
`missingPhysicalStoneBridgeBoundary`, and
`missingPhysicalHamiltonianSelfAdjointness` in
`canonicalStoneTheoremCarrierBlockers`.

This is also the correct finite Stone-von Neumann/Hilbert boundary for the
paper.  The finite one-point Stone carrier and finite quotient Hilbert staging
are inhabited, but they are not promoted to a physical Stone carrier.  The
nearest checked boundary identifier is the field projection
`DASHI.Physics.Closure.StoneTheoremCarrierReceipt.StoneTheoremCarrierReceipt.physicalStoneCarrierPromotedIsFalse`
applied to
`DASHI.Physics.Closure.StoneTheoremCarrierReceipt.canonicalStoneTheoremCarrierReceipt`.
Paper 4 may therefore discuss finite Stone/von-Neumann-style authority only
as finite carrier staging plus boundary context; it may not state that the
finite Stone carrier is the completed physical Hilbert representation.

## 7. Self-Adjoint Generator Surface

`DASHI.Quantum.SelfAdjointGenerator` packages the one-point Stone Hamiltonian
as a colimit-generator witness.  It defines `ColimitHilbert =
onePointFiniteHilbertSpace`, `ColimitVector = DepthCarrier zero`,
`H = onePointFiniteHamiltonian`, and
`colimitGeneratorSelfAdjoint = onePointFiniteHamiltonianSelfAdjoint`.  Its
canonical record `canonicalSelfAdjointColimitGeneratorWitness` contains
`finiteSupportDomain = onePointFiniteSupportColimitDomain` and
`generatorSelfAdjoint = colimitGeneratorSelfAdjoint`.

This surface is theorem-bearing only at the finite one-point level named by the
module itself.  The physical colimit generator is not promoted:
`DASHI.Physics.Closure.PhysicalHilbertColimitObligation.canonicalPhysicalHilbertColimitObligationReceipt`
fixes `selfAdjointPhysicalColimitGeneratorPromoted = false`, and
`DASHI.Physics.Closure.CrossGateHamiltonianCompatibilityReceipt.canonicalCrossGateHamiltonianCompatibilityReceipt`
fixes
`gate5SelfAdjointGeneratorGate23YMHamiltonianCompatibilityPromoted = false`
and `gate5Gate23Gate6CrossGateHamiltonianCompatibilityPromoted = false`.

This boundary matters because a physical Hamiltonian would also need
cross-gate identification.  `DASHI.Physics.Closure.CrossGateHamiltonianCompatibilityReceipt`
records Gate 5 Stone/GNS, Gate 2/3 Yang-Mills Hamiltonian, and Gate 6 DHR
sector frontiers, but its blockers include
`missingGate5SelfAdjointGeneratorToGate23YMHamiltonianIdentification`,
`missingCommonHamiltonianDomainAcrossStoneYMDHR`, and
`missingCrossGateHamiltonianNaturalityLaw`.

## 8. GNS Quotient Carrier Route

The GNS route is recorded as a quotient and representation target, not as a
constructed physical Hilbert space.  `DASHI.Physics.Closure.GNSCarrierQuotientReceipt.GNSCarrierQuotientReceipt`
threads `AQFTNet.canonicalAQFTNetReceipt`,
`L5.canonicalDepthFilteredLocalAlgebraSurface`,
`L5.canonicalAQFTL3FilteredColimitPreservationAttemptSurface`,
`Modular.abstractStateFunctional`, `Modular.abstractGNSNullIdeal`,
`Modular.abstractGNSPreHilbertQuotient`,
`Modular.canonicalGNSNullIdealPreHilbertQuotientReceipt`,
`Modular.canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt`, and
`GNSFell.canonicalGNSFellRepresentationSurface`.

The same receipt identifies the quotient path.  It sets
`filteredColimitLocalAlgebraTarget` to the `A_colim` field of
`DepthFilteredLocalAlgebraSurface`, matches the vacuum projection target to
`Modular.abstractStateFunctional`, matches the null ideal target to
`Modular.abstractGNSNullIdeal`, and matches the quotient carrier target to
`Modular.abstractGNSPreHilbertQuotient`.  It also records that modular quotient
receipt data and GNS/Fell descent receipts are available as receipts:
`modularNullIdealReceiptInhabited = true`,
`nullIdealLeftIdealTargetThreaded = true`,
`innerProductDescendsTargetThreaded = true`,
`gnsQuotientRelationAdvanced = true`, and
`finiteTraceStateAPIAvailable = true`.

The GNS Hilbert space remains closed.  The canonical receipt fixes
`filteredColimitPreservationProved = false`,
`vacuumProjectionFunctionalConstructedFromColimit = false`,
`modularQuotientTheoremPromoted = false`,
`modularWellDefinednessPromoted = false`,
`gnsFellPromoted = false`,
`gnsQuotientInnerProductPromoted = false`,
`filteredColimitLocalAlgebraInhabited = false`, and
`GNSHilbertSpaceConstructed = false`.  Its first blocker is
`missingFilteredColimitLocalAlgebraInhabitant`.

## 9. Physical Hilbert Colimit Obligation

The physical colimit obligation is explicit in
`DASHI.Physics.Closure.PhysicalHilbertColimitObligation`.  The canonical
receipt binds `finiteSelfAdjointHamiltonianStoneData` to
`Stone.onePointFiniteSelfAdjointHamiltonianStoneData`,
`finiteDepthIdentityStoneTowerSkeleton` to
`Stone.onePointFiniteDepthIdentityStoneTowerSkeleton`,
`physicalHilbertStonePrimitiveRequest` to
`Stone.canonicalPhysicalHilbertStonePrimitiveRequest`, and
`selectedFiniteQuotientDepthStoneReceipt` to
`Sch.selectedFiniteQuotientProjectionDiscreteTimeHilbertDepthStoneReceipt`.
It also records finite quotient data, finite Stone data, finite `iota`
isometry, and finite `iota`/`U` compatibility as bound through
`finiteQuotientHilbertDataBound`, `finiteQuotientStoneDataBound`,
`finiteIotaIsometryBound`, and `finiteIotaUCompatibilityBound`.

The obligation then closes the physical promotion bits.  The canonical receipt
sets `acceptedInfiniteDepthPhysicalHilbertCompletionSupplied = false`,
`physicalFilteredColimitHilbertPromoted = false`,
`traversalDerivedPhysicalStoneBundlePromoted = false`,
`physicalStrongContinuityOnCompletionPromoted = false`,
`selfAdjointPhysicalColimitGeneratorPromoted = false`, and
`externalContinuumHilbertColimitAuthorityAccepted = false`.  Its blocker list
is `canonicalPhysicalHilbertColimitBlockers`, containing
`missingNoncollapsedPhysicalQuotientInnerProduct`,
`missingAcceptedInfiniteDepthPhysicalHilbertCompletion`,
`missingPhysicalFilteredColimitHilbertCarrier`,
`missingTraversalDerivedPhysicalStoneBundle`,
`missingPhysicalStrongContinuityOnHilbertCompletion`,
`missingSelfAdjointPhysicalColimitGenerator`, and
`missingExternalContinuumHilbertColimitAuthority`.

This is the central Paper 4 boundary: finite quotient Hilbert/Stone staging is
available, but the infinite-depth physical Hilbert completion is not supplied.
It is also the exact place where Paper 4 meets the Clay Yang-Mills blocker:
the finite Stone-von Neumann/Stone carrier result supplies a finite
self-adjoint generator witness, but the physical Hilbert completion required
for the Yang-Mills Hamiltonian is precisely the closed flag
`DASHI.Physics.Closure.StoneTheoremCarrierReceipt.physicalStoneCarrierPromotedIsFalse`.
Paper 8 names the corresponding bridge as
`DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian`: the finite Hamiltonian
data can enter the tower schema, but the colimit gap lift needed for a
physical Yang-Mills Hamiltonian remains a non-promoted obligation.

## 10. Boundary To Infinite-Dimensional Authority And Measurement

The current repository records external functional-analysis authority only as
boundary text.  `DASHI.Physics.Closure.PhysicalHilbertColimitObligation.canonicalPhysicalHilbertColimitAuthorityBoundary`
mentions Stone 1932, von Neumann 1932, and Reed-Simon-style functional
analysis as context, while the same receipt fixes
`externalContinuumHilbertColimitAuthorityAccepted = false`.  Therefore this
paper may cite the boundary as a receipt-local authority boundary, but it may
not claim that an external theorem token has been imported into DASHI or that
the physical Hilbert colimit has been accepted.

The physical Stone upgrade has a precise requested interface.
`DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt.PhysicalHilbertStoneBundleDataRequest`
names required fields including a nondegenerate projection algebra, quotient
inner-product well-definedness, Hilbert completion, one-parameter traversal
automorphism group, strong continuity, generator, Stone self-adjointness, and a
`StoneBundle`.  Its canonical construction
`physicalHilbertStoneBundleDataRequest` keeps
`nondegenerateProjectionAlgebraSupplied`,
`hilbertQuotientInnerProductSupplied`, `hilbertCompletionSupplied`,
`oneParameterTraversalGroupSupplied`, `strongContinuitySupplied`, and
`stoneBundleConstructedFromQuotientTraversal` equal to `false`.

The formal-to-physical bridge is also named but absent.
`DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt.FormalToPhysicalTraversalStoneUpgradeRequest`
specifies `PhysicalTraversalStoneUpgradeData`, including `physicalTower`,
`physicalHilbertSpace`, `quotientToHilbert`, `physicalUnitary`,
`physicalStoneBundle`, and comparison to the finite advance at time 1.  Its
canonical value `formalToPhysicalTraversalStoneUpgradeRequest` records
`finiteAdvanceTraversalConstructed = true`, but
`finiteAdvanceTraversalGroupConstructed = false`,
`upgradeDataSupplied = false`, and
`physicalTraversalStoneBundleConstructed = false`.

Measurement is downstream of these missing objects.  The GNS quotient receipt
does not construct a GNS Hilbert space, and
`DASHI.Physics.QFT.AQFTTypedNetSurface` names
`missingVacuumOrGNSAdapter` and `missingBornRuleAdapter`.
`DASHI.Physics.QFT.GNSFellRepresentationSurface` records that no Born-rule
probability theorem, empirical measurement map, state-observable duality
theorem, folium construction, or Fell-topology promotion is supplied.
Consequently Paper 4 cannot derive Born probabilities.  A future promotion
would need a selected physical state or vacuum adapter, a constructed GNS
Hilbert representation, a well-defined pairing of states and observables, a
Born-rule map from projections or effects to probabilities, and compatibility
of that map with the traversal/Stone dynamics and finite-to-colimit
embeddings.  None of those objects is supplied by the receipts cited above.

## 11. What This Paper Does Not Claim

Paper 4 does not claim a completed physical Hilbert space. The governing
receipt is
`DASHI.Physics.Closure.PhysicalHilbertColimitObligation.canonicalPhysicalHilbertColimitObligationReceipt`,
where `acceptedInfiniteDepthPhysicalHilbertCompletionSupplied = false` and
`physicalFilteredColimitHilbertPromoted = false`.

Paper 4 does not claim physical strong continuity on a completed Hilbert
space. The finite one-point and finite traversal witnesses are recorded, but
`physicalStrongContinuityOnCompletionPromoted = false` in the physical Hilbert
colimit obligation and `physicalStrongContinuityPromoted = false` in
`DASHI.Physics.Closure.TraversalGroupStrongContinuity.canonicalGate5FiniteTraversalGroupStrongContinuityReceipt`.

Paper 4 does not claim a self-adjoint physical colimit Hamiltonian. The finite
one-point Stone generator is receipt-backed, but
`selfAdjointPhysicalColimitGeneratorPromoted = false` and cross-gate
Hamiltonian compatibility remains blocked by
`missingGate5SelfAdjointGeneratorToGate23YMHamiltonianIdentification`,
`missingCommonHamiltonianDomainAcrossStoneYMDHR`, and
`missingCrossGateHamiltonianNaturalityLaw`.

Paper 4 does not claim a GNS Hilbert-space construction. The GNS quotient and
Fell representation surfaces are target and packaging surfaces; the canonical
GNS quotient receipt keeps `GNSHilbertSpaceConstructed = false` and its first
blocker is `missingFilteredColimitLocalAlgebraInhabitant`.

Paper 4 does not claim the Born rule, empirical measurement, or an
interacting-QFT theorem. The AQFT/GNS surfaces still name
`missingVacuumOrGNSAdapter`, `missingBornRuleAdapter`, no empirical
measurement map, no folium promotion, and no state-observable duality theorem.

Paper 4 does not claim that external Stone, von Neumann, or Reed-Simon-style
authority has been imported as a DASHI theorem token. Those references are
recorded as boundary context only, while
`externalContinuumHilbertColimitAuthorityAccepted = false`.

## Result

Paper 4 can claim an auditable finite-to-physical construction route:
depth-indexed carriers and isometric inclusions in `DASHI.Quantum.Stone`,
selected finite quotient Hilbert/Stone staging in
`DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt`, finite
traversal and strong-continuity receipts in
`DASHI.Physics.Closure.TraversalGroupStrongContinuity`, a finite Stone theorem
carrier receipt in `DASHI.Physics.Closure.StoneTheoremCarrierReceipt`, GNS
quotient targets in `DASHI.Physics.Closure.GNSCarrierQuotientReceipt`, and the
fail-closed colimit obligation in
`DASHI.Physics.Closure.PhysicalHilbertColimitObligation`.

Paper 4 cannot claim the completed physical Hilbert space.  The exact open
boundary is the construction of a noncollapsed physical quotient Hilbert
carrier, accepted infinite-depth completion or physical filtered colimit,
invertible physical traversal unitary group, physical strong continuity,
traversal-derived Stone bundle, self-adjoint physical colimit generator,
GNS Hilbert-space construction, cross-gate Hamiltonian identification, and
Born-rule/measurement adapter.
