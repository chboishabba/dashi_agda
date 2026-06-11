# Paper 2 Draft: DCHoTT Bridge and Finite GR Geometry

Status: complete working draft; fail-closed; non-promoting.

Scope: Paper 2 packages the current geometry and Gate 4 GR surfaces as an
honest bridge paper. It records what DASHI has actually staged: B0.1
pro-object semantics, target surfaces for B0.2/B0.3, and a finite Lorentzian
valuation-metric chain through local zero-table curvature/Ricci/Einstein
receipts. It does not claim a continuum GR theorem, a sourced non-flat
Einstein equation, a W4 stress-energy source, a DCHoTT manifold equivalence, or
GRQFT promotion.

Target journal: Classical and Quantum Gravity.

## 0. Positive claim receipt anchors

Every positive GR-facing sentence in this paper is limited to one of the
following inhabited or explicitly fail-closed receipt anchors.

| Paper claim surface | Agda module and identifier | Admissible wording |
|---|---|---|
| B0.1 pro-object semantics | `DASHI.Geometry.ProObjectSemantics.canonicalConstructedProObjectLimitSurface`; `DASHI.Geometry.TransportSmoothFormalDiskSurface.canonicalTransportSmoothFormalDiskReceipt` | Constructed DASHI-side compatible-family/pro-object semantics plus transport-smooth/formal-disk obligation sockets. |
| B0.2 holonomy bridge target | `DASHI.Geometry.FlatFormalDiskHolonomySurface.b02HolonomyTargetsOnlyNoB0Promotion` | Typed flat formal-disk/holonomy target surface only; no holonomy convergence or B0 promotion. |
| B0.3 G-structure/Levi-Civita bridge target | `DASHI.Geometry.GStructureLeviCivitaBindingSurface.canonicalGStructureLeviCivitaBindingReceipt`; `DASHI.Geometry.GStructureLeviCivitaBindingSurface.canonicalLeviCivitaNotPromoted` | Typed frame/metric/G-structure binding target; Levi-Civita promotion remains false. |
| Continuum Levi-Civita bridge boundary | `DASHI.Geometry.LeviCivitaBridge.canonicalLeviCivitaBridgeReceipt`; `DASHI.Geometry.LeviCivitaBridge.LeviCivitaBridgeReceipt.noEinsteinPromotionFromThisBridge-v` | Bridge obligation only; no Einstein promotion from the bridge. |
| Finite valuation metric | `DASHI.Physics.GR.ValuationMetric.canonicalValuationMetricSurface`; `DASHI.Physics.GR.ValuationMetric.valuationMetricAt`; `DASHI.Physics.GR.ValuationMetric.valuationMetricSymmetric` | FactorVec-based finite Lorentzian valuation metric and symmetry law. |
| Finite Christoffel surface | `DASHI.Physics.GR.Christoffel.canonicalChristoffelSurface`; `DASHI.Physics.GR.Christoffel.christoffelSymbol`; `DASHI.Physics.GR.Christoffel.christoffelSymbolTorsionFree` | Local torsion-free Christoffel-symbol API over the valuation metric. |
| Local Riemann/Ricci/scalar/Einstein zero-table staging | `DASHI.Physics.GR.RiemannTensor.canonicalRiemannTensorSurface`; `DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt` | Selected four-chart local zero-table curvature, Ricci, scalar curvature, Einstein tensor, finite-r Bianchi, and local contracted-Bianchi divergence. |
| Local Einstein tensor | `DASHI.Physics.GR.EinsteinTensor.canonicalEinsteinTensorSurface`; `DASHI.Physics.GR.EinsteinTensor.EinsteinTensorSurface.contractedBianchiDivergenceZero`; `DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface.grSelectedFiniteRContractedBianchiDivergenceZero` | Inhabited local zero-table Einstein tensor with contracted-Bianchi divergence zero at that surface. |
| Gate 4 contracted-Bianchi promotion boundary | `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt`; `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.grGate4ContractedBianchiSelectedConnectionBlocker`; `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.grGate4ContractedBianchiStillNotPromoted`; blocker `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.missingCarrierConnectionIsLeviCivita` | Contracted-Bianchi promotion remains fail-closed at the selected-connection Levi-Civita dependency. |
| Lower-six downstream inspection | `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.canonicalGRLower6PostBlockerDownstreamInspectionReceipt`; `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.grLower6PostBlockerRicciEinsteinTowerStillBlocked`; `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.grLower6PostBlockerSourcedEinsteinStillBlocked` | Lower-six residual data do not advance Ricci/Einstein or sourced-Einstein promotion. |
| Ricci candidate shape | `DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature.canonicalGRDiscreteRicciCandidateFromCurvature` | Candidate shape and local-fibre decomposition only; no Ricci theorem or GR promotion. |
| Stress-energy compatibility boundary | `DASHI.Physics.GR.StressEnergyCompatibility.canonicalStressEnergyCompatibilitySurface`; `DASHI.Physics.GR.StressEnergyCompatibility.canonicalStressEnergyBoundaryInterface`; first missing field `DASHI.Physics.Closure.EinsteinEquationCandidate.missingW4AnchorArtifactReceiptForMatterStress` | Interface alignment and exact W4 source blocker; no matter source or sourced Einstein law. |
| Contracted-Bianchi matter closure | `DASHI.Physics.Closure.ContractedBianchiMatterClosure.canonicalContractedBianchiMatterClosureReceipt`; `DASHI.Physics.Closure.ContractedBianchiMatterClosure.contractedBianchiMatterClosureRemainsFailClosed`; field `DASHI.Physics.Closure.ContractedBianchiMatterClosure.ContractedBianchiMatterClosureReceipt.einsteinTensorContractedBianchiDivergenceZero` | Existing local witnesses are composed, closure promotion remains false. |
| Sourced-Einstein compatibility target | `DASHI.Physics.Closure.ContractedBianchiMatterClosure.canonicalSourcedEinsteinCompatibilityReceipt`; `DASHI.Physics.Closure.ContractedBianchiMatterClosure.sourcedEinsteinCompatibilityFiniteRecorded`; `DASHI.Physics.Closure.ContractedBianchiMatterClosure.sourcedEinsteinCompatibilityStillFailClosed` | Finite compatibility target is recorded and remains fail-closed. |
| Wald authority boundary | `DASHI.Physics.Closure.WaldGRAuthorityReceipt.canonicalWaldGRAuthorityReceipt`; `DASHI.Physics.Closure.WaldGRAuthorityReceipt.waldGRAuthorityContinuumLeviCivitaStillFailClosed`; `DASHI.Physics.Closure.WaldGRAuthorityReceipt.waldGRAuthorityContinuumSourcedEinsteinStillFailClosed` | Wald is recorded as external continuum authority; no continuum Levi-Civita or sourced-Einstein theorem is constructed in DASHI. |
| Friedmann instability/Temple authority boundary | `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.canonicalFriedmannInstabilitySaddleReceipt`; `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.friedmannInstabilitySaddlePointAuthorityBacked`; `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.friedmannInstabilityDoesNotRemoveDarkEnergyHere`; `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.friedmannInstabilityDoesNotFalsifyLCDMHere`; `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.friedmannInstabilityCosmologyPromotionStillFailClosed` | Temple-Alexander-Vogler Friedmann instability is external authority context only; no DASHI cosmology promotion. |
| Paper 8 GR tower instance | `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.canonicalMillenniumTowerGRInstanceReceipt`; `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.continuumGRAuthorityConstructedHereIsFalse`; `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.cosmologyPromotedIsFalse`; `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.millenniumTowerGRNoPromotion` | Paper 2 supplies the Gate 4 GR lane input to the Paper 8 tower schema; continuum GR authority, cosmology promotion, and GR promotion remain fail-closed. |

## 0.1 Consolidated Paper 2 claim ledger

Paper 2 has four positive claims, each bounded by the receipt anchors above.

1. DASHI has an inhabited internal B0.1 pro-object/compatible-family semantics
   for its finite refinement tower. This claim is backed by
   `canonicalConstructedProObjectLimitSurface` and by the transport-smooth
   formal-disk receipt sockets. It is not a DCHoTT manifold theorem.

2. DASHI has typed B0.2/B0.3 bridge targets for holonomy and
   G-structure/Levi-Civita comparison. This claim is backed by
   `b02HolonomyTargetsOnlyNoB0Promotion` and
   `canonicalGStructureLeviCivitaBindingReceipt`. It is not holonomy
   convergence, flat formal-disk path independence, or Levi-Civita promotion.

3. DASHI has a finite FactorVec GR staging chain: valuation metric,
   torsion-free Christoffel surface, selected four-chart local zero-table
   Riemann/Ricci/scalar/Einstein staging, and contracted-Bianchi divergence
   zero at that surface. This is backed by the GR valuation, Christoffel,
   Riemann, Einstein, selected scalar algebra, and Gate 4 Bianchi receipts.
   It is not a general non-flat continuum Ricci/Einstein theorem.

4. DASHI has sourced-Einstein and cosmology authority boundaries, not sourced
   Einstein or cosmology promotions. Wald records the classical continuum
   theorem shape as external authority; the Temple-Alexander-Vogler Friedmann
   receipt records external instability context. The local promotion flags
   remain false: no W4 matter stress-energy source, no continuum sourced
   Einstein equation, no dark-energy removal, no LCDM falsification, and no
   GRQFT promotion.

Paper 2 is the GR lane instance cited by the Paper 8 tower schema. The
cross-paper tower witness is `canonicalMillenniumTowerGRInstanceReceipt` in
`DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt`; it records the
current finite and authority-bound Gate 4 surfaces while keeping continuum GR
authority construction, cosmology promotion, and GR promotion false.

The paper should use only this ledger when writing abstract, introduction, and
conclusion claims. Any stronger sentence must either cite a newly inhabited
receipt or be moved into the non-claim table below.

## 1. DCHoTT bridge obligations B0.1/B0.2/B0.3 and pro-object semantics

Paper 2 begins from the DCHoTT bridge accounting rather than from a continuum
GR claim. The relevant local index is
`DASHI.Geometry.DCHoTTBridgeObligationIndex`. That module deliberately does
not import a hidden torsion-free theorem from DCHoTT. It names the bridge
objects that must exist before a B0 promotion can be made: a depth-indexed
carrier tower `depthCarrier`, refinement maps, a wave-coherence bound with
monotone decay, and a `proObjectLimit` target. On top of that carrier it
defines two equivalent DASHI-side point languages, `ProCompatibleFamily` and
`ProObjectPoint`, and gives the roundtrip surface
`canonicalB01CompatibleFamilyRoundtripSurface`.

The substantive positive result for B0.1 is now in
`DASHI.Geometry.ProObjectSemantics`. Its
`canonicalConstructedProObjectLimitSurface` realizes the inverse-limit point
surface as compatible families, exposes depth projections, and proves the
projection compatibility law. The same module supplies the proof-relevant
ultrametric/formal-disk scaffolding: `DepthAgreement`, `BallAtDepth`,
symmetry/transitivity for pointwise depth equality, and the depth-zero formal
disk relation. This is the correct object-level starting point for Paper 2:
DASHI has a constructed pro-object semantics on its own finite refinement
tower, not merely an aspirational prose analogy.

The bridge must remain more modest than a DCHoTT theorem. B0.1 still lacks the
transport-smooth sheaf theorem, an analytic completion theorem, the
formal-disk-to-DCHoTT equivalence, and the imported modal/cohesive reflection
authority needed to say that the DASHI pro-object is a DCHoTT formal
D-space/manifold. `DASHI.Geometry.TransportSmoothFormalDiskSurface` sharpens
this boundary. Its receipt
`canonicalTransportSmoothFormalDiskReceipt` constructs clopen ball sites,
canonical depth partitions, terminal sheaf-locality/gluing sockets, a terminal
tangent/first-graded binding, and a DCHoTT formal-disk comparison socket. The
same receipt lists the open obligations explicitly:
`missingRealAnalyticCompletion`, `missingFullSheafTheorem`,
`missingFirstOrderApproximationProof`, `missingDualNumbersEquivalence`,
`missingDCHoTTFormalDiskEquivalence`,
`missingUnconditionalReverseLiftFromImportedImReflection`,
`missingImModalQuotientEqualityReflection`, and
`missingImReflectDASHICohesionAuthority`. Thus B0.1 is a constructed
DASHI-side pro-object plus a precise analytic/cohesive import frontier.

B0.2 is the flat formal-disk/holonomy bridge. The governing target is
`DASHI.Geometry.FlatFormalDiskHolonomySurface`. It separates local discrete
decay data from analytic holonomy conclusions. The module records normed
carrier-fibre and operator-norm sockets, local discrete nonabelian-Stokes
receipt surfaces, wave-coherence uniform-bound data, and
convergence-to-identity bridge data. Its status is still target-only:
`b02HolonomyTargetsOnlyNoB0Promotion`. The named blockers include
`missingNormedCarrierFibreCompletion`,
`missingOperatorNormDefectAdapter`, `missingGeometricSummabilityProof`,
`missingFiniteAreaLoopSurface`, `missingNonabelianStokesBoundaryLaw`,
`missingHolonomyLimitToIdentity`, `missingFormalDiskPathIndependence`,
`missingFlatFormalDiskConnectionCertificate`, and
`missingDCHoTTFormalDiskTrivialisationAdapter`. Paper 2 may therefore claim
that B0.2 has a typed proof target and local decay scaffolding; it may not
claim holonomy convergence, path independence, or a flat DCHoTT formal-disk
trivialization.

B0.3 is the frame/metric/G-structure/Levi-Civita bridge. The controlling file
is `DASHI.Geometry.GStructureLeviCivitaBindingSurface`. It records a
depth-indexed frame tower, compatible metric tower, SO(3,1) reduction socket,
principal-bundle/local-triviality sockets, a local abstract-index
SO(3,1) first-prolongation-zero witness, and a
`canonicalWellenLeviCivitaTheoremSocket`. The positive content is that DASHI
has a typed target route from its pro-object and metric tower to a Lorentzian
G-structure comparison. The boundary is just as important: the residual
blockers include `missingActualDCHoTTGStructureBinding`,
`missingPrincipalBundleSocket`, `missingWeakBGCorrespondenceAuthority`,
`missingCubicalHITBGConstruction`, `missingLocalTrivialitySocket`,
`missingWellenTheoremAuthority`, `missingWellenSocketDischarge`,
`missingTorsionFreeMetricCompatibleAdapter`, and
`missingLeviCivitaUniquenessImport`. The receipt
`canonicalGStructureLeviCivitaBindingReceipt` keeps
`leviCivitaPromoted` false.

The short bridge thesis for this section is therefore:
DASHI has constructed the internal compatible-family/pro-object semantics
needed for B0.1 and has typed B0.2/B0.3 target surfaces. The DCHoTT bridge is
not closed until the transport-smooth/formal-disk equivalence, holonomy
flatness limit, actual G-structure binding, and torsion-free Levi-Civita
authority/import are supplied.

## 2. Finite Lorentzian carrier: valuation metric, Christoffel, Riemann, Ricci, Einstein

The finite GR carrier in this draft is the current Gate 4 Lorentzian
valuation-metric chain. Its first public layer is
`DASHI.Physics.GR.ValuationMetric`. The module fixes
`ValuationCarrier = GL.FactorVec`,
`ValuationDirection = FV.FactorVecTangentDirection`, and
`ValuationScalar = Q.ℚ`. It exports `valuationMetricAt` by reusing
`FV.factorVecValuationDependentP2LorentzMetric` and proves symmetry through
`valuationMetricSymmetric`. The receipt
`canonicalValuationMetricSurface` is small, but it is important: it gives
Paper 2 a concrete finite carrier, tangent-direction type, rational scalar
type, metric operation, and metric symmetry law.

The connection layer is `DASHI.Physics.GR.Christoffel`. It uses the same
carrier, direction, and scalar types and exports `christoffelSymbol` from
`FV.factorVecChristoffelSymbol`. Its key law is
`christoffelSymbolTorsionFree`, supplied by
`FV.factorVecChristoffelTorsionFree`. The receipt
`canonicalChristoffelSurface` threads the valuation metric into the
Christoffel surface. This gives the finite carrier a torsion-free connection
symbol in the local valuation-metric API. It is not yet the selected non-flat
Levi-Civita theorem; that distinction is preserved downstream by the
selected-connection blocker in Gate 4.

The curvature layer is `DASHI.Physics.GR.RiemannTensor`. Its status is
`vacuumZeroTableStagedNonFlatRouteBlocked`. The receipt
`canonicalRiemannTensorSurface` consumes
`NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt`
and exposes a local zero-table Riemann surface:
`riemannTensorComponent = GRNF.grSelectedFiniteRCurvatureAction`. It also
threads `ricciTensorComponent`, `scalarCurvatureComponent`,
`einsteinTensorComponent`, `curvatureAsBracketDefect`,
`jacobiToBianchiBridge`, `finiteRBianchiLaw`, and
`contractedBianchiDivergenceZero`. The positive result is local and finite:
curvature, Ricci, scalar curvature, finite-r Bianchi, and contracted Bianchi
are staged at the selected four-chart zero-table surface.

The Ricci and Einstein steps are made explicit in two places. First,
`DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature` records the
candidate shape from curvature to Riemann to Ricci, including local-fibre
decomposition and a no-global-eager-sweep policy. It also keeps the inherited
first missing condition from the discrete Einstein diagnostic:
`missingCarrierInternalNonFlatConnectionFromCRT`, and records the expected
downstream Bianchi missing ingredient as `missingFiniteRBianchiLaw`. Second,
`DASHI.Physics.GR.EinsteinTensor` packages the selected zero-table Einstein
tensor itself. Its `canonicalEinsteinTensorSurface` reuses
`Riemann.canonicalRiemannTensorSurface`, proves Ricci/scalar/Einstein
agreement with that Riemann surface, gives
`einsteinTensorFromRicciScalar`, and records local vacuum compatibility as
true.

The exact finite statement is narrow but real. DASHI has a concrete
FactorVec-based Lorentzian valuation metric, a torsion-free Christoffel symbol
surface, a selected local zero-table Riemann surface, Ricci contraction and
scalar trace at that surface, an Einstein tensor at that surface, and
contracted-Bianchi divergence zero at that surface. DASHI does not yet have a
general non-flat carrier-internal connection from CRT, a proof that the
selected carrier connection is the non-flat Levi-Civita connection of the
selected metric dependency, a global Ricci sweep, continuum Ricci convergence,
or a sourced Einstein law.

This distinction is also visible in
`DASHI.Physics.Closure.GRDiscreteBianchiFiniteR`. The receipt
`canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt`
states the current Gate 4 dependency cleanly: selected metric compatibility is
available at the adapter layer and the local 4R/Ricci/scalar/2G zero table is
carried as finite arithmetic, but contracted Bianchi remains fail-closed at
`missingCarrierConnectionIsLeviCivita`. Its downstream inspection
`canonicalGRLower6PostBlockerDownstreamInspectionReceipt` keeps the
Ricci/Einstein tower from advancing from lower-six residual arithmetic alone,
because the selected Levi-Civita dependency and source compatibility are not
yet inhabited.

## 3. Sourced Einstein compatibility receipt and Wald authority boundary

The sourced-Einstein story must be handled as a receipt boundary, not as an
equation asserted by prose. The theorem-facing source interface is
`DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`.
The GR-side compatibility surface is `DASHI.Physics.GR.StressEnergyCompatibility`.
Its `canonicalStressEnergyCompatibilitySurface` records the required receipt
name, the expected functions `matterFieldFromW4` and
`stressEnergyTensorFromW4`, and the exact missing-field list from the
Einstein candidate. Its first missing field is
`EEC.missingW4AnchorArtifactReceiptForMatterStress`, and its local FactorVec
blocker is `missingValuationMatterReceiptInterface`.

The separate audit `Docs/W4MatterStressEnergyCompatibilityAudit.md` explains
why this is not a naming issue. The standalone W4 preflight surface has a
Candidate256-only shape, while the theorem-facing Einstein candidate requires
the full W4/W5/DY tuple: W4 anchor, Candidate256 calibration, merged W4/W5 PDF
intake, accepted DY luminosity convention, accepted DY/PDF-backed W4 adequacy,
matter, stress-energy, and definitional compatibility of the matter and
stress-energy functions. In the current repo, the Candidate256 physical
calibration receipt and accepted DY/PDF-backed W4 adequacy are impossible
locally. Therefore the correct current result is an interface alignment and
blocker map, not a matter source.

`DASHI.Physics.Closure.ContractedBianchiMatterClosure` composes the strongest
current local GR and W4-adjacent receipts into one fail-closed record. Its
`canonicalContractedBianchiMatterClosureReceipt` consumes the selected
non-flat scalar algebra receipt, selected four-chart metric compatibility,
selected Levi-Civita/Bianchi/Einstein staging, the lower-six contracted
Bianchi dependency, the Einstein tensor surface, the GR stress-energy boundary
interface, W4 authority obstruction/final ledger receipts, and the Gate 4
YM stress-energy substitution surface. It records `closurePromoted = false`.
The closure boundary says exactly what the paper should say: local zero-table
Einstein tensor plus contracted-Bianchi divergence zero are available as a
vacuum-compatible staging receipt; W4 matter/stress-energy remains blocked;
the first W4 source hole is
`missingW4AnchorArtifactReceiptForMatterStress`; and no new GR theorem is
invented by composing these surfaces.

The external continuum authority boundary is now explicitly captured by
`DASHI.Physics.Closure.WaldGRAuthorityReceipt`. Its
`canonicalWaldGRAuthorityReceipt` records Wald, *General Relativity* (1984),
University of Chicago Press, as the external continuum authority for two
standard boundaries: torsion-free metric-compatible uniqueness of the
Levi-Civita connection, and the sourced Einstein equation boundary
`G_munu = 8pi T_munu`. This is a sourced compatibility receipt in the only
honest sense currently available: it consumes the finite fail-closed
compatibility receipt and records the external authority boundary, while
keeping `acceptedContinuumAuthorityConstructedHere = false`,
`continuumLeviCivitaPromoted = false`, and
`continuumSourcedEinsteinPromoted = false`.

The same Wald receipt lists the continuum blockers:
`missingContinuumSmoothManifoldModel`,
`missingContinuumLorentzianMetricAuthority`,
`missingSelectedNonFlatLeviCivitaInternalProof`,
`missingAuthorityBackedStressEnergyTensor`, and
`missingContinuumEinsteinEquationDerivation`. This is the authority boundary
Paper 2 should use. Wald can justify the target theorem form and the classical
continuum vocabulary; citation to Wald does not turn the finite DASHI
zero-table receipt into a continuum GR theorem or a sourced physical law.

## 4. Gate 4 GR continuum obligation and the Temple/Friedmann instability boundary

`DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt` adds a
cosmology-facing Gate 4 authority boundary on top of the contracted-Bianchi
matter closure and `DASHI.Physics.Closure.WaldGRAuthorityReceipt`. Its
`canonicalFriedmannInstabilitySaddleReceipt` records C. Alexander, B. Temple,
and Z. Vogler, "The instability of critical and underdense Friedmann
spacetimes at the Big Bang as an alternative to dark energy", *Proceedings of
the Royal Society A* 482:20250912 (2026), DOI `10.1098/rspa.2025.0912`, with
the local PDF SHA256
`a105917e23d118c6c41004292c2ecb2a32f042dec738ccd2c380253e0eace6cf`. The
authority-backed statement is only the external theorem boundary: pressureless
Friedmann spacetimes are unstable to radial perturbation in the Einstein-Euler
self-similar variables `xi = r/t`, with the critical Friedmann spacetime an
unstable saddle rest point, so DASHI records
`friedmannUnstableSaddlePoint = true` as authority-backed while also recording
the paired non-promotion flags `darkEnergyRemoved = false` and
`LCDMFalsified = false`, witnessed by
`friedmannInstabilitySaddlePointAuthorityBacked`,
`friedmannInstabilityDoesNotRemoveDarkEnergyHere`, and
`friedmannInstabilityDoesNotFalsifyLCDMHere`.

Temple et al. are therefore structurally consistent external authority for a
continuum-GR instability boundary that Paper 2 may cite alongside Wald; they
are not validation of DASHI, not an internal derivation of the Einstein-Euler
carrier ODE system, and not an identification of `xi` with ultrametric
refinement depth. The receipt preserves the fail-closed cosmology boundary
explicitly: `darkEnergyRemoved = false`, `LCDMFalsified = false`, and
`cosmologyPromoted = false`, witnessed by
`friedmannInstabilityDoesNotRemoveDarkEnergyHere`,
`friedmannInstabilityDoesNotFalsifyLCDMHere`, and
`friedmannInstabilityCosmologyPromotionStillFailClosed`.

This section is intentionally a boundary section, not a cosmology result
section. The admissible Paper 2 sentence is: the Temple/Alexander/Vogler
Friedmann instability result is recorded as external continuum-GR authority
context compatible with the paper's GR boundary vocabulary. The inadmissible
sentences are: DASHI derives the Friedmann instability; DASHI removes dark
energy; DASHI falsifies LCDM; DASHI identifies the Einstein-Euler similarity
variable with a DASHI carrier depth; or DASHI promotes cosmology from the
finite Gate 4 receipts. Those stronger statements are explicitly blocked by
the false fields in the receipt.

Claim-scan note for the Friedmann paragraph: every positive external-authority
sentence is paired with its negative receipt boundary. The only positive
authority claim is the external saddle/instability context witnessed by
`friedmannInstabilitySaddlePointAuthorityBacked`. The paired negative claims
are `friedmannInstabilityDoesNotRemoveDarkEnergyHere`,
`friedmannInstabilityDoesNotFalsifyLCDMHere`, and
`friedmannInstabilityCosmologyPromotionStillFailClosed`. No occurrence in this
draft states dark-energy removal, LCDM falsification, DASHI derivation of the
Friedmann result, or cosmology promotion as a DASHI theorem.

## 5. Continuum Levi-Civita obligation and B0 bridge as fail-closed boundary

The continuum Levi-Civita obligation is controlled by two distinct surfaces.
The first is `DASHI.Geometry.LeviCivitaBridge`. That bridge imports the real
DCHoTT `G-structures` socket through `DASHI.Geometry.DCHoTTImportShim`, links
the existing flat DASHI prerequisite
`FlatLC.canonicalGRConcreteLeviCivitaSurface`, and threads the downstream
`DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic`. Its receipt
`canonicalLeviCivitaBridgeReceipt` sets the first open obligation to
`missingB0GeometricEmergence`, records that B0 geometric emergence is
postulated there as a theorem target, and states
`noEinsteinPromotionFromThisBridge = true`.

The second is
`DASHI.Geometry.GStructureLeviCivitaBindingSurface`, which supplies the more
detailed B0.3 route. It can record a frame/metric tower, SO(3,1) reduction,
local SO(3,1) first-prolongation-zero evidence, and a Wellen theorem socket.
It cannot yet import a DCHoTT torsion-free G-structure theorem, because the
local DCHoTT clone exposes `G-structures` but not an importable
`TorsionFreeGStructure` or Levi-Civita uniqueness identifier. This is why the
B0 bridge is a fail-closed boundary: it exposes exactly where the transition
from DASHI finite/pro-object geometry to continuum-style Levi-Civita geometry
must happen, and it forbids downstream GR promotion until that transition is
inhabited.

This boundary also matches the repository-wide status documents.
`Docs/CompressedGRQFTImportRoadmap.md` records that the local DCHoTT clone and
flat import shim are present, that the first `G-structures` bridge socket is
live, that B0 has a four-part obligation index, and that B0.1 pro-object
semantics have been constructed. It also records the critical limitation:
there is no imported DCHoTT theorem, no torsion-free/Levi-Civita
specialization, and no formal-disk equivalence. The same roadmap documents the
flag boundary: local `--cohesion` and `--cubical` work cannot be collapsed into
one module in the current setup, so cohesive carrier/DCHoTT modules and
cubical quotient/path modules must meet through proof-erasing interfaces and
typed postulate sockets.

For Paper 2, the correct continuum statement is therefore conditional. If the
B0.1 transport-smooth/formal-disk equivalence is supplied, if B0.2 holonomy
flatness/path-independence is supplied, and if B0.3 binds the frame/metric
tower to an actual DCHoTT G-structure plus torsion-free Levi-Civita theorem,
then the local finite GR receipts can be read as staged inputs to a continuum
Levi-Civita bridge. Until then, the finite valuation-metric/Christoffel/Riemann
chain remains a finite Gate 4 staging surface.

This is not a weakness in the paper; it is the point of the paper's governance.
The B0 bridge converts a vague continuum-limit hope into named obligations:
formal-disk equivalence, analytic completion, holonomy limit, SO(3,1)
G-structure binding, Wellen theorem authority, and Levi-Civita import. The
paper's claim boundary is fail-closed because no downstream claim can cross
that boundary by narrative pressure. It must cross by an inhabited receipt.

## 6. What This Paper Does Not Claim

| Prohibited claim | Paper 2 status | Governing evidence |
|---|---|---|
| Continuum GR theorem proved | Not claimed. The finite zero-table receipts are local Gate 4 staging surfaces, while the continuum bridge remains an obligation boundary. | `DASHI.Physics.Closure.WaldGRAuthorityReceipt.waldGRAuthorityContinuumLeviCivitaStillFailClosed`; `DASHI.Geometry.LeviCivitaBridge.LeviCivitaBridgeReceipt.noEinsteinPromotionFromThisBridge-v`; `DASHI.Geometry.GStructureLeviCivitaBindingSurface.canonicalLeviCivitaNotPromoted`. |
| Non-flat sourced Einstein equation proved | Not claimed. The sourced route is an interface target and remains blocked by W4 matter/stress-energy and selected-connection requirements. | `DASHI.Physics.Closure.ContractedBianchiMatterClosure.sourcedEinsteinCompatibilityStillFailClosed`; `DASHI.Physics.GR.StressEnergyCompatibility.canonicalStressEnergyCompatibilitySurface`; `DASHI.Physics.Closure.EinsteinEquationCandidate.missingW4AnchorArtifactReceiptForMatterStress`. |
| Contracted-Bianchi promotion closed | Not claimed. The local Einstein tensor has zero-table contracted-Bianchi divergence, but the Gate 4 contracted-Bianchi promotion receipt remains blocked at the selected carrier connection being Levi-Civita. | `DASHI.Physics.GR.EinsteinTensor.EinsteinTensorSurface.contractedBianchiDivergenceZero`; `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.grGate4ContractedBianchiStillNotPromoted`; `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.grGate4ContractedBianchiSelectedConnectionBlocker`. |
| W4 matter source constructed | Not claimed. The first theorem-facing source hole remains the W4 anchor artifact receipt, and the local FactorVec matter interface remains blocked. | `DASHI.Physics.Closure.EinsteinEquationCandidate.missingW4AnchorArtifactReceiptForMatterStress`; `DASHI.Physics.GR.StressEnergyCompatibility.canonicalStressEnergyBoundaryInterface`; `DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface.missingValuationMatterReceiptInterface`. |
| DCHoTT manifold or formal-disk equivalence proved | Not claimed. B0.1 has constructed DASHI-side pro-object semantics and obligation sockets, not an imported DCHoTT formal D-space/manifold theorem. | `DASHI.Geometry.ProObjectSemantics.canonicalConstructedProObjectLimitSurface`; `DASHI.Geometry.TransportSmoothFormalDiskSurface.canonicalTransportSmoothFormalDiskReceipt`; blockers `DASHI.Geometry.TransportSmoothFormalDiskSurface.missingDCHoTTFormalDiskEquivalence` and `DASHI.Geometry.TransportSmoothFormalDiskSurface.missingImReflectDASHICohesionAuthority`. |
| Holonomy flatness or path independence proved | Not claimed. B0.2 is target-only and records no B0 promotion. | `DASHI.Geometry.FlatFormalDiskHolonomySurface.b02HolonomyTargetsOnlyNoB0Promotion`; blockers `DASHI.Geometry.FlatFormalDiskHolonomySurface.missingHolonomyLimitToIdentity` and `DASHI.Geometry.FlatFormalDiskHolonomySurface.missingFormalDiskPathIndependence`. |
| Dark energy removed or LCDM falsified | Not claimed. The Temple-Alexander-Vogler result is recorded only as an external Friedmann-instability authority boundary. | `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.friedmannInstabilityDoesNotRemoveDarkEnergyHere`; `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.friedmannInstabilityDoesNotFalsifyLCDMHere`; `DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.friedmannInstabilityCosmologyPromotionStillFailClosed`. |
| GRQFT or cross-paper terminal promotion | Not claimed. Paper 2 is a geometry and Gate 4 staging map and does not borrow terminal composition status from later papers. | `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.canonicalGRDiscreteBianchiFiniteRUnsupportedClaims`; `DASHI.Physics.Closure.GRDiscreteBianchiFiniteR.unsupportedGRQFTPromotionClaim`; `Docs/Papers2To7CriticalPathStatus.md`. |

The strongest admissible Paper 2 wording is: DASHI currently supplies a
typed, fail-closed geometry-to-Gate-4 GR staging map with inhabited finite
zero-table receipts, explicit DCHoTT bridge obligations, and external Wald and
Friedmann authority boundaries. It does not promote continuum GR, sourced
Einstein equations, cosmology, or GRQFT.

## 7. Blocker map for Paper 3 non-flat GR promotion

Paper 3 may attempt non-flat GR promotion only after Paper 2's geometry
boundary is respected. The current blocker map is as follows.

First, the B0 bridge blockers must be discharged or explicitly carried as
assumptions. B0.1 still needs transport-smooth sheaf/locality strength beyond
the constructed pro-object semantics, analytic completion, DCHoTT formal-disk
equivalence, and `Im`/modal reflection authority. B0.2 still needs a real
operator-norm transport-defect adapter, geometric summability, nonabelian
Stokes boundary law, holonomy limit to identity, formal-disk path
independence, and DCHoTT formal-disk trivialization. B0.3 still needs actual
DCHoTT G-structure binding, principal-bundle/local-triviality authority where
not merely socketed, WeakBG/Wellen theorem authority, torsion-free
metric-compatible specialization, and Levi-Civita uniqueness import.

Second, the finite non-flat GR chain must move beyond the local zero-table
surface. `Docs/GRNonFlatNextThread.md` names the exact older blocker list:
`missingCarrierInternalNonFlatConnectionFromCRT`,
`missingCurvatureToRicciContraction`, `missingFiniteRBianchiWitness`,
`missingDiscreteEinsteinTensorLaw`,
`missingW4MatterStressEnergyInterfaceReceipt`, `missingMetricErrorBound`,
`missingConnectionErrorBound`, `missingWeakFieldNewtonianPotential`,
`missingW4MassSource`, `missingSchwarzschildMetricMatch`,
`missingEinsteinTensorContinuity`, and
`missingW2BridgeOrObstructionResolution`. Newer Gate 4 receipts have narrowed
some local finite arithmetic and local-fibre surfaces, but they have not
removed the central selected-connection and source blockers. The live Gate 4
selected-chain blocker is still `missingCarrierConnectionIsLeviCivita` at the
contracted-Bianchi dependency, and the sourced route still waits for the W4
matter/stress-energy receipt plus a discrete GR equation law.

Third, W4 and Candidate256 authority must be supplied before any sourced
Einstein equation can be promoted. The current theorem-facing receipt is
`EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`, and the
current first missing field is
`missingW4AnchorArtifactReceiptForMatterStress`. The W4-side authority blocker
also includes `missingCandidate256CalibrationReceiptForMatterInterface`.
Without W4 anchor evidence, accepted DY/PDF-backed W4 adequacy, Candidate256
physical calibration, matter-field construction, stress-energy tensor
construction, and the consumer/law in
`W4DiscreteGREquationLawObligation`, Paper 3 cannot state
`G_munu = 8pi T_munu` as a DASHI theorem.

Fourth, the continuum and known-limit checks must be explicit. A Paper 3
non-flat GR promotion needs metric and connection error bounds, Einstein tensor
continuity, Ricci convergence or a precise finite-to-continuum replacement,
Schwarzschild or weak-field recovery where claimed, Newtonian normalization
and physical-unit authority where `G_N` appears, and a boundary to W2
bridge/rate assumptions. Wald authority can be cited for the classical theorem
shape, but the repo still needs the DASHI-to-continuum bridge and the internal
selected non-flat Levi-Civita proof.

Fifth, cross-paper dependencies must stay out of the proof unless inhabited.
`Docs/Papers2To7CriticalPathStatus.md` records that the physical Hilbert/Stone
route still lacks quotient projection, quotient inner product,
completion/topology, reversible traversal group, strong continuity, Stone
bundle, and self-adjoint generator data. It also records that Paper 7
composition remains blocked on Paper 3 Hilbert/self-adjointness, Paper 4 YM,
Paper 5 continuum/GR, DR/SM matching, W4/Candidate256 authority, and external
Clay/community acceptance. A Paper 3 non-flat GR result therefore cannot borrow
terminal composition status as evidence; it must independently inhabit the
named GR bridge receipts.

The promotion rule for Paper 3 should be simple. A non-flat GR statement is
admissible only when its exact receipt exists: selected non-flat
Levi-Civita/metric compatibility, curvature-as-connection defect, finite-r
Bianchi, Ricci/scalar contraction, Einstein tensor law, W4 stress-energy
source, sourced equation law, continuum/error bridge, and the relevant
external authority receipts. Until then, Paper 2's honest output is a complete
geometry/GR staging map: constructed pro-object semantics, typed B0 bridge
obligations, finite Lorentzian valuation-metric tensor staging, Wald authority
boundary, and a blocker map precise enough for Paper 3 to execute without
silent promotion.
