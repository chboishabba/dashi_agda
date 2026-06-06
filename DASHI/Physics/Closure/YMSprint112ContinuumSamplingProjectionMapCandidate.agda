module DASHI.Physics.Closure.YMSprint112ContinuumSamplingProjectionMapCandidate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint111FiniteContinuumEmbeddingProjectionMaps
  as Maps111
import DASHI.Physics.Closure.YMSprint111GaugeQuotientPhysicalSectorCompatibility
  as Quotient111
import DASHI.Physics.Closure.YMSprint110RecoveryCoreDensityEnergyLimsup
  as Recovery110

------------------------------------------------------------------------
-- Sprint 112 continuum-to-finite sampling/projection map candidate.
--
-- This module records a concrete candidate recipe for P_a.  It names the
-- input surface, local representative choice, plaquette/edge holonomy
-- sampling, finite lattice vector assembly, finite physical projection, and
-- quotient output.  It is an inhabited analytic-obligation ledger only:
-- construction, representative independence, compatibility, convergence,
-- energy-limsup feeding, and Clay promotion remain false.

samplingProjectionCandidateRecorded : Bool
samplingProjectionCandidateRecorded = true

plaquetteHolonomySamplingRecorded : Bool
plaquetteHolonomySamplingRecorded = true

finitePhysicalProjectionRecipeRecorded : Bool
finitePhysicalProjectionRecipeRecorded = true

recoveryConsumerInterfaceRecorded : Bool
recoveryConsumerInterfaceRecorded = true

obligationLedgerRecorded : Bool
obligationLedgerRecorded = true

samplingProjectionMapConstructedHere : Bool
samplingProjectionMapConstructedHere = false

quotientRepresentativeIndependenceProvedHere : Bool
quotientRepresentativeIndependenceProvedHere = false

finitePhysicalProjectionCompatibilityProvedHere : Bool
finitePhysicalProjectionCompatibilityProvedHere = false

recoverySamplingConvergenceProvedHere : Bool
recoverySamplingConvergenceProvedHere = false

energyLimsupFedHere : Bool
energyLimsupFedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sprintNumber : Nat
sprintNumber = 112

moduleSourcePath : String
moduleSourcePath =
  "DASHI/Physics/Closure/YMSprint112ContinuumSamplingProjectionMapCandidate.agda"

maps111SourcePath : String
maps111SourcePath =
  "DASHI/Physics/Closure/YMSprint111FiniteContinuumEmbeddingProjectionMaps.agda"

quotient111SourcePath : String
quotient111SourcePath =
  "DASHI/Physics/Closure/YMSprint111GaugeQuotientPhysicalSectorCompatibility.agda"

recovery110SourcePath : String
recovery110SourcePath =
  "DASHI/Physics/Closure/YMSprint110RecoveryCoreDensityEnergyLimsup.agda"

continuumInputSurfaceStatementText : String
continuumInputSurfaceStatementText =
  "Continuum input surface for P_a candidate: a finite-energy physical vector u in the Sprint111 projection input D(q) subset H_phys, with the Sprint110 recovery-core convention available as a consumer surface."

localGaugeRepresentativeStatementText : String
localGaugeRepresentativeStatementText =
  "Representative step: choose a local gauge representative A of u on each chart of the finite volume window before sampling; this is a recipe step only, because independence under continuum gauge-equivalent representative changes is not proved here."

plaquetteHolonomySamplingStatementText : String
plaquetteHolonomySamplingStatementText =
  "Holonomy sampling step: for lattice spacing a, sample edge parallel transports U_e(A) by path-ordered exponentials of A along lattice edges and plaquette holonomies U_p(A) around elementary plaquettes, using the shared Sprint111 renormalization convention."

finiteLatticeVectorStatementText : String
finiteLatticeVectorStatementText =
  "Finite lattice vector step: assemble the sampled edge and plaquette holonomy data into a finite lattice vector x_a(A) in the finite carrier named by Sprint111, before physical projection and gauge quotienting."

finitePhysicalProjectionRecipeStatementText : String
finitePhysicalProjectionRecipeStatementText =
  "Finite physical projection recipe: apply Pi_a,phys to x_a(A), then pass to the finite gauge quotient [Pi_a,phys x_a(A)] so the candidate output lands in H_a,phys / gauge."

samplingProjectionCandidateStatementText : String
samplingProjectionCandidateStatementText =
  "Candidate P_a recipe: continuum finite-energy vector u -> local gauge representative A -> edge and plaquette holonomy samples -> finite lattice vector x_a(A) -> finite physical projection Pi_a,phys x_a(A) -> finite gauge quotient [Pi_a,phys x_a(A)]."

sourcePathsAndImportsStatementText : String
sourcePathsAndImportsStatementText =
  "Sources: Sprint111 map surface in DASHI/Physics/Closure/YMSprint111FiniteContinuumEmbeddingProjectionMaps.agda, Sprint111 quotient/physical-sector compatibility in DASHI/Physics/Closure/YMSprint111GaugeQuotientPhysicalSectorCompatibility.agda, and Sprint110 recovery consumer obligations in DASHI/Physics/Closure/YMSprint110RecoveryCoreDensityEnergyLimsup.agda."

recoveryConsumerInterfaceStatementText : String
recoveryConsumerInterfaceStatementText =
  "Recovery consumer interface: if later proved representative-independent, physical-sector compatible, convergent under E_a or I_a, and energy-limsup admissible, this P_a candidate can feed the Sprint110 recovery sampling lane S_a and the limsup criterion limsup_{a -> 0} q_a(S_a u) <= q(u)."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint112 records a concrete P_a sampling/projection candidate and exact obligations only; no construction theorem, quotient independence theorem, compatibility theorem, recovery convergence theorem, energy-limsup feed, Mosco convergence, spectral gap, or Clay Yang-Mills promotion is proved here."

constructionBlockerText : String
constructionBlockerText =
  "Exact blocker A: the local representative, path-ordered holonomy sampling, finite vector assembly, projection, and quotient steps are recorded as a candidate recipe, not as a DASHI-native total map P_a with domain, codomain, and operator bounds."

representativeIndependenceBlockerText : String
representativeIndependenceBlockerText =
  "Exact blocker B: no proof shows that changing the local continuum gauge representative A changes the sampled finite vector only by a finite gauge transformation before quotienting."

physicalProjectionCompatibilityBlockerText : String
physicalProjectionCompatibilityBlockerText =
  "Exact blocker C: no proof shows that holonomy sampling commutes with Pi_phys and Pi_a,phys or preserves the physical sector after finite projection."

recoveryConvergenceBlockerText : String
recoveryConvergenceBlockerText =
  "Exact blocker D: no proof shows E_a(P_a u) -> u, I_a(S_a u) -> u, or any Sprint110 strong recovery convergence statement for this candidate."

energyLimsupBlockerText : String
energyLimsupBlockerText =
  "Exact blocker E: no proof feeds the sampled finite vector into the Sprint110 limsup inequality limsup_{a -> 0} q_a(S_a u) <= q(u)."

normalizationBlockerText : String
normalizationBlockerText =
  "Exact blocker F: the holonomy-to-field-strength scaling, coupling normalization g(a), field-strength normalization Z(a), finite-volume exhaustion, and quotient norm comparison are not proved consistent in one a-window."

data SamplingProjectionLane : Set where
  continuum-input-surface :
    SamplingProjectionLane
  local-gauge-representative :
    SamplingProjectionLane
  plaquette-holonomy-sampling :
    SamplingProjectionLane
  finite-lattice-vector :
    SamplingProjectionLane
  finite-physical-projection :
    SamplingProjectionLane
  finite-gauge-quotient-output :
    SamplingProjectionLane
  recovery-consumer-interface :
    SamplingProjectionLane
  obligation-ledger :
    SamplingProjectionLane
  receipt-lane :
    SamplingProjectionLane

data SamplingProjectionStatus : Set where
  recorded-inhabited :
    SamplingProjectionStatus
  imported-sprint111-map-surface :
    SamplingProjectionStatus
  imported-sprint111-quotient-surface :
    SamplingProjectionStatus
  imported-sprint110-recovery-surface :
    SamplingProjectionStatus
  candidate-recipe-recorded :
    SamplingProjectionStatus
  analytic-obligation-recorded :
    SamplingProjectionStatus
  exact-blocker :
    SamplingProjectionStatus
  theorem-open :
    SamplingProjectionStatus
  fail-closed-nonpromotion :
    SamplingProjectionStatus

data AnalyticObligationKind : Set where
  construct-total-sampling-projection-map :
    AnalyticObligationKind
  prove-representative-independence :
    AnalyticObligationKind
  prove-physical-projection-compatibility :
    AnalyticObligationKind
  prove-recovery-sampling-convergence :
    AnalyticObligationKind
  feed-energy-limsup :
    AnalyticObligationKind
  fix-renormalized-normalization :
    AnalyticObligationKind

canonicalSamplingProjectionLanes : List SamplingProjectionLane
canonicalSamplingProjectionLanes =
  continuum-input-surface
  ∷ local-gauge-representative
  ∷ plaquette-holonomy-sampling
  ∷ finite-lattice-vector
  ∷ finite-physical-projection
  ∷ finite-gauge-quotient-output
  ∷ recovery-consumer-interface
  ∷ obligation-ledger
  ∷ receipt-lane
  ∷ []

record ContinuumInputSurface : Setω where
  constructor mkContinuumInputSurface
  field
    lane :
      SamplingProjectionLane
    statement :
      String
    continuumInputSymbol :
      String
    finiteEnergyDomainSymbol :
      String
    importedMapsReceipt :
      Maps111.YMSprint111FiniteContinuumEmbeddingProjectionMapsReceipt
    mapsSourcePath :
      String
    projectionInputRecorded :
      Bool
    status :
      SamplingProjectionStatus

record HolonomySamplingRecipe : Set where
  constructor mkHolonomySamplingRecipe
  field
    representativeLane :
      SamplingProjectionLane
    samplingLane :
      SamplingProjectionLane
    representativeStatement :
      String
    samplingStatement :
      String
    representativeSymbol :
      String
    edgeHolonomySymbol :
      String
    plaquetteHolonomySymbol :
      String
    pathOrderedExponentialsRequired :
      Bool
    sharedRenormalizationConvention :
      String
    plaquetteSamplingRecorded :
      Bool
    representativeIndependenceProvedHere :
      Bool
    representativeIndependenceProvedHereIsFalse :
      representativeIndependenceProvedHere ≡ false
    status :
      SamplingProjectionStatus

record FiniteProjectionStep : Set where
  constructor mkFiniteProjectionStep
  field
    latticeVectorLane :
      SamplingProjectionLane
    physicalProjectionLane :
      SamplingProjectionLane
    quotientOutputLane :
      SamplingProjectionLane
    latticeVectorStatement :
      String
    projectionStatement :
      String
    finiteVectorSymbol :
      String
    finiteProjectionSymbol :
      String
    finiteQuotientOutputSymbol :
      String
    importedQuotientReceipt :
      Quotient111.ModuleReceipt
    quotientSourcePath :
      String
    finitePhysicalProjectionRecipeRecordedFlag :
      Bool
    projectionCompatibilityProvedHere :
      Bool
    projectionCompatibilityProvedHereIsFalse :
      projectionCompatibilityProvedHere ≡ false
    status :
      SamplingProjectionStatus

record RecoveryConsumerInterface : Setω where
  constructor mkRecoveryConsumerInterface
  field
    lane :
      SamplingProjectionLane
    statement :
      String
    importedRecoveryReceipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    recoverySourcePath :
      String
    samplingLaneSymbol :
      String
    energyLimsupInequality :
      String
    consumerInterfaceRecorded :
      Bool
    recoveryConvergenceProvedHere :
      Bool
    recoveryConvergenceProvedHereIsFalse :
      recoveryConvergenceProvedHere ≡ false
    energyLimsupFedHereFlag :
      Bool
    energyLimsupFedHereFlagIsFalse :
      energyLimsupFedHereFlag ≡ false
    status :
      SamplingProjectionStatus

record AnalyticObligation : Set where
  constructor mkAnalyticObligation
  field
    kind :
      AnalyticObligationKind
    lane :
      SamplingProjectionLane
    statement :
      String
    sourcePath :
      String
    mustCloseBeforeConstructionTheorem :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      SamplingProjectionStatus

record BlockerLedger : Set where
  constructor mkBlockerLedger
  field
    lane :
      SamplingProjectionLane
    constructionBlocker :
      String
    representativeIndependenceBlocker :
      String
    physicalProjectionCompatibilityBlocker :
      String
    recoveryConvergenceBlocker :
      String
    energyLimsupBlocker :
      String
    normalizationBlocker :
      String
    allBlockersConcrete :
      Bool
    theoremStillOpen :
      Bool
    blockers :
      List String
    status :
      SamplingProjectionStatus

record TheoremFlagBoundary : Set where
  constructor mkTheoremFlagBoundary
  field
    boundaryStatement :
      String
    samplingProjectionMapConstructedHereFlag :
      Bool
    samplingProjectionMapConstructedHereFlagIsFalse :
      samplingProjectionMapConstructedHereFlag ≡ false
    quotientRepresentativeIndependenceProvedHereFlag :
      Bool
    quotientRepresentativeIndependenceProvedHereFlagIsFalse :
      quotientRepresentativeIndependenceProvedHereFlag ≡ false
    finitePhysicalProjectionCompatibilityProvedHereFlag :
      Bool
    finitePhysicalProjectionCompatibilityProvedHereFlagIsFalse :
      finitePhysicalProjectionCompatibilityProvedHereFlag ≡ false
    recoverySamplingConvergenceProvedHereFlag :
      Bool
    recoverySamplingConvergenceProvedHereFlagIsFalse :
      recoverySamplingConvergenceProvedHereFlag ≡ false
    energyLimsupFedHereFlag :
      Bool
    energyLimsupFedHereFlagIsFalse :
      energyLimsupFedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      SamplingProjectionStatus

record SamplingProjectionCandidateReceipt : Setω where
  constructor mkSamplingProjectionCandidateReceipt
  field
    sprint :
      Nat
    sourcePath :
      String
    continuumInput :
      ContinuumInputSurface
    holonomySampling :
      HolonomySamplingRecipe
    finiteProjection :
      FiniteProjectionStep
    recoveryConsumer :
      RecoveryConsumerInterface
    analyticObligations :
      List AnalyticObligation
    blockerLedger :
      BlockerLedger
    theoremFlagBoundary :
      TheoremFlagBoundary
    candidateRecipe :
      String
    sourcePathsAndImports :
      String
    receiptStatements :
      List String
    samplingProjectionCandidateRecordedFlag :
      Bool
    plaquetteHolonomySamplingRecordedFlag :
      Bool
    finitePhysicalProjectionRecipeRecordedFlag :
      Bool
    recoveryConsumerInterfaceRecordedFlag :
      Bool
    obligationLedgerRecordedFlag :
      Bool
    samplingProjectionMapConstructedHereFlag :
      Bool
    samplingProjectionMapConstructedHereFlagIsFalse :
      samplingProjectionMapConstructedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open SamplingProjectionCandidateReceipt public

canonicalContinuumInputSurface : ContinuumInputSurface
canonicalContinuumInputSurface =
  mkContinuumInputSurface
    continuum-input-surface
    continuumInputSurfaceStatementText
    "u"
    "D(q) subset H_phys"
    Maps111.canonicalReceipt
    maps111SourcePath
    Maps111.projectionMapSpecificationRecorded
    imported-sprint111-map-surface

canonicalHolonomySamplingRecipe : HolonomySamplingRecipe
canonicalHolonomySamplingRecipe =
  mkHolonomySamplingRecipe
    local-gauge-representative
    plaquette-holonomy-sampling
    localGaugeRepresentativeStatementText
    plaquetteHolonomySamplingStatementText
    "A"
    "U_e(A)"
    "U_p(A)"
    true
    Maps111.renormalizationConventionStatementText
    plaquetteHolonomySamplingRecorded
    quotientRepresentativeIndependenceProvedHere
    refl
    candidate-recipe-recorded

canonicalFiniteProjectionStep : FiniteProjectionStep
canonicalFiniteProjectionStep =
  mkFiniteProjectionStep
    finite-lattice-vector
    finite-physical-projection
    finite-gauge-quotient-output
    finiteLatticeVectorStatementText
    finitePhysicalProjectionRecipeStatementText
    "x_a(A)"
    "Pi_a,phys"
    "[Pi_a,phys x_a(A)]"
    Quotient111.canonicalReceipt
    quotient111SourcePath
    finitePhysicalProjectionRecipeRecorded
    finitePhysicalProjectionCompatibilityProvedHere
    refl
    imported-sprint111-quotient-surface

canonicalRecoveryConsumerInterface : RecoveryConsumerInterface
canonicalRecoveryConsumerInterface =
  mkRecoveryConsumerInterface
    recovery-consumer-interface
    recoveryConsumerInterfaceStatementText
    Recovery110.canonicalReceipt
    recovery110SourcePath
    "S_a u"
    Recovery110.canonicalReceiptEnergyLimsupInequality
    recoveryConsumerInterfaceRecorded
    recoverySamplingConvergenceProvedHere
    refl
    energyLimsupFedHere
    refl
    imported-sprint110-recovery-surface

canonicalAnalyticObligations : List AnalyticObligation
canonicalAnalyticObligations =
  mkAnalyticObligation
    construct-total-sampling-projection-map
    continuum-input-surface
    constructionBlockerText
    maps111SourcePath
    true
    samplingProjectionMapConstructedHere
    refl
    exact-blocker
  ∷ mkAnalyticObligation
    prove-representative-independence
    local-gauge-representative
    representativeIndependenceBlockerText
    quotient111SourcePath
    true
    quotientRepresentativeIndependenceProvedHere
    refl
    exact-blocker
  ∷ mkAnalyticObligation
    prove-physical-projection-compatibility
    finite-physical-projection
    physicalProjectionCompatibilityBlockerText
    quotient111SourcePath
    true
    finitePhysicalProjectionCompatibilityProvedHere
    refl
    exact-blocker
  ∷ mkAnalyticObligation
    prove-recovery-sampling-convergence
    recovery-consumer-interface
    recoveryConvergenceBlockerText
    recovery110SourcePath
    true
    recoverySamplingConvergenceProvedHere
    refl
    exact-blocker
  ∷ mkAnalyticObligation
    feed-energy-limsup
    recovery-consumer-interface
    energyLimsupBlockerText
    recovery110SourcePath
    true
    energyLimsupFedHere
    refl
    exact-blocker
  ∷ mkAnalyticObligation
    fix-renormalized-normalization
    obligation-ledger
    normalizationBlockerText
    maps111SourcePath
    true
    false
    refl
    exact-blocker
  ∷ []

canonicalBlockerLedger : BlockerLedger
canonicalBlockerLedger =
  mkBlockerLedger
    obligation-ledger
    constructionBlockerText
    representativeIndependenceBlockerText
    physicalProjectionCompatibilityBlockerText
    recoveryConvergenceBlockerText
    energyLimsupBlockerText
    normalizationBlockerText
    true
    true
    (constructionBlockerText
     ∷ representativeIndependenceBlockerText
     ∷ physicalProjectionCompatibilityBlockerText
     ∷ recoveryConvergenceBlockerText
     ∷ energyLimsupBlockerText
     ∷ normalizationBlockerText
     ∷ [])
    exact-blocker

canonicalTheoremFlagBoundary : TheoremFlagBoundary
canonicalTheoremFlagBoundary =
  mkTheoremFlagBoundary
    nonPromotionBoundaryText
    samplingProjectionMapConstructedHere
    refl
    quotientRepresentativeIndependenceProvedHere
    refl
    finitePhysicalProjectionCompatibilityProvedHere
    refl
    recoverySamplingConvergenceProvedHere
    refl
    energyLimsupFedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalSamplingProjectionCandidateReceipt :
  SamplingProjectionCandidateReceipt
canonicalSamplingProjectionCandidateReceipt =
  mkSamplingProjectionCandidateReceipt
    sprintNumber
    moduleSourcePath
    canonicalContinuumInputSurface
    canonicalHolonomySamplingRecipe
    canonicalFiniteProjectionStep
    canonicalRecoveryConsumerInterface
    canonicalAnalyticObligations
    canonicalBlockerLedger
    canonicalTheoremFlagBoundary
    samplingProjectionCandidateStatementText
    sourcePathsAndImportsStatementText
    (continuumInputSurfaceStatementText
     ∷ localGaugeRepresentativeStatementText
     ∷ plaquetteHolonomySamplingStatementText
     ∷ finiteLatticeVectorStatementText
     ∷ finitePhysicalProjectionRecipeStatementText
     ∷ samplingProjectionCandidateStatementText
     ∷ recoveryConsumerInterfaceStatementText
     ∷ sourcePathsAndImportsStatementText
     ∷ constructionBlockerText
     ∷ representativeIndependenceBlockerText
     ∷ physicalProjectionCompatibilityBlockerText
     ∷ recoveryConvergenceBlockerText
     ∷ energyLimsupBlockerText
     ∷ normalizationBlockerText
     ∷ nonPromotionBoundaryText
     ∷ [])
    samplingProjectionCandidateRecorded
    plaquetteHolonomySamplingRecorded
    finitePhysicalProjectionRecipeRecorded
    recoveryConsumerInterfaceRecorded
    obligationLedgerRecorded
    samplingProjectionMapConstructedHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt : SamplingProjectionCandidateReceipt
canonicalReceipt =
  canonicalSamplingProjectionCandidateReceipt

canonicalSamplingProjectionMapConstructedHereIsFalse :
  samplingProjectionMapConstructedHereFlag canonicalReceipt ≡ false
canonicalSamplingProjectionMapConstructedHereIsFalse =
  refl

canonicalQuotientRepresentativeIndependenceProvedHereIsFalse :
  TheoremFlagBoundary.quotientRepresentativeIndependenceProvedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalQuotientRepresentativeIndependenceProvedHereIsFalse =
  refl

canonicalFinitePhysicalProjectionCompatibilityProvedHereIsFalse :
  TheoremFlagBoundary.finitePhysicalProjectionCompatibilityProvedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalFinitePhysicalProjectionCompatibilityProvedHereIsFalse =
  refl

canonicalRecoverySamplingConvergenceProvedHereIsFalse :
  TheoremFlagBoundary.recoverySamplingConvergenceProvedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalRecoverySamplingConvergenceProvedHereIsFalse =
  refl

canonicalEnergyLimsupFedHereIsFalse :
  TheoremFlagBoundary.energyLimsupFedHereFlag
    (theoremFlagBoundary canonicalReceipt) ≡ false
canonicalEnergyLimsupFedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalHolonomyRepresentativeIndependenceNotProved :
  HolonomySamplingRecipe.representativeIndependenceProvedHere
    (holonomySampling canonicalReceipt) ≡ false
canonicalHolonomyRepresentativeIndependenceNotProved =
  refl

canonicalFiniteProjectionCompatibilityNotProved :
  FiniteProjectionStep.projectionCompatibilityProvedHere
    (finiteProjection canonicalReceipt) ≡ false
canonicalFiniteProjectionCompatibilityNotProved =
  refl

canonicalRecoveryConvergenceNotProved :
  RecoveryConsumerInterface.recoveryConvergenceProvedHere
    (recoveryConsumer canonicalReceipt) ≡ false
canonicalRecoveryConvergenceNotProved =
  refl

canonicalRecoveryEnergyLimsupNotFed :
  RecoveryConsumerInterface.energyLimsupFedHereFlag
    (recoveryConsumer canonicalReceipt) ≡ false
canonicalRecoveryEnergyLimsupNotFed =
  refl
