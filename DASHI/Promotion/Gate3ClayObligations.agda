module DASHI.Promotion.Gate3ClayObligations where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry

infixr 5 _++_

_++_ : {A : Set₁} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

rowCount : {A : Set₁} → List A → Nat
rowCount [] = zero
rowCount (_ ∷ xs) = suc (rowCount xs)

------------------------------------------------------------------------
-- Gate 3 / Clay promotion obligations.
--
-- This module is a promotion work index.  It is intentionally not a proof of
-- Gate 3 closure, Navier-Stokes regularity, or Yang-Mills mass gap.  It names
-- the rows that must become inhabited, source-bound, and validated before the
-- corresponding promotion guard may flip.

data ClayPromotionLane : Set where
  gate3ClosureLane : ClayPromotionLane
  navierStokesClayLane : ClayPromotionLane
  yangMillsClayLane : ClayPromotionLane
  terminalClayUnificationLane : ClayPromotionLane

data PromotionTarget : Set where
  gate3DensityProof : PromotionTarget
  gate3MoscoLiminf : PromotionTarget
  gate3MoscoRecovery : PromotionTarget
  gate3NoSpectralPollution : PromotionTarget
  gate3SpectralTransfer : PromotionTarget
  gate3MassShellIdentification : PromotionTarget
  navierStokesWeakSolutionClass : PromotionTarget
  navierStokesStrongSolutionClass : PromotionTarget
  navierStokesPressureReconstruction : PromotionTarget
  navierStokesNonlinearTermPassage : PromotionTarget
  navierStokesEnergyInequality : PromotionTarget
  navierStokesRegularityCriterion : PromotionTarget
  navierStokesGlobalSmoothness : PromotionTarget
  yangMillsGaugeIdentification : PromotionTarget
  yangMillsLieAlgebraIdentification : PromotionTarget
  yangMillsWilsonAction : PromotionTarget
  yangMillsOSPositivity : PromotionTarget
  yangMillsContinuumLimit : PromotionTarget
  yangMillsWightmanReconstruction : PromotionTarget
  yangMillsPositiveMassGap : PromotionTarget
  yangMillsExternalAcceptance : PromotionTarget
  terminalCrossLaneConsistency : PromotionTarget

data ObligationKind : Set where
  finiteEvidence : ObligationKind
  theoremObligation : ObligationKind
  adapterObligation : ObligationKind
  authorityObligation : ObligationKind
  validationObligation : ObligationKind
  terminalObligation : ObligationKind

data ObligationStatus : Set where
  evidenceRecordedNonPromoting : ObligationStatus
  openAdapterRequired : ObligationStatus
  openTheoremRequired : ObligationStatus
  openAuthorityRequired : ObligationStatus
  openValidationRequired : ObligationStatus
  blockedUntilAllRowsPromote : ObligationStatus

data PromotionGuard : Set where
  gate3ClosedGuard : PromotionGuard
  moscoLiminfPromotedGuard : PromotionGuard
  moscoRecoveryPromotedGuard : PromotionGuard
  noSpectralPollutionPromotedGuard : PromotionGuard
  continuumTransferPromotedGuard : PromotionGuard
  massShellBridgePromotedGuard : PromotionGuard
  navierStokesClayPromotedGuard : PromotionGuard
  yangMillsClayPromotedGuard : PromotionGuard
  terminalPromotionGuard : PromotionGuard

record PromotionObligationRow : Set₁ where
  field
    rowLabel :
      String

    lane :
      ClayPromotionLane

    target :
      PromotionTarget

    obligationKind :
      ObligationKind

    status :
      ObligationStatus

    registryLawTarget :
      String

    ownerSurface :
      String

    existingEvidence :
      List String

    requiredEvidence :
      List String

    guardToFlip :
      PromotionGuard

    guardName :
      String

    validationTarget :
      String

    validationCommand :
      String

    evidenceSatisfied :
      Bool

    promotesGlobalClaim :
      Bool

    promotesGlobalClaimIsFalse :
      promotesGlobalClaim ≡ false

    boundaryNotes :
      List String

open PromotionObligationRow public

mkOpenObligation :
  String →
  ClayPromotionLane →
  PromotionTarget →
  ObligationKind →
  ObligationStatus →
  String →
  String →
  List String →
  List String →
  PromotionGuard →
  String →
  String →
  String →
  List String →
  PromotionObligationRow
mkOpenObligation
  label lane target kind status law owner existing required guard guardName
  validationTarget validationCommand notes =
  record
    { rowLabel = label
    ; lane = lane
    ; target = target
    ; obligationKind = kind
    ; status = status
    ; registryLawTarget = law
    ; ownerSurface = owner
    ; existingEvidence = existing
    ; requiredEvidence = required
    ; guardToFlip = guard
    ; guardName = guardName
    ; validationTarget = validationTarget
    ; validationCommand = validationCommand
    ; evidenceSatisfied = false
    ; promotesGlobalClaim = false
    ; promotesGlobalClaimIsFalse = refl
    ; boundaryNotes = notes
    }

mkRecordedEvidence :
  String →
  ClayPromotionLane →
  PromotionTarget →
  String →
  String →
  List String →
  List String →
  PromotionGuard →
  String →
  String →
  String →
  List String →
  PromotionObligationRow
mkRecordedEvidence
  label lane target law owner existing required guard guardName
  validationTarget validationCommand notes =
  record
    { rowLabel = label
    ; lane = lane
    ; target = target
    ; obligationKind = finiteEvidence
    ; status = evidenceRecordedNonPromoting
    ; registryLawTarget = law
    ; ownerSurface = owner
    ; existingEvidence = existing
    ; requiredEvidence = required
    ; guardToFlip = guard
    ; guardName = guardName
    ; validationTarget = validationTarget
    ; validationCommand = validationCommand
    ; evidenceSatisfied = true
    ; promotesGlobalClaim = false
    ; promotesGlobalClaimIsFalse = refl
    ; boundaryNotes = notes
    }

gate3ValidationCommand : String
gate3ValidationCommand =
  "agda -i . DASHI/Promotion/Gate3ClayObligations.agda"

canonicalGate3ObligationRows : List PromotionObligationRow
canonicalGate3ObligationRows =
  mkRecordedEvidence
    "Gate 3 pruned-union density and fill-distance evidence"
    gate3ClosureLane
    gate3DensityProof
    "Gate 3 density/fill-distance target"
    "DASHI.Physics.Closure.Gate3PrunedUnionDensityReceipt"
    ( "Gate3PrunedUnionDensityReceipt"
    ∷ "Gate3PrunedUnionDensityClosureReceipt"
    ∷ "ArithmeticGate3KnownInputsReferenceReceipt.densityEvidencePromoted=true"
    ∷ []
    )
    ( "consumer theorem must use the density row in a Mosco argument"
    ∷ "density alone must not be read as Gate 3 closure"
    ∷ []
    )
    gate3ClosedGuard
    "gate3Closed"
    "DASHI/Promotion/Gate3ClayObligations.agda"
    gate3ValidationCommand
    ( "recorded finite route evidence only"
    ∷ "no continuum operator claim follows from this row"
    ∷ []
    )
  ∷ mkOpenObligation
    "Gate 3 Mosco liminf inequality"
    gate3ClosureLane
    gate3MoscoLiminf
    theoremObligation
    openTheoremRequired
    "Gate 3 Mosco target"
    "DASHI.Physics.Closure.Gate3PrunedDensityMoscoReceipt"
    ( "Gate3PrunedDensityMoscoReceipt"
    ∷ "Gate3MoscoConstructiveSequenceReceipt"
    ∷ []
    )
    ( "common ambient Hilbert/energy space"
    ∷ "lower-semicontinuity inequality for every convergent approximating sequence"
    ∷ "unit and domain compatibility with the finite norm dictionary"
    ∷ "proof consumed by the Gate 3 closure guard"
    ∷ []
    )
    moscoLiminfPromotedGuard
    "moscoLiminfPromoted"
    "DASHI/Physics/Closure/Gate3PrunedDensityMoscoReceipt.agda"
    "agda -i . DASHI/Physics/Closure/Gate3PrunedDensityMoscoReceipt.agda"
    ( "liminf is independent from recovery"
    ∷ "cannot be replaced by finite sampling evidence"
    ∷ []
    )
  ∷ mkOpenObligation
    "Gate 3 Mosco recovery sequence"
    gate3ClosureLane
    gate3MoscoRecovery
    theoremObligation
    openTheoremRequired
    "Gate 3 Mosco recovery target"
    "DASHI.Physics.Closure.Gate3MoscoRecoveryPreciseReceipt"
    ( "Gate3MoscoRecoveryPreciseReceipt"
    ∷ "Gate3MoscoConstructiveSequenceReceipt"
    ∷ []
    )
    ( "constructive recovery sequence for each continuum admissible vector"
    ∷ "energy convergence proof"
    ∷ "domain preservation proof"
    ∷ "compatibility with pruned-union density evidence"
    ∷ []
    )
    moscoRecoveryPromotedGuard
    "moscoRecoveryPromoted"
    "DASHI/Physics/Closure/Gate3MoscoRecoveryPreciseReceipt.agda"
    "agda -i . DASHI/Physics/Closure/Gate3MoscoRecoveryPreciseReceipt.agda"
    ( "recovery sequence is the missing positive construction"
    ∷ "Gate 3 remains open without it"
    ∷ []
    )
  ∷ mkOpenObligation
    "Gate 3 no spectral pollution"
    gate3ClosureLane
    gate3NoSpectralPollution
    theoremObligation
    openTheoremRequired
    "Gate 3 no-spectral-pollution target"
    "DASHI.Physics.Closure.Gate3NoSpectralPollutionReceipt"
    ( "NoSpectralPollutionReceipt"
    ∷ "Gate3NoSpectralPollutionConditionalProofReceipt"
    ∷ []
    )
    ( "resolvent or form convergence theorem strong enough for spectral exclusion"
    ∷ "proof that spurious finite eigenvalues cannot persist"
    ∷ "operator-domain compatibility"
    ∷ "explicit dependence on Mosco liminf and recovery rows"
    ∷ []
    )
    noSpectralPollutionPromotedGuard
    "noSpectralPollutionPromoted"
    "DASHI/Physics/Closure/Gate3NoSpectralPollutionReceipt.agda"
    "agda -i . DASHI/Physics/Closure/Gate3NoSpectralPollutionReceipt.agda"
    ( "conditional rows do not flip the guard"
    ∷ "finite spectrum tables are diagnostic only"
    ∷ []
    )
  ∷ mkOpenObligation
    "Gate 3 spectral transfer to continuum operator"
    gate3ClosureLane
    gate3SpectralTransfer
    theoremObligation
    openTheoremRequired
    "Gate 3 spectral transfer target"
    "DASHI.Physics.Closure.SpectralConvergenceGate3Receipt"
    ( "SpectralConvergenceGate3Receipt"
    ∷ "Gate3SpectralTransferOrPruningReceipt"
    ∷ []
    )
    ( "spectral convergence theorem from finite/pruned carriers"
    ∷ "identification of limiting operator"
    ∷ "no-pollution consumer proof"
    ∷ "stable translation into NS/YM consumer lanes"
    ∷ []
    )
    continuumTransferPromotedGuard
    "continuumTransferPromoted"
    "DASHI/Physics/Closure/SpectralConvergenceGate3Receipt.agda"
    "agda -i . DASHI/Physics/Closure/SpectralConvergenceGate3Receipt.agda"
    ( "transfer must name the continuum operator"
    ∷ "route evidence alone is not spectral convergence"
    ∷ []
    )
  ∷ mkOpenObligation
    "Gate 3 mass-shell bridge"
    gate3ClosureLane
    gate3MassShellIdentification
    adapterObligation
    openAdapterRequired
    "mass-shell bridge target"
    "DASHI.Physics.Closure.CarrierEnergyToMassShellReceipt"
    ( "CarrierEnergyToMassShellReceipt"
    ∷ "CarrierMoscoConvergenceFromPhysicsReceipt"
    ∷ []
    )
    ( "energy-to-mass-shell map"
    ∷ "unit convention and exact/authority constants consumed"
    ∷ "operator spectrum to physical mass interpretation"
    ∷ "known-physics translation receipt"
    ∷ []
    )
    massShellBridgePromotedGuard
    "massShellBridgePromoted"
    "DASHI/Physics/Closure/CarrierEnergyToMassShellReceipt.agda"
    "agda -i . DASHI/Physics/Closure/CarrierEnergyToMassShellReceipt.agda"
    ( "mass shell is a physics adapter, not a finite arithmetic fact"
    ∷ "must remain separate from Clay acceptance"
    ∷ []
    )
  ∷ []

canonicalNavierStokesObligationRows : List PromotionObligationRow
canonicalNavierStokesObligationRows =
  mkOpenObligation
    "Navier-Stokes weak solution class"
    navierStokesClayLane
    navierStokesWeakSolutionClass
    adapterObligation
    openAdapterRequired
    "Navier-Stokes equations"
    "DASHI.Physics.Closure.NSClayCurrentStateReceipt"
    ( "NSClayCurrentStateReceipt"
    ∷ "NSClayHonestAssessmentReceipt"
    ∷ []
    )
    ( "standard 3D incompressible NS formulation"
    ∷ "Leray-Hopf weak class or explicitly equivalent class"
    ∷ "initial data and forcing conventions"
    ∷ "pressure/distribution convention"
    ∷ []
    )
    navierStokesClayPromotedGuard
    "navierStokesClayPromoted"
    "DASHI/Physics/Closure/NSClayCurrentStateReceipt.agda"
    "agda -i . DASHI/Physics/Closure/NSClayCurrentStateReceipt.agda"
    ( "weak class is necessary but never sufficient for Clay smoothness"
    ∷ []
    )
  ∷ mkOpenObligation
    "Navier-Stokes strong solution continuation class"
    navierStokesClayLane
    navierStokesStrongSolutionClass
    theoremObligation
    openTheoremRequired
    "Navier-Stokes equations"
    "DASHI.Physics.Closure.NSH118VsClayGapReceipt"
    ( "NSH118VsClayGapReceipt"
    ∷ "NSClayDistanceFinalReceipt"
    ∷ []
    )
    ( "strong solution class tied to Clay smoothness statement"
    ∷ "continuation criterion in the chosen norm"
    ∷ "approximation stability from finite/carrier route"
    ∷ []
    )
    navierStokesClayPromotedGuard
    "navierStokesClayPromoted"
    "DASHI/Physics/Closure/NSH118VsClayGapReceipt.agda"
    "agda -i . DASHI/Physics/Closure/NSH118VsClayGapReceipt.agda"
    ( "H118-style internal bounds must translate to standard PDE regularity"
    ∷ []
    )
  ∷ mkOpenObligation
    "Navier-Stokes pressure reconstruction"
    navierStokesClayLane
    navierStokesPressureReconstruction
    theoremObligation
    openTheoremRequired
    "Navier-Stokes pressure equation"
    "DASHI.Physics.Closure.NSPhasePressureGate3Receipt"
    ( "NSPhasePressureGate3Receipt"
    ∷ "ClaySprintSixtyFiveNSPressureReconstructionCKNContractReceipt"
    ∷ []
    )
    ( "Poisson pressure reconstruction from velocity"
    ∷ "Riesz transform or equivalent boundedness"
    ∷ "phase/unit-group compatibility"
    ∷ "local energy inequality compatibility"
    ∷ []
    )
    navierStokesClayPromotedGuard
    "navierStokesClayPromoted"
    "DASHI/Physics/Closure/NSPhasePressureGate3Receipt.agda"
    "agda -i . DASHI/Physics/Closure/NSPhasePressureGate3Receipt.agda"
    ( "pressure is a known explicit blocker for the NS route"
    ∷ []
    )
  ∷ mkOpenObligation
    "Navier-Stokes nonlinear term passage"
    navierStokesClayLane
    navierStokesNonlinearTermPassage
    theoremObligation
    openTheoremRequired
    "Navier-Stokes nonlinear convection"
    "DASHI.Physics.Closure.NSCarrierVsClayGapReceipt"
    ( "NSCarrierVsClayGapReceipt"
    ∷ "ClaySprintSixtyFourNSSourceBudgetExhaustionCKNRouteReceipt"
    ∷ []
    )
    ( "compactness or strong convergence adequate for u dot grad u"
    ∷ "commutator/remainder control"
    ∷ "pressure-coupled nonlinear passage"
    ∷ "no hidden regularity assumption"
    ∷ []
    )
    navierStokesClayPromotedGuard
    "navierStokesClayPromoted"
    "DASHI/Physics/Closure/NSCarrierVsClayGapReceipt.agda"
    "agda -i . DASHI/Physics/Closure/NSCarrierVsClayGapReceipt.agda"
    ( "finite diagnostics cannot replace nonlinear passage"
    ∷ []
    )
  ∷ mkOpenObligation
    "Navier-Stokes energy inequality"
    navierStokesClayLane
    navierStokesEnergyInequality
    theoremObligation
    openTheoremRequired
    "Navier-Stokes energy inequality"
    "DASHI.Physics.Closure.NSEnstrophyClayHingeReceipt"
    ( "NSEnstrophyClayHingeReceipt"
    ∷ "NSSubcriticalVortexStretching"
    ∷ []
    )
    ( "global energy inequality in the standard PDE variables"
    ∷ "local energy inequality where the route uses CKN"
    ∷ "dissipation dominance without circular regularity"
    ∷ []
    )
    navierStokesClayPromotedGuard
    "navierStokesClayPromoted"
    "DASHI/Physics/Closure/NSEnstrophyClayHingeReceipt.agda"
    "agda -i . DASHI/Physics/Closure/NSEnstrophyClayHingeReceipt.agda"
    ( "energy control is necessary but not the full Clay theorem"
    ∷ []
    )
  ∷ mkOpenObligation
    "Navier-Stokes regularity criterion"
    navierStokesClayLane
    navierStokesRegularityCriterion
    theoremObligation
    openTheoremRequired
    "Navier-Stokes regularity criterion"
    "DASHI.Physics.Closure.ClaySprintSixtySevenNSCKNLemmaTestLadderReceipt"
    ( "ClaySprintSixtySevenNSCKNLemmaTestLadderReceipt"
    ∷ "ClaySprintSixtyEightNSResearchUpdateFalsificationLedgerReceipt"
    ∷ []
    )
    ( "accepted Serrin/CKN/Beale-Kato-Majda-style criterion or equivalent"
    ∷ "DASHI route proves the criterion hypothesis globally"
    ∷ "proof avoids subcritical assumption leakage"
    ∷ []
    )
    navierStokesClayPromotedGuard
    "navierStokesClayPromoted"
    "DASHI/Physics/Closure/ClaySprintSixtySevenNSCKNLemmaTestLadderReceipt.agda"
    "agda -i . DASHI/Physics/Closure/ClaySprintSixtySevenNSCKNLemmaTestLadderReceipt.agda"
    ( "criterion and hypothesis proof must both be present"
    ∷ []
    )
  ∷ mkOpenObligation
    "Navier-Stokes global smoothness"
    navierStokesClayLane
    navierStokesGlobalSmoothness
    theoremObligation
    openTheoremRequired
    "Navier-Stokes Clay global regularity target"
    "DASHI.Physics.Closure.NSFastestClayPathReceipt"
    ( "NSFastestClayPathReceipt"
    ∷ "NSPaper1ClayTargetReceipt"
    ∷ "NSClayDistanceRevisionReceipt"
    ∷ []
    )
    ( "standard Clay theorem statement"
    ∷ "global existence and smoothness proof"
    ∷ "pressure and nonlinear passage consumed"
    ∷ "validation target passes after all NS rows are inhabited"
    ∷ []
    )
    navierStokesClayPromotedGuard
    "navierStokesClayPromoted"
    "DASHI/Physics/Closure/NSFastestClayPathReceipt.agda"
    "agda -i . DASHI/Physics/Closure/NSFastestClayPathReceipt.agda"
    ( "only this row can close the NS Clay promotion"
    ∷ []
    )
  ∷ []

canonicalYangMillsObligationRows : List PromotionObligationRow
canonicalYangMillsObligationRows =
  mkOpenObligation
    "Yang-Mills gauge identification"
    yangMillsClayLane
    yangMillsGaugeIdentification
    adapterObligation
    openAdapterRequired
    "Yang-Mills equation and mass gap target"
    "DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt"
    ( "YangMillsGate3DiscreteGeometryReceipt"
    ∷ "YMPaper3ClayTargetReceipt"
    ∷ []
    )
    ( "compact gauge group convention"
    ∷ "principal-bundle or lattice-gauge carrier"
    ∷ "gauge equivalence relation"
    ∷ "observables invariant under gauge action"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/YangMillsGate3DiscreteGeometryReceipt.agda"
    "agda -i . DASHI/Physics/Closure/YangMillsGate3DiscreteGeometryReceipt.agda"
    ( "gauge target vocabulary alone is not YM construction"
    ∷ []
    )
  ∷ mkOpenObligation
    "Yang-Mills Lie algebra identification"
    yangMillsClayLane
    yangMillsLieAlgebraIdentification
    adapterObligation
    openAdapterRequired
    "Yang-Mills Lie algebra target"
    "DASHI.Physics.Closure.ClayProofCampaignDependencyDAGReceipt"
    ( "ClayProofCampaignDependencyDAGReceipt"
    ∷ "fieldStrengthFibreRepresentation"
    ∷ "killingAdInvariance"
    ∷ []
    )
    ( "su(3) or stated compact simple Lie algebra"
    ∷ "positive invariant form"
    ∷ "field strength curvature map"
    ∷ "normalization compatible with Wilson action"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/ClayProofCampaignDependencyDAGReceipt.agda"
    "agda -i . DASHI/Physics/Closure/ClayProofCampaignDependencyDAGReceipt.agda"
    ( "algebra identification must be consumed by the action row"
    ∷ []
    )
  ∷ mkOpenObligation
    "Yang-Mills Wilson action and measure"
    yangMillsClayLane
    yangMillsWilsonAction
    theoremObligation
    openTheoremRequired
    "Yang-Mills Wilson action"
    "DASHI.Physics.Closure.YMKPActivityRatioMarginReceipt"
    ( "YMKPActivityRatioMarginReceipt"
    ∷ "ClaySprintSeventySixYMLatticeMassGapFromAnisotropicKPReceipt"
    ∷ []
    )
    ( "Wilson plaquette action or continuum action with exact normalization"
    ∷ "finite-volume measure"
    ∷ "gauge-fixing or gauge-invariant construction"
    ∷ "KP/Balaban activity bounds tied to this action"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/YMKPActivityRatioMarginReceipt.agda"
    "agda -i . DASHI/Physics/Closure/YMKPActivityRatioMarginReceipt.agda"
    ( "activity estimates must be action-bound"
    ∷ []
    )
  ∷ mkOpenObligation
    "Yang-Mills Osterwalder-Schrader positivity"
    yangMillsClayLane
    yangMillsOSPositivity
    theoremObligation
    openTheoremRequired
    "Yang-Mills OS positivity target"
    "DASHI.Physics.Closure.ClaySprintSeventySixYMContinuumOSMassGapSurvivalReceipt"
    ( "ClaySprintSeventySixYMContinuumOSMassGapSurvivalReceipt"
    ∷ "ClaySprintSeventyThreeYMTransferMatrixCompatibilityGateReceipt"
    ∷ []
    )
    ( "reflection positivity for the lattice/continuum measure"
    ∷ "transfer-matrix compatibility"
    ∷ "survival under blocking or continuum limiting operation"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/ClaySprintSeventySixYMContinuumOSMassGapSurvivalReceipt.agda"
    "agda -i . DASHI/Physics/Closure/ClaySprintSeventySixYMContinuumOSMassGapSurvivalReceipt.agda"
    ( "OS positivity is required before Wightman reconstruction"
    ∷ []
    )
  ∷ mkOpenObligation
    "Yang-Mills continuum limit"
    yangMillsClayLane
    yangMillsContinuumLimit
    theoremObligation
    openTheoremRequired
    "Yang-Mills continuum limit target"
    "DASHI.Physics.Closure.YMBalabanTransferCompatibilityTheorem"
    ( "YMBalabanTransferCompatibilityTheorem"
    ∷ "ClaySprintSeventySixYMBalabanTransferCompatibilityReceipt"
    ∷ "ClaySprintSeventyEightYMBalabanEndpointAfterSpatialSupportReceipt"
    ∷ []
    )
    ( "tightness or projective-limit construction"
    ∷ "renormalization-group transfer"
    ∷ "nontrivial limiting measure"
    ∷ "mass gap survival through the limit"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/YMBalabanTransferCompatibilityTheorem.agda"
    "agda -i . DASHI/Physics/Closure/YMBalabanTransferCompatibilityTheorem.agda"
    ( "finite lattice gap is not continuum Clay authority"
    ∷ []
    )
  ∷ mkOpenObligation
    "Yang-Mills Wightman reconstruction"
    yangMillsClayLane
    yangMillsWightmanReconstruction
    theoremObligation
    openTheoremRequired
    "Yang-Mills Wightman reconstruction target"
    "DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation"
    ( "ContinuumClayMassGapReceiptObligation"
    ∷ "ClaySprintSeventySixYMContinuumOSMassGapSurvivalReceipt"
    ∷ []
    )
    ( "OS axioms verified for the limiting Schwinger functions"
    ∷ "Hilbert space reconstruction"
    ∷ "spectrum condition and locality"
    ∷ "nontriviality of reconstructed four-dimensional theory"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/ContinuumClayMassGapReceiptObligation.agda"
    "agda -i . DASHI/Physics/Closure/ContinuumClayMassGapReceiptObligation.agda"
    ( "Wightman reconstruction is downstream of OS positivity"
    ∷ []
    )
  ∷ mkOpenObligation
    "Yang-Mills positive mass gap"
    yangMillsClayLane
    yangMillsPositiveMassGap
    theoremObligation
    openTheoremRequired
    "Yang-Mills mass gap target"
    "DASHI.Physics.Closure.ClaySprintSeventySevenYMEndpointMassGapExactLemmaReceipt"
    ( "ClaySprintSeventySevenYMEndpointMassGapExactLemmaReceipt"
    ∷ "ClaySprintSeventySixYMLatticeMassGapFromAnisotropicKPReceipt"
    ∷ "YMKPActivityRatioMarginReceipt"
    ∷ []
    )
    ( "strict positive lower spectral gap"
    ∷ "gap attached to the reconstructed continuum Hamiltonian"
    ∷ "uniformity in lattice spacing and volume"
    ∷ "external Clay formulation compatibility"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/ClaySprintSeventySevenYMEndpointMassGapExactLemmaReceipt.agda"
    "agda -i . DASHI/Physics/Closure/ClaySprintSeventySevenYMEndpointMassGapExactLemmaReceipt.agda"
    ( "endpoint finite gap must survive both infinite-volume and continuum limits"
    ∷ []
    )
  ∷ mkOpenObligation
    "Yang-Mills external Clay acceptance"
    yangMillsClayLane
    yangMillsExternalAcceptance
    authorityObligation
    openAuthorityRequired
    "Yang-Mills Clay problem statement"
    "DASHI.Physics.Closure.YMClayFinalStateReceipt"
    ( "YMClayFinalStateReceipt"
    ∷ "YMClayDistanceFinalReceipt"
    ∷ "YMClayDistanceRevisionReceipt"
    ∷ []
    )
    ( "standard Clay-compatible theorem statement"
    ∷ "external mathematical review or accepted authority token"
    ∷ "claim-surface audit after validation"
    ∷ []
    )
    yangMillsClayPromotedGuard
    "yangMillsClayPromoted"
    "DASHI/Physics/Closure/YMClayFinalStateReceipt.agda"
    "agda -i . DASHI/Physics/Closure/YMClayFinalStateReceipt.agda"
    ( "internal receipt alone is not external acceptance"
    ∷ []
    )
  ∷ []

canonicalTerminalClayObligationRows : List PromotionObligationRow
canonicalTerminalClayObligationRows =
  mkOpenObligation
    "Terminal cross-lane Clay and unification consistency"
    terminalClayUnificationLane
    terminalCrossLaneConsistency
    terminalObligation
    blockedUntilAllRowsPromote
    "terminal/full unification target"
    "DASHI.Interop.CategoricalInterlinkLayer"
    ( "canonicalCategoricalInterlinkReceipt"
    ∷ "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
    ∷ "canonicalArithmeticGate3KnownInputsReferenceReceipt"
    ∷ []
    )
    ( "Gate 3 closure guard true"
    ∷ "Navier-Stokes Clay guard true if claimed"
    ∷ "Yang-Mills Clay guard true if claimed"
    ∷ "known-physics translation receipts consumed"
    ∷ "no contradictory false blockers remain in claim surface"
    ∷ "full validation manifest passes"
    ∷ []
    )
    terminalPromotionGuard
    "terminalPromotion"
    "DASHI/Interop/CategoricalInterlinkLayer.agda"
    "agda -i . DASHI/Interop/CategoricalInterlinkLayer.agda"
    ( "terminal promotion is last-only"
    ∷ "no terminal claim follows from this obligation index"
    ∷ []
    )
  ∷ []

allGate3ClayPromotionObligations : List PromotionObligationRow
allGate3ClayPromotionObligations =
  canonicalGate3ObligationRows
  ++ canonicalNavierStokesObligationRows
  ++ canonicalYangMillsObligationRows
  ++ canonicalTerminalClayObligationRows

record Gate3ClayPromotionObligationReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    sourceArithmeticGate3Receipt :
      ArithmeticGate3KnownInputsReferenceReceipt

    obligationRows :
      List PromotionObligationRow

    gate3Rows :
      List PromotionObligationRow

    navierStokesRows :
      List PromotionObligationRow

    yangMillsRows :
      List PromotionObligationRow

    terminalRows :
      List PromotionObligationRow

    densityEvidenceRecorded :
      Bool

    densityEvidenceRecordedIsTrue :
      densityEvidenceRecorded ≡ true

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    moscoLiminfPromoted :
      Bool

    moscoLiminfPromotedIsFalse :
      moscoLiminfPromoted ≡ false

    moscoRecoveryPromoted :
      Bool

    moscoRecoveryPromotedIsFalse :
      moscoRecoveryPromoted ≡ false

    noSpectralPollutionPromoted :
      Bool

    noSpectralPollutionPromotedIsTrue :
      noSpectralPollutionPromoted ≡ true

    continuumTransferPromoted :
      Bool

    continuumTransferPromotedIsFalse :
      continuumTransferPromoted ≡ false

    massShellBridgePromoted :
      Bool

    massShellBridgePromotedIsFalse :
      massShellBridgePromoted ≡ false

    navierStokesClayPromoted :
      Bool

    navierStokesClayPromotedIsFalse :
      navierStokesClayPromoted ≡ false

    yangMillsClayPromoted :
      Bool

    yangMillsClayPromotedIsFalse :
      yangMillsClayPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    validationTarget :
      String

    validationCommand :
      String

open Gate3ClayPromotionObligationReceipt public

canonicalGate3ClayPromotionObligationReceipt :
  Gate3ClayPromotionObligationReceipt
canonicalGate3ClayPromotionObligationReceipt = record
  { sourcePopulationReceipt =
      canonicalKnownInputsPopulationReceipt
  ; sourceArithmeticGate3Receipt =
      canonicalArithmeticGate3KnownInputsReferenceReceipt
  ; obligationRows =
      allGate3ClayPromotionObligations
  ; gate3Rows =
      canonicalGate3ObligationRows
  ; navierStokesRows =
      canonicalNavierStokesObligationRows
  ; yangMillsRows =
      canonicalYangMillsObligationRows
  ; terminalRows =
      canonicalTerminalClayObligationRows
  ; densityEvidenceRecorded =
      true
  ; densityEvidenceRecordedIsTrue =
      refl
  ; gate3Closed =
      false
  ; gate3ClosedIsFalse =
      refl
  ; moscoLiminfPromoted =
      false
  ; moscoLiminfPromotedIsFalse =
      refl
  ; moscoRecoveryPromoted =
      false
  ; moscoRecoveryPromotedIsFalse =
      refl
  ; noSpectralPollutionPromoted =
      true
  ; noSpectralPollutionPromotedIsTrue =
      refl
  ; continuumTransferPromoted =
      false
  ; continuumTransferPromotedIsFalse =
      refl
  ; massShellBridgePromoted =
      false
  ; massShellBridgePromotedIsFalse =
      refl
  ; navierStokesClayPromoted =
      false
  ; navierStokesClayPromotedIsFalse =
      refl
  ; yangMillsClayPromoted =
      false
  ; yangMillsClayPromotedIsFalse =
      refl
  ; terminalPromotion =
      false
  ; terminalPromotionIsFalse =
      refl
  ; validationTarget =
      "DASHI/Promotion/Gate3ClayObligations.agda"
  ; validationCommand =
      gate3ValidationCommand
  }

gate3ClayObligationKeepsRegistryPhysicalLawDerivedFalse :
  ConstantsRegistry.physicalLawDerived repoWideConstantsRegistry ≡ false
gate3ClayObligationKeepsRegistryPhysicalLawDerivedFalse =
  ConstantsRegistry.physicalLawDerivedIsFalse repoWideConstantsRegistry

gate3ClayObligationKeepsRegistryEmpiricalAdequacyFalse :
  ConstantsRegistry.empiricalAdequacyAccepted repoWideConstantsRegistry ≡ false
gate3ClayObligationKeepsRegistryEmpiricalAdequacyFalse =
  ConstantsRegistry.empiricalAdequacyAcceptedIsFalse repoWideConstantsRegistry

gate3ClayReceiptTerminalPromotionIsFalse :
  Gate3ClayPromotionObligationReceipt.terminalPromotion
    canonicalGate3ClayPromotionObligationReceipt
  ≡ false
gate3ClayReceiptTerminalPromotionIsFalse =
  Gate3ClayPromotionObligationReceipt.terminalPromotionIsFalse
    canonicalGate3ClayPromotionObligationReceipt

canonicalGate3ObligationCountIs6 :
  rowCount
    (Gate3ClayPromotionObligationReceipt.gate3Rows
      canonicalGate3ClayPromotionObligationReceipt)
  ≡ suc (suc (suc (suc (suc (suc zero)))))
canonicalGate3ObligationCountIs6 = refl

canonicalNavierStokesObligationCountIs7 :
  rowCount
    (Gate3ClayPromotionObligationReceipt.navierStokesRows
      canonicalGate3ClayPromotionObligationReceipt)
  ≡ suc (suc (suc (suc (suc (suc (suc zero))))))
canonicalNavierStokesObligationCountIs7 = refl

canonicalYangMillsObligationCountIs8 :
  rowCount
    (Gate3ClayPromotionObligationReceipt.yangMillsRows
      canonicalGate3ClayPromotionObligationReceipt)
  ≡ suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
canonicalYangMillsObligationCountIs8 = refl

canonicalTerminalClayObligationCountIs1 :
  rowCount
    (Gate3ClayPromotionObligationReceipt.terminalRows
      canonicalGate3ClayPromotionObligationReceipt)
  ≡ suc zero
canonicalTerminalClayObligationCountIs1 = refl

canonicalAllGate3ClayObligationCountIs22 :
  rowCount
    (Gate3ClayPromotionObligationReceipt.obligationRows
      canonicalGate3ClayPromotionObligationReceipt)
  ≡
    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc zero)))))))))))))))))))))
canonicalAllGate3ClayObligationCountIs22 = refl
