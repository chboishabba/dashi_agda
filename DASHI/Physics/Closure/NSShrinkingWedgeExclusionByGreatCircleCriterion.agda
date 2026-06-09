module DASHI.Physics.Closure.NSShrinkingWedgeExclusionByGreatCircleCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSLeiRenTianRadialZeroModeAuthorityBoundary as LRT
import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSTangentialZeroModePressureStarvationBoundary as Tangential

------------------------------------------------------------------------
-- Shrinking wedge exclusion by the Lei-Ren-Tian great-circle criterion.
--
-- Corrected boundary statement:
--
--   a shrinking cone/wedge trap for high-vorticity directions is a
--   great-circle-avoiding angular support scenario.  Lei-Ren-Tian
--   arXiv:2501.08976 gives the external deterministic criterion that a
--   singular vorticity-direction set must intersect every great circle.
--   Therefore a wedge trap is excluded as a singularity mechanism once
--   the aperture-to-great-circle-avoidance and microlocal support-transfer
--   steps are supplied.
--
-- Pressure starvation remains a secondary fallback route for wedge-like or
-- tangential traps.  It is not the primary promoted proof here, and this
-- module does not prove it.
--
-- This is a checked boundary surface.  It consumes the current
-- microlocal-defect-mass boundary, the Lei-Ren-Tian authority boundary, and
-- the tangential pressure-starvation boundary.  It does not construct the
-- microlocal measure, close sector switching, prove residual depletion, or
-- promote Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Angular wedge carriers.

data AngularTrapCarrier : Set where
  shrinkingConeTrap :
    AngularTrapCarrier

  shrinkingWedgeTrap :
    AngularTrapCarrier

  sigmaWedgeTrap :
    AngularTrapCarrier

data ApertureRegime : Set where
  positiveAperture :
    ApertureRegime

  shrinkingAperture :
    ApertureRegime

  apertureTendsToZero :
    ApertureRegime

data HighVorticityDirectionTrap : Set where
  highVorticityDirectionsTrappedIn :
    AngularTrapCarrier →
    ApertureRegime →
    HighVorticityDirectionTrap

canonicalWedgeTrap : AngularTrapCarrier
canonicalWedgeTrap =
  shrinkingWedgeTrap

canonicalApertureRegime : ApertureRegime
canonicalApertureRegime =
  apertureTendsToZero

canonicalHighVorticityDirectionTrap :
  HighVorticityDirectionTrap
canonicalHighVorticityDirectionTrap =
  highVorticityDirectionsTrappedIn
    canonicalWedgeTrap
    canonicalApertureRegime

data GreatCircleAvoidanceCarrier : Set where
  missesSomeGreatCircle :
    HighVorticityDirectionTrap →
    GreatCircleAvoidanceCarrier

data LeiRenTianWedgeExclusionBoundary : Set where
  wedgeTrapExcludedByGreatCircleCriterion :
    GreatCircleAvoidanceCarrier →
    LRT.GreatCircleIntersectionAuthority →
    LeiRenTianWedgeExclusionBoundary

canonicalGreatCircleAvoidance :
  GreatCircleAvoidanceCarrier
canonicalGreatCircleAvoidance =
  missesSomeGreatCircle canonicalHighVorticityDirectionTrap

canonicalWedgeExclusionBoundary :
  LeiRenTianWedgeExclusionBoundary
canonicalWedgeExclusionBoundary =
  wedgeTrapExcludedByGreatCircleCriterion
    canonicalGreatCircleAvoidance
    LRT.canonicalGreatCircleAuthority

------------------------------------------------------------------------
-- The corrected proof route separates primary authority geometry from
-- secondary pressure fallback.

data WedgeExclusionRoute : Set where
  primaryGreatCircleAvoidanceRoute :
    WedgeExclusionRoute

  secondaryPressureStarvationFallback :
    WedgeExclusionRoute

  sectorSwitchingCompactnessRoute :
    WedgeExclusionRoute

canonicalWedgeExclusionRoutes :
  List WedgeExclusionRoute
canonicalWedgeExclusionRoutes =
  primaryGreatCircleAvoidanceRoute
  ∷ secondaryPressureStarvationFallback
  ∷ sectorSwitchingCompactnessRoute
  ∷ []

wedgeExclusionRouteCount : Nat
wedgeExclusionRouteCount =
  listLength canonicalWedgeExclusionRoutes

wedgeExclusionRouteCountIs3 :
  wedgeExclusionRouteCount ≡ 3
wedgeExclusionRouteCountIs3 =
  refl

primaryRouteIsGreatCircleAvoidance :
  canonicalWedgeExclusionRoutes
  ≡
  primaryGreatCircleAvoidanceRoute
  ∷ secondaryPressureStarvationFallback
  ∷ sectorSwitchingCompactnessRoute
  ∷ []
primaryRouteIsGreatCircleAvoidance =
  refl

data WedgeExclusionStep : Set where
  selectShrinkingAngularConeOrWedge :
    WedgeExclusionStep

  bindHighVorticityDirectionsToTrap :
    WedgeExclusionStep

  proveApertureImpliesGreatCircleAvoidance :
    WedgeExclusionStep

  applyLeiRenTianGreatCircleCriterion :
    WedgeExclusionStep

  excludeSingularWedgeTrap :
    WedgeExclusionStep

  retainPressureStarvationAsFallbackOnly :
    WedgeExclusionStep

  controlSectorSwitchingAcrossScales :
    WedgeExclusionStep

canonicalWedgeExclusionSteps :
  List WedgeExclusionStep
canonicalWedgeExclusionSteps =
  selectShrinkingAngularConeOrWedge
  ∷ bindHighVorticityDirectionsToTrap
  ∷ proveApertureImpliesGreatCircleAvoidance
  ∷ applyLeiRenTianGreatCircleCriterion
  ∷ excludeSingularWedgeTrap
  ∷ retainPressureStarvationAsFallbackOnly
  ∷ controlSectorSwitchingAcrossScales
  ∷ []

wedgeExclusionStepCount : Nat
wedgeExclusionStepCount =
  listLength canonicalWedgeExclusionSteps

wedgeExclusionStepCountIs7 :
  wedgeExclusionStepCount ≡ 7
wedgeExclusionStepCountIs7 =
  refl

------------------------------------------------------------------------
-- Blockers requested by the worker contract.

data ShrinkingWedgeBlocker : Set where
  missingQuantitativeApertureToGreatCircleAvoidance :
    ShrinkingWedgeBlocker

  missingMicrolocalSupportTransferToVorticityDirectionSet :
    ShrinkingWedgeBlocker

  missingLeiRenTianInternalFormalization :
    ShrinkingWedgeBlocker

  missingSectorSwitchingCompactness :
    ShrinkingWedgeBlocker

  missingPressureStarvationFallbackEstimate :
    ShrinkingWedgeBlocker

  missingMicrolocalDefectMassConstruction :
    ShrinkingWedgeBlocker

  missingNoZeroModeDegeneracyRidingCascade :
    ShrinkingWedgeBlocker

  missingNSCriticalResidualNonPositive :
    ShrinkingWedgeBlocker

  missingFullLocalDefectMonotonicity :
    ShrinkingWedgeBlocker

  missingMechanismExhaustionForFullClayNS :
    ShrinkingWedgeBlocker

  clayNavierStokesPromotionClosed :
    ShrinkingWedgeBlocker

canonicalShrinkingWedgeBlockers :
  List ShrinkingWedgeBlocker
canonicalShrinkingWedgeBlockers =
  missingQuantitativeApertureToGreatCircleAvoidance
  ∷ missingMicrolocalSupportTransferToVorticityDirectionSet
  ∷ missingLeiRenTianInternalFormalization
  ∷ missingSectorSwitchingCompactness
  ∷ missingPressureStarvationFallbackEstimate
  ∷ missingMicrolocalDefectMassConstruction
  ∷ missingNoZeroModeDegeneracyRidingCascade
  ∷ missingNSCriticalResidualNonPositive
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

shrinkingWedgeBlockerCount : Nat
shrinkingWedgeBlockerCount =
  listLength canonicalShrinkingWedgeBlockers

shrinkingWedgeBlockerCountIs11 :
  shrinkingWedgeBlockerCount ≡ 11
shrinkingWedgeBlockerCountIs11 =
  refl

data ShrinkingWedgeSupportRow : Set where
  microlocalDefectMassBoundaryConsumed :
    ShrinkingWedgeSupportRow

  leiRenTianGreatCircleAuthorityConsumed :
    ShrinkingWedgeSupportRow

  tangentialPressureStarvationFallbackConsumed :
    ShrinkingWedgeSupportRow

  shrinkingConeToGreatCircleAvoidanceTarget :
    ShrinkingWedgeSupportRow

  supportTransferFromMuToDirectionSetTarget :
    ShrinkingWedgeSupportRow

  sectorSwitchingAcrossScalesTarget :
    ShrinkingWedgeSupportRow

  pressureFallbackNotPrimaryProofRow :
    ShrinkingWedgeSupportRow

  noClayOrTerminalPromotionRow :
    ShrinkingWedgeSupportRow

canonicalShrinkingWedgeSupportRows :
  List ShrinkingWedgeSupportRow
canonicalShrinkingWedgeSupportRows =
  microlocalDefectMassBoundaryConsumed
  ∷ leiRenTianGreatCircleAuthorityConsumed
  ∷ tangentialPressureStarvationFallbackConsumed
  ∷ shrinkingConeToGreatCircleAvoidanceTarget
  ∷ supportTransferFromMuToDirectionSetTarget
  ∷ sectorSwitchingAcrossScalesTarget
  ∷ pressureFallbackNotPrimaryProofRow
  ∷ noClayOrTerminalPromotionRow
  ∷ []

shrinkingWedgeSupportRowCount : Nat
shrinkingWedgeSupportRowCount =
  listLength canonicalShrinkingWedgeSupportRows

shrinkingWedgeSupportRowCountIs8 :
  shrinkingWedgeSupportRowCount ≡ 8
shrinkingWedgeSupportRowCountIs8 =
  refl

data ShrinkingWedgeStatusRow : Set where
  wedgeTrapCarrierTypedStatus :
    ShrinkingWedgeStatusRow

  greatCircleAvoidanceBoundaryTypedStatus :
    ShrinkingWedgeStatusRow

  primaryLRTAuthorityRouteRecordedStatus :
    ShrinkingWedgeStatusRow

  pressureStarvationFallbackDemotedStatus :
    ShrinkingWedgeStatusRow

  apertureGeometryStillOpenStatus :
    ShrinkingWedgeStatusRow

  supportTransferStillOpenStatus :
    ShrinkingWedgeStatusRow

  sectorSwitchingStillOpenStatus :
    ShrinkingWedgeStatusRow

  clayPromotionFalseStatus :
    ShrinkingWedgeStatusRow

canonicalShrinkingWedgeStatusRows :
  List ShrinkingWedgeStatusRow
canonicalShrinkingWedgeStatusRows =
  wedgeTrapCarrierTypedStatus
  ∷ greatCircleAvoidanceBoundaryTypedStatus
  ∷ primaryLRTAuthorityRouteRecordedStatus
  ∷ pressureStarvationFallbackDemotedStatus
  ∷ apertureGeometryStillOpenStatus
  ∷ supportTransferStillOpenStatus
  ∷ sectorSwitchingStillOpenStatus
  ∷ clayPromotionFalseStatus
  ∷ []

shrinkingWedgeStatusRowCount : Nat
shrinkingWedgeStatusRowCount =
  listLength canonicalShrinkingWedgeStatusRows

shrinkingWedgeStatusRowCountIs8 :
  shrinkingWedgeStatusRowCount ≡ 8
shrinkingWedgeStatusRowCountIs8 =
  refl

data ShrinkingWedgePromotion : Set where

shrinkingWedgePromotionImpossibleHere :
  ShrinkingWedgePromotion →
  ⊥
shrinkingWedgePromotionImpossibleHere ()

------------------------------------------------------------------------
-- Governance flags.

NSShrinkingWedgeExclusionByGreatCircleCriterionRecorded : Bool
NSShrinkingWedgeExclusionByGreatCircleCriterionRecorded =
  true

MicrolocalBoundaryConsumed : Bool
MicrolocalBoundaryConsumed =
  true

LeiRenTianAuthorityBoundaryConsumed : Bool
LeiRenTianAuthorityBoundaryConsumed =
  true

TangentialPressureFallbackBoundaryConsumed : Bool
TangentialPressureFallbackBoundaryConsumed =
  true

PrimaryRouteIsLeiRenTianGreatCircleCriterion : Bool
PrimaryRouteIsLeiRenTianGreatCircleCriterion =
  true

PressureStarvationFallbackOnly : Bool
PressureStarvationFallbackOnly =
  true

ShrinkingWedgeTrapTyped : Bool
ShrinkingWedgeTrapTyped =
  true

GreatCircleAvoidanceTargetTyped : Bool
GreatCircleAvoidanceTargetTyped =
  true

QuantitativeApertureToGreatCircleAvoidanceProved : Bool
QuantitativeApertureToGreatCircleAvoidanceProved =
  false

MicrolocalSupportTransferProved : Bool
MicrolocalSupportTransferProved =
  false

LeiRenTianTheoremInternallyFormalized : Bool
LeiRenTianTheoremInternallyFormalized =
  false

SectorSwitchingCompactnessProved : Bool
SectorSwitchingCompactnessProved =
  false

PressureStarvationFallbackProved : Bool
PressureStarvationFallbackProved =
  false

WedgeExclusionAsSingularityMechanismProved : Bool
WedgeExclusionAsSingularityMechanismProved =
  false

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

NoZeroModeDegeneracyRidingCascade : Bool
NoZeroModeDegeneracyRidingCascade =
  false

NSCriticalResidualNonPositive : Bool
NSCriticalResidualNonPositive =
  false

FullLocalDefectMonotonicity : Bool
FullLocalDefectMonotonicity =
  false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

------------------------------------------------------------------------
-- Canonical explanatory strings and ORCSLPGF.

theoremName : String
theoremName =
  "NSShrinkingWedgeExclusionByGreatCircleCriterion"

primaryCriterionText : String
primaryCriterionText =
  "A shrinking cone or wedge trap is excluded primarily by reducing it to a great-circle-avoiding high-vorticity direction set and applying the Lei-Ren-Tian great-circle criterion."

fallbackText : String
fallbackText =
  "Pressure starvation remains a secondary fallback route for wedge-like traps; it is not promoted as the primary proof in this module."

blockerText : String
blockerText =
  "Open blockers: quantitative angular aperture-to-great-circle avoidance, microlocal support transfer to the Lei-Ren-Tian direction set I, and sector switching across scales."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "This boundary records the corrected wedge-collapse theorem target only; microlocal mass, sector switching, pressure starvation, residual depletion, Clay NS, and terminal promotion remain false."

organizationString : String
organizationString =
  "O: Worker lane 4 owns only the NS shrinking-wedge great-circle exclusion boundary."

requirementString : String
requirementString =
  "R: Encode the corrected wedge-collapse boundary: shrinking high-vorticity cone/wedge traps avoid a great circle, Lei-Ren-Tian excludes that singularity mechanism, and pressure starvation is fallback only."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSShrinkingWedgeExclusionByGreatCircleCriterion exports wedge carriers, great-circle avoidance boundary, route/step/support/status/blocker rows, imported anchors, ORCSLPGF, and false promotion guards."

stateString : String
stateString =
  "S: Microlocal defect-mass, Lei-Ren-Tian authority, and tangential pressure-starvation boundaries are consumed; aperture geometry, support transfer, sector switching, and residual depletion remain open."

latticeString : String
latticeString =
  "L: shrinking wedge trap -> high-vorticity direction trap -> great-circle avoidance -> Lei-Ren-Tian authority boundary -> wedge singularity exclusion target, with pressure-starvation fallback and sector-switching blockers."

proposalString : String
proposalString =
  "P: Promote only the corrected wedge boundary target as executable Agda structure; do not promote pressure starvation, microlocal mass, Clay NS, or terminal unification."

governanceString : String
governanceString =
  "G: Primary LRT route and fallback demotion are recorded true; all proof-completion and Clay/terminal flags are false."

gapString : String
gapString =
  "F: Missing evidence is the quantitative aperture-to-great-circle lemma, transfer from microlocal support to the Lei-Ren-Tian direction set I, sector-switching compactness, and the downstream residual monotonicity argument."

record NSShrinkingWedgeExclusionORCSLPGF : Set where
  constructor nsShrinkingWedgeExclusionORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open NSShrinkingWedgeExclusionORCSLPGF public

canonicalNSShrinkingWedgeExclusionORCSLPGF :
  NSShrinkingWedgeExclusionORCSLPGF
canonicalNSShrinkingWedgeExclusionORCSLPGF =
  nsShrinkingWedgeExclusionORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

------------------------------------------------------------------------
-- Canonical receipt.

record NSShrinkingWedgeExclusionByGreatCircleCriterionReceipt : Setω where
  constructor nsShrinkingWedgeExclusionByGreatCircleCriterionReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ theoremName

    microlocalBoundaryAnchor :
      Micro.NSMicrolocalDefectMassConstructionBoundaryReceipt
    microlocalBoundaryRecorded :
      Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
    microlocalMassStillFalse :
      Micro.MicrolocalDefectMassConstructed ≡ false
    microlocalPressureBootstrapStillFalse :
      Micro.PressureNonlocalityBootstrapClosed ≡ false

    leiRenTianAuthorityAnchor :
      LRT.NSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt
    leiRenTianAuthorityBoundaryRecorded :
      LRT.LeiRenTianGreatCircleAuthorityBoundaryRecorded ≡ true
    leiRenTianInternalProofStillFalse :
      LRT.LeiRenTianTheoremInternallyFormalized ≡ false
    leiRenTianClayStillFalse :
      LRT.clayNavierStokesPromoted ≡ false

    tangentialFallbackAnchor :
      Tangential.NSTangentialZeroModePressureStarvationBoundaryReceipt
    tangentialBoundaryRecorded :
      Tangential.NSTangentialZeroModePressureStarvationBoundaryRecorded
      ≡
      true
    tangentialPressureStarvationStillFalse :
      Tangential.TangentialZeroModePressureStarvationProved ≡ false
    dnsEvidenceNotProof :
      Tangential.DNSEvidencePromotedAsProof ≡ false

    highVorticityDirectionTrap :
      HighVorticityDirectionTrap
    highVorticityDirectionTrapIsCanonical :
      highVorticityDirectionTrap
      ≡
      canonicalHighVorticityDirectionTrap

    greatCircleAvoidance :
      GreatCircleAvoidanceCarrier
    greatCircleAvoidanceIsCanonical :
      greatCircleAvoidance ≡ canonicalGreatCircleAvoidance

    wedgeExclusionBoundary :
      LeiRenTianWedgeExclusionBoundary
    wedgeExclusionBoundaryIsCanonical :
      wedgeExclusionBoundary ≡ canonicalWedgeExclusionBoundary

    routes :
      List WedgeExclusionRoute
    routesAreCanonical :
      routes ≡ canonicalWedgeExclusionRoutes
    routeCount :
      Nat
    routeCountIsThree :
      routeCount ≡ 3

    steps :
      List WedgeExclusionStep
    stepsAreCanonical :
      steps ≡ canonicalWedgeExclusionSteps
    stepCount :
      Nat
    stepCountIsSeven :
      stepCount ≡ 7

    supportRows :
      List ShrinkingWedgeSupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalShrinkingWedgeSupportRows
    supportRowCount :
      Nat
    supportRowCountIsEight :
      supportRowCount ≡ 8

    statusRows :
      List ShrinkingWedgeStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalShrinkingWedgeStatusRows
    statusRowCount :
      Nat
    statusRowCountIsEight :
      statusRowCount ≡ 8

    blockerRows :
      List ShrinkingWedgeBlocker
    blockerRowsAreCanonical :
      blockerRows ≡ canonicalShrinkingWedgeBlockers
    blockerRowCount :
      Nat
    blockerRowCountIsEleven :
      blockerRowCount ≡ 11

    orcslpgf :
      NSShrinkingWedgeExclusionORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSShrinkingWedgeExclusionORCSLPGF

    primaryCriterion :
      String
    primaryCriterionIsCanonical :
      primaryCriterion ≡ primaryCriterionText
    fallbackDescription :
      String
    fallbackDescriptionIsCanonical :
      fallbackDescription ≡ fallbackText
    blockersDescription :
      String
    blockersDescriptionIsCanonical :
      blockersDescription ≡ blockerText
    nonPromotionBoundary :
      String
    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ nonPromotionBoundaryText

    boundaryRecorded :
      NSShrinkingWedgeExclusionByGreatCircleCriterionRecorded ≡ true
    microlocalBoundaryConsumed :
      MicrolocalBoundaryConsumed ≡ true
    leiRenTianBoundaryConsumed :
      LeiRenTianAuthorityBoundaryConsumed ≡ true
    tangentialFallbackBoundaryConsumed :
      TangentialPressureFallbackBoundaryConsumed ≡ true
    primaryRouteIsLeiRenTian :
      PrimaryRouteIsLeiRenTianGreatCircleCriterion ≡ true
    pressureStarvationFallbackOnly :
      PressureStarvationFallbackOnly ≡ true
    shrinkingWedgeTrapTyped :
      ShrinkingWedgeTrapTyped ≡ true
    greatCircleAvoidanceTargetTyped :
      GreatCircleAvoidanceTargetTyped ≡ true

    apertureAvoidanceStillFalse :
      QuantitativeApertureToGreatCircleAvoidanceProved ≡ false
    microlocalSupportTransferStillFalse :
      MicrolocalSupportTransferProved ≡ false
    leiRenTianInternalFormalizationStillFalse :
      LeiRenTianTheoremInternallyFormalized ≡ false
    sectorSwitchingStillFalse :
      SectorSwitchingCompactnessProved ≡ false
    pressureFallbackStillFalse :
      PressureStarvationFallbackProved ≡ false
    wedgeExclusionStillFalse :
      WedgeExclusionAsSingularityMechanismProved ≡ false
    microlocalDefectMassStillFalse :
      MicrolocalDefectMassConstructed ≡ false
    noDegeneracyRidingCascadeStillFalse :
      NoZeroModeDegeneracyRidingCascade ≡ false
    nsCriticalResidualStillFalse :
      NSCriticalResidualNonPositive ≡ false
    fullLocalDefectMonotonicityStillFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionStillFalse :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedSnakeFalse :
      full_clay_ns_solved ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List ShrinkingWedgePromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    remainingObligations :
      List String

open NSShrinkingWedgeExclusionByGreatCircleCriterionReceipt public

canonicalNSShrinkingWedgeExclusionByGreatCircleCriterionReceipt :
  NSShrinkingWedgeExclusionByGreatCircleCriterionReceipt
canonicalNSShrinkingWedgeExclusionByGreatCircleCriterionReceipt =
  nsShrinkingWedgeExclusionByGreatCircleCriterionReceipt
    theoremName
    refl
    Micro.canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
    refl
    refl
    refl
    LRT.canonicalNSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt
    refl
    refl
    refl
    Tangential.canonicalNSTangentialZeroModePressureStarvationBoundaryReceipt
    refl
    refl
    refl
    canonicalHighVorticityDirectionTrap
    refl
    canonicalGreatCircleAvoidance
    refl
    canonicalWedgeExclusionBoundary
    refl
    canonicalWedgeExclusionRoutes
    refl
    wedgeExclusionRouteCount
    refl
    canonicalWedgeExclusionSteps
    refl
    wedgeExclusionStepCount
    refl
    canonicalShrinkingWedgeSupportRows
    refl
    shrinkingWedgeSupportRowCount
    refl
    canonicalShrinkingWedgeStatusRows
    refl
    shrinkingWedgeStatusRowCount
    refl
    canonicalShrinkingWedgeBlockers
    refl
    shrinkingWedgeBlockerCount
    refl
    canonicalNSShrinkingWedgeExclusionORCSLPGF
    refl
    primaryCriterionText
    refl
    fallbackText
    refl
    blockerText
    refl
    nonPromotionBoundaryText
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    []
    refl
    ("prove shrinking angular aperture implies existence of an avoided great circle"
    ∷ "transfer microlocal support in a wedge to the Lei-Ren-Tian high-vorticity direction set I"
    ∷ "prove sector-switching compactness for cascades that hop between wedge and non-wedge sectors"
    ∷ "keep pressure starvation as fallback unless a scale-correct pressure little-o estimate is proved"
    ∷ "construct microlocal defect mass and close residual monotonicity before any Clay NS promotion"
    ∷ [])

------------------------------------------------------------------------
-- Convenience checks.

nsShrinkingWedgeBoundaryRecorded :
  NSShrinkingWedgeExclusionByGreatCircleCriterionRecorded ≡ true
nsShrinkingWedgeBoundaryRecorded =
  refl

nsShrinkingWedgeConsumesMicrolocalBoundary :
  Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
nsShrinkingWedgeConsumesMicrolocalBoundary =
  refl

nsShrinkingWedgeConsumesLeiRenTianAuthority :
  LRT.LeiRenTianGreatCircleAuthorityBoundaryRecorded ≡ true
nsShrinkingWedgeConsumesLeiRenTianAuthority =
  refl

nsShrinkingWedgeConsumesTangentialFallback :
  Tangential.NSTangentialZeroModePressureStarvationBoundaryRecorded
  ≡
  true
nsShrinkingWedgeConsumesTangentialFallback =
  refl

pressureStarvationIsFallbackNotPrimary :
  PressureStarvationFallbackOnly ≡ true
pressureStarvationIsFallbackNotPrimary =
  refl

wedgeApertureGeometryStillOpen :
  QuantitativeApertureToGreatCircleAvoidanceProved ≡ false
wedgeApertureGeometryStillOpen =
  refl

wedgeMicrolocalTransferStillOpen :
  MicrolocalSupportTransferProved ≡ false
wedgeMicrolocalTransferStillOpen =
  refl

wedgeSectorSwitchingStillOpen :
  SectorSwitchingCompactnessProved ≡ false
wedgeSectorSwitchingStillOpen =
  refl

wedgeExclusionKeepsMicrolocalMassFalse :
  MicrolocalDefectMassConstructed ≡ false
wedgeExclusionKeepsMicrolocalMassFalse =
  refl

wedgeExclusionKeepsNSClayFalse :
  clayNavierStokesPromoted ≡ false
wedgeExclusionKeepsNSClayFalse =
  refl

wedgeExclusionKeepsTerminalFalse :
  terminalPromotion ≡ false
wedgeExclusionKeepsTerminalFalse =
  refl
