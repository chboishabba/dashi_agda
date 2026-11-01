module DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.BTNSBoundaryDefectLeakageTarget as BTNS
import DASHI.Physics.Closure.NSSigmaNonRadialCommutatorLowerBoundTarget as Sigma
import DASHI.Physics.Closure.NSSprint162CriticalResidualBoundaryReceipt as S162
import DASHI.Physics.Closure.NSSprint163TopologicalAlignmentObstructionBoundaryReceipt as S163
import DASHI.Physics.Closure.NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt as S164

------------------------------------------------------------------------
-- NS microlocal defect-mass construction boundary.
--
-- This worker-lane surface records the exact remaining NS analytic gap:
--
--   blowup sequence
--     -> Littlewood-Paley localized vorticity at scale N_n ~ r_n^-1
--     -> semiclassical / microlocal defect measure
--     -> positive mass in the maximal-strain eigenbundle graph near Sigma
--     -> pressure nonlocality bootstrap blocker
--
-- It is deliberately a boundary receipt.  It imports the Sprint162
-- critical-residual boundary, Sprint163 Sanni/symbol-level Sigma support,
-- Sprint164 microlocal/topological bridge, the corrected
-- SigmaNonRadialCommutatorLowerBound target, and the finite-depth BT/NS
-- boundary-defect leakage target.  It does not prove a pressure bootstrap,
-- topological stretching leakage, full local defect monotonicity, mechanism
-- exhaustion, or Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSBlowupSequenceCarrier : Set where
  suitableBlowupSequence :
    NSBlowupSequenceCarrier

data CriticalScaleCarrier : Set where
  shrinkingParabolicScale :
    NSBlowupSequenceCarrier →
    CriticalScaleCarrier

data LittlewoodPaleyFrequencyScale : Set where
  reciprocalBlowupScaleFrequency :
    CriticalScaleCarrier →
    LittlewoodPaleyFrequencyScale

data LocalizedVorticityCarrier : Set where
  lpLocalizedVorticityShell :
    LittlewoodPaleyFrequencyScale →
    LocalizedVorticityCarrier

data SemiclassicalDefectMeasureCarrier : Set where
  weakStarLimitDefectMeasure :
    LocalizedVorticityCarrier →
    SemiclassicalDefectMeasureCarrier

data MaximalStrainGraphCarrier : Set where
  maximalStrainEigenbundleGraphNearSigma :
    Sigma.SigmaTransverseNeighborhood →
    MaximalStrainGraphCarrier

data PositiveMassTarget : Set where
  positiveMassInMaximalStrainGraph :
    SemiclassicalDefectMeasureCarrier →
    MaximalStrainGraphCarrier →
    PositiveMassTarget

data PressureNonlocalityBootstrap : Set where
  pressureRieszNonlocalityBootstrap :
    PositiveMassTarget →
    PressureNonlocalityBootstrap

data MicrolocalDefectMassDependencyLink : Set where
  criticalResidualSelectsBlowupSequence :
    MicrolocalDefectMassDependencyLink
  reciprocalScaleSelectsLPShell :
    MicrolocalDefectMassDependencyLink
  lpShellFeedsSemiclassicalMeasure :
    MicrolocalDefectMassDependencyLink
  defectMeasureMustChargeLMaxGraph :
    MicrolocalDefectMassDependencyLink
  positiveLMaxMassFeedsPressureBootstrap :
    MicrolocalDefectMassDependencyLink
  pressureBootstrapFeedsResidualDepletion :
    MicrolocalDefectMassDependencyLink

canonicalBlowupSequence : NSBlowupSequenceCarrier
canonicalBlowupSequence =
  suitableBlowupSequence

canonicalCriticalScale : CriticalScaleCarrier
canonicalCriticalScale =
  shrinkingParabolicScale canonicalBlowupSequence

canonicalLPFrequencyScale : LittlewoodPaleyFrequencyScale
canonicalLPFrequencyScale =
  reciprocalBlowupScaleFrequency canonicalCriticalScale

canonicalLocalizedVorticity : LocalizedVorticityCarrier
canonicalLocalizedVorticity =
  lpLocalizedVorticityShell canonicalLPFrequencyScale

canonicalDefectMeasure : SemiclassicalDefectMeasureCarrier
canonicalDefectMeasure =
  weakStarLimitDefectMeasure canonicalLocalizedVorticity

canonicalMaximalStrainGraph : MaximalStrainGraphCarrier
canonicalMaximalStrainGraph =
  maximalStrainEigenbundleGraphNearSigma
    Sigma.canonicalSigmaNeighborhood

canonicalPositiveMassTarget : PositiveMassTarget
canonicalPositiveMassTarget =
  positiveMassInMaximalStrainGraph
    canonicalDefectMeasure
    canonicalMaximalStrainGraph

canonicalPressureBootstrap : PressureNonlocalityBootstrap
canonicalPressureBootstrap =
  pressureRieszNonlocalityBootstrap canonicalPositiveMassTarget

canonicalMicrolocalDefectMassDependencyLinks :
  List MicrolocalDefectMassDependencyLink
canonicalMicrolocalDefectMassDependencyLinks =
  criticalResidualSelectsBlowupSequence
  ∷ reciprocalScaleSelectsLPShell
  ∷ lpShellFeedsSemiclassicalMeasure
  ∷ defectMeasureMustChargeLMaxGraph
  ∷ positiveLMaxMassFeedsPressureBootstrap
  ∷ pressureBootstrapFeedsResidualDepletion
  ∷ []

microlocalDefectMassDependencyLinkCount : Nat
microlocalDefectMassDependencyLinkCount =
  listLength canonicalMicrolocalDefectMassDependencyLinks

microlocalDefectMassDependencyLinkCountIs6 :
  microlocalDefectMassDependencyLinkCount ≡ 6
microlocalDefectMassDependencyLinkCountIs6 =
  refl

record NSMicrolocalDefectMassAdmissibilityQuotientBoundary : Set where
  constructor nsMicrolocalDefectMassAdmissibilityQuotientBoundary
  field
    admissibleCarrierRepresentative :
      LocalizedVorticityCarrier
    admissibleCarrierRepresentativeIsCanonical :
      admissibleCarrierRepresentative ≡ canonicalLocalizedVorticity
    quotientDefectMeasure :
      SemiclassicalDefectMeasureCarrier
    quotientDefectMeasureIsCanonical :
      quotientDefectMeasure ≡ canonicalDefectMeasure
    quotientMaximalStrainGraph :
      MaximalStrainGraphCarrier
    quotientMaximalStrainGraphIsCanonical :
      quotientMaximalStrainGraph ≡ canonicalMaximalStrainGraph
    quotientPositiveMassTarget :
      PositiveMassTarget
    quotientPositiveMassTargetIsCanonical :
      quotientPositiveMassTarget ≡ canonicalPositiveMassTarget
    dependencyLinks :
      List MicrolocalDefectMassDependencyLink
    dependencyLinksAreCanonical :
      dependencyLinks ≡ canonicalMicrolocalDefectMassDependencyLinks
    dependencyLinkCount :
      Nat
    dependencyLinkCountIs6 :
      dependencyLinkCount ≡ 6
    positiveMassTargetRecorded :
      Bool
    positiveMassTargetRecordedIsTrue :
      positiveMassTargetRecorded ≡ true
    positiveMassConstructed :
      Bool
    positiveMassConstructedIsFalse :
      positiveMassConstructed ≡ false
    pressureBootstrapClosed :
      Bool
    pressureBootstrapClosedIsFalse :
      pressureBootstrapClosed ≡ false

open NSMicrolocalDefectMassAdmissibilityQuotientBoundary public

canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary :
  NSMicrolocalDefectMassAdmissibilityQuotientBoundary
canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary =
  nsMicrolocalDefectMassAdmissibilityQuotientBoundary
    canonicalLocalizedVorticity
    refl
    canonicalDefectMeasure
    refl
    canonicalMaximalStrainGraph
    refl
    canonicalPositiveMassTarget
    refl
    canonicalMicrolocalDefectMassDependencyLinks
    refl
    microlocalDefectMassDependencyLinkCount
    refl
    true
    refl
    false
    refl
    false
    refl

data MicrolocalDefectMassConstructionStep : Set where
  chooseSuitableBlowupSequenceWithPositiveCriticalResidual :
    MicrolocalDefectMassConstructionStep
  rescaleAtParabolicBlowupScales :
    MicrolocalDefectMassConstructionStep
  chooseLittlewoodPaleyShellAtReciprocalScale :
    MicrolocalDefectMassConstructionStep
  localizeVorticityToCriticalFrequencyShell :
    MicrolocalDefectMassConstructionStep
  extractSemiclassicalDefectMeasure :
    MicrolocalDefectMassConstructionStep
  identifyMaximalStrainEigenbundleGraph :
    MicrolocalDefectMassConstructionStep
  provePositiveMassNearSigmaInMaximalStrainGraph :
    MicrolocalDefectMassConstructionStep
  closePressureNonlocalityBootstrap :
    MicrolocalDefectMassConstructionStep
  feedSigmaNonRadialCommutatorLowerBound :
    MicrolocalDefectMassConstructionStep
  feedFiniteDepthBTBoundaryLeakageDiagnostic :
    MicrolocalDefectMassConstructionStep

canonicalMicrolocalDefectMassConstructionSteps :
  List MicrolocalDefectMassConstructionStep
canonicalMicrolocalDefectMassConstructionSteps =
  chooseSuitableBlowupSequenceWithPositiveCriticalResidual
  ∷ rescaleAtParabolicBlowupScales
  ∷ chooseLittlewoodPaleyShellAtReciprocalScale
  ∷ localizeVorticityToCriticalFrequencyShell
  ∷ extractSemiclassicalDefectMeasure
  ∷ identifyMaximalStrainEigenbundleGraph
  ∷ provePositiveMassNearSigmaInMaximalStrainGraph
  ∷ closePressureNonlocalityBootstrap
  ∷ feedSigmaNonRadialCommutatorLowerBound
  ∷ feedFiniteDepthBTBoundaryLeakageDiagnostic
  ∷ []

microlocalDefectMassConstructionStepCount : Nat
microlocalDefectMassConstructionStepCount =
  listLength canonicalMicrolocalDefectMassConstructionSteps

microlocalDefectMassConstructionStepCountIs10 :
  microlocalDefectMassConstructionStepCount ≡ 10
microlocalDefectMassConstructionStepCountIs10 =
  refl

data MicrolocalDefectMassBlocker : Set where
  missingBlowupProfileCompactnessAtCriticalResidual :
    MicrolocalDefectMassBlocker
  missingLittlewoodPaleyVorticityTightness :
    MicrolocalDefectMassBlocker
  missingSemiclassicalMeasureExtractionWithPressure :
    MicrolocalDefectMassBlocker
  missingPositiveMassInMaximalStrainGraph :
    MicrolocalDefectMassBlocker
  missingSigmaNeighborhoodMassPersistence :
    MicrolocalDefectMassBlocker
  missingPressureNonlocalityBootstrap :
    MicrolocalDefectMassBlocker
  missingBranchSpreadPressureLeakage :
    MicrolocalDefectMassBlocker
  missingWedgeCollapsePressureStarvation :
    MicrolocalDefectMassBlocker
  missingNoPositiveCriticalResidualCascade :
    MicrolocalDefectMassBlocker
  missingFullLocalDefectMonotonicity :
    MicrolocalDefectMassBlocker
  missingMechanismExhaustionForFullClayNS :
    MicrolocalDefectMassBlocker
  clayNavierStokesPromotionClosed :
    MicrolocalDefectMassBlocker

canonicalMicrolocalDefectMassBlockers :
  List MicrolocalDefectMassBlocker
canonicalMicrolocalDefectMassBlockers =
  missingBlowupProfileCompactnessAtCriticalResidual
  ∷ missingLittlewoodPaleyVorticityTightness
  ∷ missingSemiclassicalMeasureExtractionWithPressure
  ∷ missingPositiveMassInMaximalStrainGraph
  ∷ missingSigmaNeighborhoodMassPersistence
  ∷ missingPressureNonlocalityBootstrap
  ∷ missingBranchSpreadPressureLeakage
  ∷ missingWedgeCollapsePressureStarvation
  ∷ missingNoPositiveCriticalResidualCascade
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

microlocalDefectMassBlockerCount : Nat
microlocalDefectMassBlockerCount =
  listLength canonicalMicrolocalDefectMassBlockers

microlocalDefectMassBlockerCountIs12 :
  microlocalDefectMassBlockerCount ≡ 12
microlocalDefectMassBlockerCountIs12 =
  refl

data MicrolocalDefectMassSupportRow : Set where
  sprint162CriticalResidualBoundarySupport :
    MicrolocalDefectMassSupportRow
  sprint163AngularStrainSymbolDegeneracySupport :
    MicrolocalDefectMassSupportRow
  sprint163MaximalEigenbundleNonOrientabilitySupport :
    MicrolocalDefectMassSupportRow
  sprint164MicrolocalAlignmentConcentrationTargetSupport :
    MicrolocalDefectMassSupportRow
  sprint164AngularDegeneracyCommutatorTargetSupport :
    MicrolocalDefectMassSupportRow
  sigmaNonRadialLowerBoundTargetSupport :
    MicrolocalDefectMassSupportRow
  btBoundaryDefectLeakageTargetSupport :
    MicrolocalDefectMassSupportRow

canonicalMicrolocalDefectMassSupportRows :
  List MicrolocalDefectMassSupportRow
canonicalMicrolocalDefectMassSupportRows =
  sprint162CriticalResidualBoundarySupport
  ∷ sprint163AngularStrainSymbolDegeneracySupport
  ∷ sprint163MaximalEigenbundleNonOrientabilitySupport
  ∷ sprint164MicrolocalAlignmentConcentrationTargetSupport
  ∷ sprint164AngularDegeneracyCommutatorTargetSupport
  ∷ sigmaNonRadialLowerBoundTargetSupport
  ∷ btBoundaryDefectLeakageTargetSupport
  ∷ []

microlocalDefectMassSupportRowCount : Nat
microlocalDefectMassSupportRowCount =
  listLength canonicalMicrolocalDefectMassSupportRows

microlocalDefectMassSupportRowCountIs7 :
  microlocalDefectMassSupportRowCount ≡ 7
microlocalDefectMassSupportRowCountIs7 =
  refl

data MicrolocalDefectMassStatusRow : Set where
  exactRemainingNSGapRecordedStatus :
    MicrolocalDefectMassStatusRow
  blowupSequenceToLPVorticityTypedStatus :
    MicrolocalDefectMassStatusRow
  lpVorticityToDefectMeasureTypedStatus :
    MicrolocalDefectMassStatusRow
  maximalStrainGraphMassTargetTypedStatus :
    MicrolocalDefectMassStatusRow
  pressureNonlocalityBootstrapBlockerTypedStatus :
    MicrolocalDefectMassStatusRow
  admissibilityQuotientBoundaryTypedStatus :
    MicrolocalDefectMassStatusRow
  positiveMassTargetRecordedTrueStatus :
    MicrolocalDefectMassStatusRow
  sigmaLowerBoundConsumerTypedStatus :
    MicrolocalDefectMassStatusRow
  btBoundaryLeakageConsumerTypedStatus :
    MicrolocalDefectMassStatusRow
  microlocalDefectMassConstructedFalseStatus :
    MicrolocalDefectMassStatusRow
  positiveMassConstructedFalseStatus :
    MicrolocalDefectMassStatusRow
  noPersistentPositiveResidualFalseStatus :
    MicrolocalDefectMassStatusRow
  clayPromotionFalseStatus :
    MicrolocalDefectMassStatusRow

canonicalMicrolocalDefectMassStatusRows :
  List MicrolocalDefectMassStatusRow
canonicalMicrolocalDefectMassStatusRows =
  exactRemainingNSGapRecordedStatus
  ∷ blowupSequenceToLPVorticityTypedStatus
  ∷ lpVorticityToDefectMeasureTypedStatus
  ∷ maximalStrainGraphMassTargetTypedStatus
  ∷ pressureNonlocalityBootstrapBlockerTypedStatus
  ∷ admissibilityQuotientBoundaryTypedStatus
  ∷ positiveMassTargetRecordedTrueStatus
  ∷ sigmaLowerBoundConsumerTypedStatus
  ∷ btBoundaryLeakageConsumerTypedStatus
  ∷ microlocalDefectMassConstructedFalseStatus
  ∷ positiveMassConstructedFalseStatus
  ∷ noPersistentPositiveResidualFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

microlocalDefectMassStatusRowCount : Nat
microlocalDefectMassStatusRowCount =
  listLength canonicalMicrolocalDefectMassStatusRows

microlocalDefectMassStatusRowCountIs13 :
  microlocalDefectMassStatusRowCount ≡ 13
microlocalDefectMassStatusRowCountIs13 =
  refl

NSMicrolocalDefectMassConstructionBoundaryRecorded : Bool
NSMicrolocalDefectMassConstructionBoundaryRecorded =
  true

BlowupSequenceToLPVorticityTyped : Bool
BlowupSequenceToLPVorticityTyped =
  true

LPVorticityToSemiclassicalDefectMeasureTyped : Bool
LPVorticityToSemiclassicalDefectMeasureTyped =
  true

MaximalStrainGraphMassTargetTyped : Bool
MaximalStrainGraphMassTargetTyped =
  true

PressureNonlocalityBootstrapBlockerTyped : Bool
PressureNonlocalityBootstrapBlockerTyped =
  true

SigmaNonRadialLowerBoundConsumerTyped : Bool
SigmaNonRadialLowerBoundConsumerTyped =
  true

BTBoundaryDefectLeakageConsumerTyped : Bool
BTBoundaryDefectLeakageConsumerTyped =
  true

SigmaNonRadialTargetAnchorImported : Bool
SigmaNonRadialTargetAnchorImported =
  true

BTBoundaryDefectLeakageAnchorImported : Bool
BTBoundaryDefectLeakageAnchorImported =
  true

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

PositiveMassInMaximalStrainGraphProved : Bool
PositiveMassInMaximalStrainGraphProved =
  false

PressureNonlocalityBootstrapClosed : Bool
PressureNonlocalityBootstrapClosed =
  false

BranchSpreadPressureLeakage : Bool
BranchSpreadPressureLeakage =
  false

WedgeCollapsePressureStarvation : Bool
WedgeCollapsePressureStarvation =
  false

NoPersistentPositiveNSCriticalResidual : Bool
NoPersistentPositiveNSCriticalResidual =
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

organizationString : String
organizationString =
  "O: NSMicrolocalDefectMassConstructionBoundary is worker lane 3's fail-closed NS analytic-gap receipt."

requirementString : String
requirementString =
  "R: Type the exact remaining NS gap: blowup sequence -> LP localized vorticity -> semiclassical defect measure -> positive maximal-strain graph mass near Sigma, with pressure nonlocality bootstrap still open."

codeArtifactString : String
codeArtifactString =
  "C: The module exports carriers for the LP-shell -> defect-measure -> L_max-mass -> pressure-bootstrap chain, an admissibility/quotient boundary, canonical rows, imported anchors, equality receipts, and false Clay promotion guards."

stateString : String
stateString =
  "S: Sprint162/163/164, Sigma non-radial lower-bound target, and BTNS boundary leakage target are consumed; the microlocal defect mass and pressure bootstrap remain unproved."

latticeString : String
latticeString =
  "L: critical residual -> blowup profile -> LP vorticity shell -> semiclassical defect measure -> positive mass target on L_max graph near Sigma -> pressure nonlocality bootstrap -> commutator/leakage consumers -> full local monotonicity blocker."

proposalString : String
proposalString =
  "P: Promote only the exact statement of the remaining analytic gap; do not promote the microlocal mass construction, pressure leakage, residual depletion, mechanism exhaustion, or Clay NS."

governanceString : String
governanceString =
  "G: All theorem-completion and Clay flags are false; this surface is an executable boundary receipt for the next analytic calculation."

gapString : String
gapString =
  "F: Missing evidence is the compactness/LP-tightness/semiclassical extraction argument with pressure nonlocality, plus positive mass in the maximal-strain graph near Sigma and the bootstrap that feeds residual depletion."

record NSMicrolocalDefectMassConstructionORCSLPGF : Set where
  constructor nsMicrolocalDefectMassConstructionORCSLPGF
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

open NSMicrolocalDefectMassConstructionORCSLPGF public

canonicalNSMicrolocalDefectMassConstructionORCSLPGF :
  NSMicrolocalDefectMassConstructionORCSLPGF
canonicalNSMicrolocalDefectMassConstructionORCSLPGF =
  nsMicrolocalDefectMassConstructionORCSLPGF
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

record NSMicrolocalDefectMassConstructionBoundaryReceipt : Setω where
  constructor nsMicrolocalDefectMassConstructionBoundaryReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "MicrolocalDefectMassConstruction"

    sprint162Anchor :
      S162.NSSprint162CriticalResidualBoundaryReceipt
    sprint162AnchorIsCanonical :
      sprint162Anchor
      ≡
      S162.canonicalNSSprint162CriticalResidualBoundaryReceipt

    sprint163Anchor :
      S163.NSSprint163TopologicalAlignmentObstructionBoundaryReceipt
    sprint163AnchorIsCanonical :
      sprint163Anchor
      ≡
      S163.canonicalNSSprint163TopologicalAlignmentObstructionBoundaryReceipt

    sprint164Anchor :
      S164.NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt
    sprint164AnchorIsCanonical :
      sprint164Anchor
      ≡
      S164.canonicalNSSprint164MicrolocalTopologicalBridgeBoundaryReceipt

    sigmaNonRadialTargetAnchorImported :
      SigmaNonRadialTargetAnchorImported ≡ true

    btBoundaryDefectLeakageAnchor :
      BTNS.BTNSBoundaryDefectLeakageTargetReceipt
    btBoundaryDefectLeakageAnchorIsCanonical :
      btBoundaryDefectLeakageAnchor
      ≡
      BTNS.canonicalBTNSBoundaryDefectLeakageTargetReceipt

    blowupSequence :
      NSBlowupSequenceCarrier
    blowupSequenceIsCanonical :
      blowupSequence ≡ canonicalBlowupSequence
    criticalScale :
      CriticalScaleCarrier
    criticalScaleIsCanonical :
      criticalScale ≡ canonicalCriticalScale
    lpFrequencyScale :
      LittlewoodPaleyFrequencyScale
    lpFrequencyScaleIsCanonical :
      lpFrequencyScale ≡ canonicalLPFrequencyScale
    localizedVorticity :
      LocalizedVorticityCarrier
    localizedVorticityIsCanonical :
      localizedVorticity ≡ canonicalLocalizedVorticity
    defectMeasure :
      SemiclassicalDefectMeasureCarrier
    defectMeasureIsCanonical :
      defectMeasure ≡ canonicalDefectMeasure
    maximalStrainGraph :
      MaximalStrainGraphCarrier
    maximalStrainGraphIsCanonical :
      maximalStrainGraph ≡ canonicalMaximalStrainGraph
    positiveMassTarget :
      PositiveMassTarget
    positiveMassTargetIsCanonical :
      positiveMassTarget ≡ canonicalPositiveMassTarget
    pressureBootstrap :
      PressureNonlocalityBootstrap
    pressureBootstrapIsCanonical :
      pressureBootstrap ≡ canonicalPressureBootstrap
    admissibilityQuotientBoundary :
      NSMicrolocalDefectMassAdmissibilityQuotientBoundary
    admissibilityQuotientBoundaryIsCanonical :
      admissibilityQuotientBoundary
      ≡
      canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary

    orcslpgf :
      NSMicrolocalDefectMassConstructionORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf
      ≡
      canonicalNSMicrolocalDefectMassConstructionORCSLPGF

    constructionSteps :
      List MicrolocalDefectMassConstructionStep
    constructionStepsAreCanonical :
      constructionSteps ≡ canonicalMicrolocalDefectMassConstructionSteps
    supportRows :
      List MicrolocalDefectMassSupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalMicrolocalDefectMassSupportRows
    statusRows :
      List MicrolocalDefectMassStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalMicrolocalDefectMassStatusRows
    dependencyLinks :
      List MicrolocalDefectMassDependencyLink
    dependencyLinksAreCanonical :
      dependencyLinks ≡ canonicalMicrolocalDefectMassDependencyLinks
    blockerRows :
      List MicrolocalDefectMassBlocker
    blockerRowsAreCanonical :
      blockerRows ≡ canonicalMicrolocalDefectMassBlockers

    constructionStepCount :
      Nat
    constructionStepCountIs10 :
      constructionStepCount ≡ 10
    supportRowCount :
      Nat
    supportRowCountIs7 :
      supportRowCount ≡ 7
    statusRowCount :
      Nat
    statusRowCountIs13 :
      statusRowCount ≡ 13
    dependencyLinkCount :
      Nat
    dependencyLinkCountIs6 :
      dependencyLinkCount ≡ 6
    blockerRowCount :
      Nat
    blockerRowCountIs12 :
      blockerRowCount ≡ 12

    sprint162CriticalResidualBoundaryRecorded :
      S162.CriticalResidualBoundaryRecorded ≡ true
    sprint162NoPersistentResidualStillFalse :
      S162.NoPersistentPositiveNSCriticalResidual ≡ false
    sprint163SigmaVocabularyRecorded :
      S163.AngularStrainSymbolDegeneracyRecorded ≡ true
    sprint163MaxEigenbundleNonOrientabilityRecorded :
      S163.MaximalEigenbundleNonOrientabilityRecorded ≡ true
    sprint164MicrolocalAlignmentTargetRecorded :
      S164.MicrolocalAlignmentConcentrationTargetRecorded ≡ true
    sprint164MicrolocalAlignmentLemmaStillFalse :
      S164.MicrolocalAlignmentConcentrationLemma ≡ false
    sprint164PressureCommutatorTargetRecorded :
      S164.AngularDegeneracyPressureCommutatorGainTargetRecorded ≡ true
    sprint164PressureCommutatorGainStillFalse :
      S164.AngularDegeneracyPressureCommutatorGain ≡ false
    sigmaLowerBoundTargetStillFalse :
      Sigma.SigmaNonRadialCommutatorLowerBound ≡ false
    sigmaMicrolocalDefectMassStillFalse :
      Sigma.MicrolocalDefectMassConstructed ≡ false
    btBoundaryLeakageTargetStillFalse :
      BTNS.FiniteDepthNSTopologicalLeakage ≡ false

    boundaryRecorded :
      NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
    blowupSequenceToLPVorticityTyped :
      BlowupSequenceToLPVorticityTyped ≡ true
    lpVorticityToDefectMeasureTyped :
      LPVorticityToSemiclassicalDefectMeasureTyped ≡ true
    maximalStrainGraphMassTargetTyped :
      MaximalStrainGraphMassTargetTyped ≡ true
    pressureNonlocalityBootstrapBlockerTyped :
      PressureNonlocalityBootstrapBlockerTyped ≡ true
    admissibilityQuotientPositiveMassTargetRecorded :
      positiveMassTargetRecorded
        canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary
      ≡
      true
    admissibilityQuotientPositiveMassConstructedFalse :
      positiveMassConstructed
        canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary
      ≡
      false
    admissibilityQuotientPressureBootstrapClosedFalse :
      pressureBootstrapClosed
        canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary
      ≡
      false
    sigmaNonRadialLowerBoundConsumerTyped :
      SigmaNonRadialLowerBoundConsumerTyped ≡ true
    btBoundaryDefectLeakageConsumerTyped :
      BTBoundaryDefectLeakageConsumerTyped ≡ true
    btBoundaryDefectLeakageAnchorImported :
      BTBoundaryDefectLeakageAnchorImported ≡ true

    microlocalDefectMassConstructedFalse :
      MicrolocalDefectMassConstructed ≡ false
    positiveMassInMaximalStrainGraphProvedFalse :
      PositiveMassInMaximalStrainGraphProved ≡ false
    pressureNonlocalityBootstrapClosedFalse :
      PressureNonlocalityBootstrapClosed ≡ false
    branchSpreadPressureLeakageFalse :
      BranchSpreadPressureLeakage ≡ false
    wedgeCollapsePressureStarvationFalse :
      WedgeCollapsePressureStarvation ≡ false
    noPersistentPositiveNSCriticalResidualFalse :
      NoPersistentPositiveNSCriticalResidual ≡ false
    fullLocalDefectMonotonicityFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionForFullClayNSFalse :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedSnakeFalse :
      full_clay_ns_solved ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSMicrolocalDefectMassConstructionBoundaryReceipt public

canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt :
  NSMicrolocalDefectMassConstructionBoundaryReceipt
canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt =
  record
    { gateName =
        "MicrolocalDefectMassConstruction"
    ; gateNameIsCanonical =
        refl
    ; sprint162Anchor =
        S162.canonicalNSSprint162CriticalResidualBoundaryReceipt
    ; sprint162AnchorIsCanonical =
        refl
    ; sprint163Anchor =
        S163.canonicalNSSprint163TopologicalAlignmentObstructionBoundaryReceipt
    ; sprint163AnchorIsCanonical =
        refl
    ; sprint164Anchor =
        S164.canonicalNSSprint164MicrolocalTopologicalBridgeBoundaryReceipt
    ; sprint164AnchorIsCanonical =
        refl
    ; sigmaNonRadialTargetAnchorImported =
        refl
    ; btBoundaryDefectLeakageAnchor =
        BTNS.canonicalBTNSBoundaryDefectLeakageTargetReceipt
    ; btBoundaryDefectLeakageAnchorIsCanonical =
        refl
    ; blowupSequence =
        canonicalBlowupSequence
    ; blowupSequenceIsCanonical =
        refl
    ; criticalScale =
        canonicalCriticalScale
    ; criticalScaleIsCanonical =
        refl
    ; lpFrequencyScale =
        canonicalLPFrequencyScale
    ; lpFrequencyScaleIsCanonical =
        refl
    ; localizedVorticity =
        canonicalLocalizedVorticity
    ; localizedVorticityIsCanonical =
        refl
    ; defectMeasure =
        canonicalDefectMeasure
    ; defectMeasureIsCanonical =
        refl
    ; maximalStrainGraph =
        canonicalMaximalStrainGraph
    ; maximalStrainGraphIsCanonical =
        refl
    ; positiveMassTarget =
        canonicalPositiveMassTarget
    ; positiveMassTargetIsCanonical =
        refl
    ; pressureBootstrap =
        canonicalPressureBootstrap
    ; pressureBootstrapIsCanonical =
        refl
    ; admissibilityQuotientBoundary =
        canonicalNSMicrolocalDefectMassAdmissibilityQuotientBoundary
    ; admissibilityQuotientBoundaryIsCanonical =
        refl
    ; orcslpgf =
        canonicalNSMicrolocalDefectMassConstructionORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; constructionSteps =
        canonicalMicrolocalDefectMassConstructionSteps
    ; constructionStepsAreCanonical =
        refl
    ; supportRows =
        canonicalMicrolocalDefectMassSupportRows
    ; supportRowsAreCanonical =
        refl
    ; statusRows =
        canonicalMicrolocalDefectMassStatusRows
    ; statusRowsAreCanonical =
        refl
    ; dependencyLinks =
        canonicalMicrolocalDefectMassDependencyLinks
    ; dependencyLinksAreCanonical =
        refl
    ; blockerRows =
        canonicalMicrolocalDefectMassBlockers
    ; blockerRowsAreCanonical =
        refl
    ; constructionStepCount =
        microlocalDefectMassConstructionStepCount
    ; constructionStepCountIs10 =
        refl
    ; supportRowCount =
        microlocalDefectMassSupportRowCount
    ; supportRowCountIs7 =
        refl
    ; statusRowCount =
        microlocalDefectMassStatusRowCount
    ; statusRowCountIs13 =
        refl
    ; dependencyLinkCount =
        microlocalDefectMassDependencyLinkCount
    ; dependencyLinkCountIs6 =
        refl
    ; blockerRowCount =
        microlocalDefectMassBlockerCount
    ; blockerRowCountIs12 =
        refl
    ; sprint162CriticalResidualBoundaryRecorded =
        refl
    ; sprint162NoPersistentResidualStillFalse =
        refl
    ; sprint163SigmaVocabularyRecorded =
        refl
    ; sprint163MaxEigenbundleNonOrientabilityRecorded =
        refl
    ; sprint164MicrolocalAlignmentTargetRecorded =
        refl
    ; sprint164MicrolocalAlignmentLemmaStillFalse =
        refl
    ; sprint164PressureCommutatorTargetRecorded =
        refl
    ; sprint164PressureCommutatorGainStillFalse =
        refl
    ; sigmaLowerBoundTargetStillFalse =
        refl
    ; sigmaMicrolocalDefectMassStillFalse =
        refl
    ; btBoundaryLeakageTargetStillFalse =
        refl
    ; boundaryRecorded =
        refl
    ; blowupSequenceToLPVorticityTyped =
        refl
    ; lpVorticityToDefectMeasureTyped =
        refl
    ; maximalStrainGraphMassTargetTyped =
        refl
    ; pressureNonlocalityBootstrapBlockerTyped =
        refl
    ; admissibilityQuotientPositiveMassTargetRecorded =
        refl
    ; admissibilityQuotientPositiveMassConstructedFalse =
        refl
    ; admissibilityQuotientPressureBootstrapClosedFalse =
        refl
    ; sigmaNonRadialLowerBoundConsumerTyped =
        refl
    ; btBoundaryDefectLeakageConsumerTyped =
        refl
    ; btBoundaryDefectLeakageAnchorImported =
        refl
    ; microlocalDefectMassConstructedFalse =
        refl
    ; positiveMassInMaximalStrainGraphProvedFalse =
        refl
    ; pressureNonlocalityBootstrapClosedFalse =
        refl
    ; branchSpreadPressureLeakageFalse =
        refl
    ; wedgeCollapsePressureStarvationFalse =
        refl
    ; noPersistentPositiveNSCriticalResidualFalse =
        refl
    ; fullLocalDefectMonotonicityFalse =
        refl
    ; mechanismExhaustionForFullClayNSFalse =
        refl
    ; fullClayNSSolvedSnakeFalse =
        refl
    ; fullClayNSSolvedFalse =
        refl
    ; clayNavierStokesPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    }

nsMicrolocalDefectMassConstructionBoundaryIsRecorded :
  NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
nsMicrolocalDefectMassConstructionBoundaryIsRecorded =
  refl

nsMicrolocalDefectMassConstructionKeepsMassFalse :
  microlocalDefectMassConstructedFalse
    canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
  ≡
  refl
nsMicrolocalDefectMassConstructionKeepsMassFalse =
  refl

nsMicrolocalDefectMassConstructionKeepsPressureBootstrapFalse :
  pressureNonlocalityBootstrapClosedFalse
    canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
  ≡
  refl
nsMicrolocalDefectMassConstructionKeepsPressureBootstrapFalse =
  refl

nsMicrolocalDefectMassConstructionKeepsClayFalse :
  clayNavierStokesPromotedFalse
    canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
  ≡
  refl
nsMicrolocalDefectMassConstructionKeepsClayFalse =
  refl
