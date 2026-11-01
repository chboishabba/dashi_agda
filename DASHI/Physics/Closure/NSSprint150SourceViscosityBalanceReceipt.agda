module DASHI.Physics.Closure.NSSprint150SourceViscosityBalanceReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_+_; _≤_)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSMigrationInitiationThresholdConstantsReceipt as Constants
import DASHI.Physics.Closure.NSSprint149ScalingConsistencyGateReceipt as S149

------------------------------------------------------------------------
-- Sprint 150 source-integral / retained-viscosity balance receipt.
--
-- This module advances the Hou-Luo concentration route by isolating the
-- exact analytic balance needed after Sprint 149:
--
--   SourceIntegralLowerBoundForMigratingMaximum
--   RetainedViscosityLowerBoundAtMigratingMaximum
--   SourceBeatsRetainedViscosityAtScaleDelta
--
-- It does not prove any of those theorems.  The checked content is the
-- normalized obligation surface: concrete decomposition rows, exact counts,
-- inherited inequality directions from Sprint 147 constants, and fail-closed
-- guards that prevent treating numerical support as Clay promotion.

sprint150SourceViscosityLedgerClosed : Bool
sprint150SourceViscosityLedgerClosed = true

sprint149ScalingConsistencyAnchored : Bool
sprint149ScalingConsistencyAnchored = true

sprint149ScalingConsistencyStillOpen : Bool
sprint149ScalingConsistencyStillOpen =
  S149.ScalingConsistencyForHouLuoConcentrationOpen

sprint149ScalingConsistencyStillFalse : Bool
sprint149ScalingConsistencyStillFalse =
  S149.ScalingConsistencyForHouLuoConcentration

sprint149NumericalSourceSupportInherited : Bool
sprint149NumericalSourceSupportInherited =
  S149.numericalSourceLowerBoundSupport

sprint149SourceAnalyticTheoremStillFalse : Bool
sprint149SourceAnalyticTheoremStillFalse =
  S149.SourceLowerBoundAnalyticTheorem

normalizedSourceObserved : Nat
normalizedSourceObserved =
  Constants.sourceIntegralObservedLowerBound

normalizedSourceRequired : Nat
normalizedSourceRequired =
  Constants.sourceIntegralRequiredLowerBound

sourceDeficitWitness : normalizedSourceRequired ≡ normalizedSourceObserved + 18
sourceDeficitWitness = refl

normalizedRetainedViscosityObserved : Nat
normalizedRetainedViscosityObserved =
  Constants.viscosityRetentionObservedLowerBound

normalizedRetainedViscosityRequired : Nat
normalizedRetainedViscosityRequired =
  Constants.viscosityRetentionRequiredLowerBound

retainedViscosityDeficitWitness :
  normalizedRetainedViscosityRequired
    ≡ normalizedRetainedViscosityObserved + 54
retainedViscosityDeficitWitness = refl

sourceObservedBelowRequired :
  normalizedSourceObserved ≤ normalizedSourceRequired
sourceObservedBelowRequired =
  Constants.sourceIntegralBelowRequired

retainedViscosityObservedBelowRequired :
  normalizedRetainedViscosityObserved ≤ normalizedRetainedViscosityRequired
retainedViscosityObservedBelowRequired =
  Constants.viscosityRetentionBelowRequired

offAxisGainAboveBaseline :
  Constants.normalizedBaselineUnit
    ≤ Constants.offAxisGainObservedUpperDemand
offAxisGainAboveBaseline =
  Constants.offAxisGainExceedsBaseline

logFeedbackAboveBaseline :
  Constants.normalizedBaselineUnit
    ≤ Constants.logFeedbackObservedUpperDemand
logFeedbackAboveBaseline =
  Constants.logFeedbackExceedsBaseline

SourceIntegralLowerBoundForMigratingMaximum : Bool
SourceIntegralLowerBoundForMigratingMaximum = false

SourceIntegralLowerBoundForMigratingMaximumOpen : Bool
SourceIntegralLowerBoundForMigratingMaximumOpen = true

RetainedViscosityLowerBoundAtMigratingMaximum : Bool
RetainedViscosityLowerBoundAtMigratingMaximum = false

RetainedViscosityLowerBoundAtMigratingMaximumOpen : Bool
RetainedViscosityLowerBoundAtMigratingMaximumOpen = true

SourceBeatsRetainedViscosityAtScaleDelta : Bool
SourceBeatsRetainedViscosityAtScaleDelta = false

SourceBeatsRetainedViscosityAtScaleDeltaOpen : Bool
SourceBeatsRetainedViscosityAtScaleDeltaOpen = true

LocalizedSourceViscosityBalanceAtMigratingMaximum : Bool
LocalizedSourceViscosityBalanceAtMigratingMaximum = false

LocalizedSourceViscosityBalanceAtMigratingMaximumOpen : Bool
LocalizedSourceViscosityBalanceAtMigratingMaximumOpen = true

MigrationInitiationThresholdForLargeDataPromotedBySprint150 : Bool
MigrationInitiationThresholdForLargeDataPromotedBySprint150 = false

ScalingConsistencyForHouLuoConcentrationPromotedBySprint150 : Bool
ScalingConsistencyForHouLuoConcentrationPromotedBySprint150 = false

SymmetricHouLuoBKMFinite : Bool
SymmetricHouLuoBKMFinite = false

fullNavierStokesSolutionConstructed : Bool
fullNavierStokesSolutionConstructed = false

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint149AnchorKeepsScalingConsistencyOpen :
  sprint149ScalingConsistencyStillOpen ≡ true
sprint149AnchorKeepsScalingConsistencyOpen = refl

sprint149AnchorKeepsScalingConsistencyFalse :
  sprint149ScalingConsistencyStillFalse ≡ false
sprint149AnchorKeepsScalingConsistencyFalse = refl

sprint150KeepsSourceLowerBoundFalse :
  SourceIntegralLowerBoundForMigratingMaximum ≡ false
sprint150KeepsSourceLowerBoundFalse = refl

sprint150KeepsRetainedViscosityFalse :
  RetainedViscosityLowerBoundAtMigratingMaximum ≡ false
sprint150KeepsRetainedViscosityFalse = refl

sprint150KeepsBalanceFalse :
  SourceBeatsRetainedViscosityAtScaleDelta ≡ false
sprint150KeepsBalanceFalse = refl

sprint150KeepsLocalizedBalanceFalse :
  LocalizedSourceViscosityBalanceAtMigratingMaximum ≡ false
sprint150KeepsLocalizedBalanceFalse = refl

sprint150KeepsFullClayNSFalse :
  full_clay_ns_solved ≡ false
sprint150KeepsFullClayNSFalse = refl

sprint150KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint150KeepsClayPromotionFalse = refl

data SourceIntegralComponent : Set where
  streamFunctionConcavityWindow :
    SourceIntegralComponent

  radialGammaGradientWindow :
    SourceIntegralComponent

  offAxisResidenceTimeWindow :
    SourceIntegralComponent

  signCoherenceAtMigratingMaximum :
    SourceIntegralComponent

  cutoffLocalizedSourceMass :
    SourceIntegralComponent

  boundaryImageCorrectionBudget :
    SourceIntegralComponent

  nonlocalTailControlBudget :
    SourceIntegralComponent

  amplitudeNormalizationAgainstLargeData :
    SourceIntegralComponent

canonicalSourceIntegralComponents : List SourceIntegralComponent
canonicalSourceIntegralComponents =
  streamFunctionConcavityWindow
  ∷ radialGammaGradientWindow
  ∷ offAxisResidenceTimeWindow
  ∷ signCoherenceAtMigratingMaximum
  ∷ cutoffLocalizedSourceMass
  ∷ boundaryImageCorrectionBudget
  ∷ nonlocalTailControlBudget
  ∷ amplitudeNormalizationAgainstLargeData
  ∷ []

sourceIntegralComponentCount : Nat
sourceIntegralComponentCount = 8

data RetainedViscosityComponent : Set where
  localizedDiffusionCore :
    RetainedViscosityComponent

  cutoffGradientLoss :
    RetainedViscosityComponent

  annularFluxLoss :
    RetainedViscosityComponent

  radialCurvatureLoss :
    RetainedViscosityComponent

  transportResidenceLoss :
    RetainedViscosityComponent

  boundaryLayerLeakage :
    RetainedViscosityComponent

  largeDataUniformityLoss :
    RetainedViscosityComponent

canonicalRetainedViscosityComponents : List RetainedViscosityComponent
canonicalRetainedViscosityComponents =
  localizedDiffusionCore
  ∷ cutoffGradientLoss
  ∷ annularFluxLoss
  ∷ radialCurvatureLoss
  ∷ transportResidenceLoss
  ∷ boundaryLayerLeakage
  ∷ largeDataUniformityLoss
  ∷ []

retainedViscosityComponentCount : Nat
retainedViscosityComponentCount = 7

data SourceViscosityAnalyticLemma : Set where
  sourceIntegralLowerBoundForMigratingMaximumLemma :
    SourceViscosityAnalyticLemma

  retainedViscosityLowerBoundAtMigratingMaximumLemma :
    SourceViscosityAnalyticLemma

  offAxisGainAbsorptionLemma :
    SourceViscosityAnalyticLemma

  logFeedbackAbsorptionLemma :
    SourceViscosityAnalyticLemma

  cutoffLocalizationErrorLemma :
    SourceViscosityAnalyticLemma

  boundaryImageCorrectionLemma :
    SourceViscosityAnalyticLemma

  nonlocalTailSmallnessLemma :
    SourceViscosityAnalyticLemma

  largeDataUniformityOfConstantsLemma :
    SourceViscosityAnalyticLemma

  localizedSourceBeatsRetainedViscosityLemma :
    SourceViscosityAnalyticLemma

canonicalSourceViscosityAnalyticLemmas :
  List SourceViscosityAnalyticLemma
canonicalSourceViscosityAnalyticLemmas =
  sourceIntegralLowerBoundForMigratingMaximumLemma
  ∷ retainedViscosityLowerBoundAtMigratingMaximumLemma
  ∷ offAxisGainAbsorptionLemma
  ∷ logFeedbackAbsorptionLemma
  ∷ cutoffLocalizationErrorLemma
  ∷ boundaryImageCorrectionLemma
  ∷ nonlocalTailSmallnessLemma
  ∷ largeDataUniformityOfConstantsLemma
  ∷ localizedSourceBeatsRetainedViscosityLemma
  ∷ []

sourceViscosityAnalyticLemmaCount : Nat
sourceViscosityAnalyticLemmaCount = 9

data SourceViscosityInequalityRow : Set where
  sourceObservedBelowRequiredRow :
    SourceViscosityInequalityRow

  retainedViscosityObservedBelowRequiredRow :
    SourceViscosityInequalityRow

  offAxisGainAboveBaselineRow :
    SourceViscosityInequalityRow

  logFeedbackAboveBaselineRow :
    SourceViscosityInequalityRow

  sourceDeficitEighteenRow :
    SourceViscosityInequalityRow

  retainedViscosityDeficitFiftyFourRow :
    SourceViscosityInequalityRow

canonicalSourceViscosityInequalityRows :
  List SourceViscosityInequalityRow
canonicalSourceViscosityInequalityRows =
  sourceObservedBelowRequiredRow
  ∷ retainedViscosityObservedBelowRequiredRow
  ∷ offAxisGainAboveBaselineRow
  ∷ logFeedbackAboveBaselineRow
  ∷ sourceDeficitEighteenRow
  ∷ retainedViscosityDeficitFiftyFourRow
  ∷ []

sourceViscosityInequalityRowCount : Nat
sourceViscosityInequalityRowCount = 6

data SourceViscosityBlocker : Set where
  sourceLowerBoundAnalyticTheoremMissing :
    SourceViscosityBlocker

  retainedViscosityLowerBoundMissing :
    SourceViscosityBlocker

  offAxisGainAbsorptionMissing :
    SourceViscosityBlocker

  logFeedbackAbsorptionMissing :
    SourceViscosityBlocker

  cutoffLocalizationErrorMissing :
    SourceViscosityBlocker

  boundaryAndAnnularBudgetMissing :
    SourceViscosityBlocker

  nonlocalTailControlMissing :
    SourceViscosityBlocker

  largeDataUniformityMissing :
    SourceViscosityBlocker

canonicalSourceViscosityBlockers : List SourceViscosityBlocker
canonicalSourceViscosityBlockers =
  sourceLowerBoundAnalyticTheoremMissing
  ∷ retainedViscosityLowerBoundMissing
  ∷ offAxisGainAbsorptionMissing
  ∷ logFeedbackAbsorptionMissing
  ∷ cutoffLocalizationErrorMissing
  ∷ boundaryAndAnnularBudgetMissing
  ∷ nonlocalTailControlMissing
  ∷ largeDataUniformityMissing
  ∷ []

sourceViscosityBlockerCount : Nat
sourceViscosityBlockerCount = 8

data SourceViscosityFalsePromotionGuard : Set where
  doNotPromoteNumericalSourceSupport :
    SourceViscosityFalsePromotionGuard

  doNotPromoteObservedBelowRequiredInequality :
    SourceViscosityFalsePromotionGuard

  doNotPromoteRetainedViscosityDeficit :
    SourceViscosityFalsePromotionGuard

  doNotPromoteOffAxisGainWithoutAbsorption :
    SourceViscosityFalsePromotionGuard

  doNotPromoteLogFeedbackWithoutAbsorption :
    SourceViscosityFalsePromotionGuard

  doNotPromoteLocalizedBalanceWithoutAllLemmas :
    SourceViscosityFalsePromotionGuard

  doNotPromoteClayNSFromSprint150 :
    SourceViscosityFalsePromotionGuard

canonicalSourceViscosityFalsePromotionGuards :
  List SourceViscosityFalsePromotionGuard
canonicalSourceViscosityFalsePromotionGuards =
  doNotPromoteNumericalSourceSupport
  ∷ doNotPromoteObservedBelowRequiredInequality
  ∷ doNotPromoteRetainedViscosityDeficit
  ∷ doNotPromoteOffAxisGainWithoutAbsorption
  ∷ doNotPromoteLogFeedbackWithoutAbsorption
  ∷ doNotPromoteLocalizedBalanceWithoutAllLemmas
  ∷ doNotPromoteClayNSFromSprint150
  ∷ []

sourceViscosityFalsePromotionGuardCount : Nat
sourceViscosityFalsePromotionGuardCount = 7

organizationString : String
organizationString =
  "O: Sprint150 owns the source-integral / retained-viscosity analytic balance for the Hou-Luo migrating-maximum route."

requirementString : String
requirementString =
  "R: Prove a localized source-integral lower bound, retained-viscosity lower bound, off-axis/log absorption, and a source-beats-viscosity inequality at scale delta."

codeArtifactString : String
codeArtifactString =
  "C: The Agda receipt records decomposition rows, required analytic lemmas, inherited inequality directions, exact counts, and false-promotion guards."

stateString : String
stateString =
  "S: Numerical source support is inherited, but source observed is below required, retained viscosity observed is below required, and off-axis/log demands exceed baseline."

latticeString : String
latticeString =
  "L: decomposition rows < analytic lemmas < localized source-viscosity balance < migration threshold < scaling consistency < symmetric BKM < Clay."

proposalString : String
proposalString =
  "P: Calculate the source lower bound and retained-viscosity bound first, then discharge off-axis/log/cutoff/boundary/nonlocal/uniformity lemmas."

governanceString : String
governanceString =
  "G: No Sprint150 row promotes MigrationInitiationThresholdForLargeData, ScalingConsistencyForHouLuoConcentration, SymmetricHouLuoBKMFinite, or Clay NS."

gapString : String
gapString =
  "F: Missing nine analytic lemmas keep LocalizedSourceViscosityBalanceAtMigratingMaximum=false/open and Clay promotion false."

record SourceViscosityORCSLPGF : Set where
  constructor sourceViscosityORCSLPGF
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

open SourceViscosityORCSLPGF public

canonicalSourceViscosityORCSLPGF : SourceViscosityORCSLPGF
canonicalSourceViscosityORCSLPGF =
  sourceViscosityORCSLPGF
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

summaryString : String
summaryString =
  "Sprint150 decomposes the live source-integral / retained-viscosity balance and records the inherited adverse inequality directions; all analytic balance, migration, scaling, BKM, and Clay promotion gates remain false/open."

record SourceViscosityBalanceSurface : Set where
  constructor sourceViscosityBalanceSurface
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "LocalizedSourceViscosityBalanceAtMigratingMaximum"
    anchorReceipt :
      S149.NSSprint149ScalingConsistencyGateReceipt
    anchorReceiptIsCanonical :
      anchorReceipt ≡ S149.canonicalNSSprint149ScalingConsistencyGateReceipt
    constantsReceipt :
      Constants.NSMigrationInitiationThresholdConstantsReceipt
    constantsReceiptIsCanonical :
      constantsReceipt
        ≡ Constants.canonicalNSMigrationInitiationThresholdConstantsReceipt
    orcslpgf :
      SourceViscosityORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalSourceViscosityORCSLPGF
    sourceBelowRequiredField :
      normalizedSourceObserved ≤ normalizedSourceRequired
    retainedViscosityBelowRequiredField :
      normalizedRetainedViscosityObserved ≤ normalizedRetainedViscosityRequired
    sourceDeficitField :
      normalizedSourceRequired ≡ normalizedSourceObserved + 18
    retainedViscosityDeficitField :
      normalizedRetainedViscosityRequired
        ≡ normalizedRetainedViscosityObserved + 54
    offAxisGainAboveBaselineField :
      Constants.normalizedBaselineUnit
        ≤ Constants.offAxisGainObservedUpperDemand
    logFeedbackAboveBaselineField :
      Constants.normalizedBaselineUnit
        ≤ Constants.logFeedbackObservedUpperDemand
    sourceLowerBoundFalseField :
      SourceIntegralLowerBoundForMigratingMaximum ≡ false
    retainedViscosityFalseField :
      RetainedViscosityLowerBoundAtMigratingMaximum ≡ false
    balanceFalseField :
      SourceBeatsRetainedViscosityAtScaleDelta ≡ false
    localizedBalanceFalseField :
      LocalizedSourceViscosityBalanceAtMigratingMaximum ≡ false
    migrationPromotionFalseField :
      MigrationInitiationThresholdForLargeDataPromotedBySprint150 ≡ false
    scalingPromotionFalseField :
      ScalingConsistencyForHouLuoConcentrationPromotedBySprint150 ≡ false
    bkmFalseField :
      SymmetricHouLuoBKMFinite ≡ false
    clayFalseField :
      clayNavierStokesPromoted ≡ false

open SourceViscosityBalanceSurface public

canonicalSourceViscosityBalanceSurface : SourceViscosityBalanceSurface
canonicalSourceViscosityBalanceSurface =
  sourceViscosityBalanceSurface
    "LocalizedSourceViscosityBalanceAtMigratingMaximum"
    refl
    S149.canonicalNSSprint149ScalingConsistencyGateReceipt
    refl
    Constants.canonicalNSMigrationInitiationThresholdConstantsReceipt
    refl
    canonicalSourceViscosityORCSLPGF
    refl
    sourceObservedBelowRequired
    retainedViscosityObservedBelowRequired
    sourceDeficitWitness
    retainedViscosityDeficitWitness
    offAxisGainAboveBaseline
    logFeedbackAboveBaseline
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

data SourceViscosityPromotion : Set where

sourceViscosityPromotionImpossibleHere :
  SourceViscosityPromotion →
  ⊥
sourceViscosityPromotionImpossibleHere ()

record NSSprint150SourceViscosityBalanceReceipt : Set where
  constructor nsSprint150SourceViscosityBalanceReceipt
  field
    surface :
      SourceViscosityBalanceSurface
    surfaceIsCanonical :
      surface ≡ canonicalSourceViscosityBalanceSurface
    sourceComponents :
      List SourceIntegralComponent
    sourceComponentsAreCanonical :
      sourceComponents ≡ canonicalSourceIntegralComponents
    retainedViscosityComponents :
      List RetainedViscosityComponent
    retainedViscosityComponentsAreCanonical :
      retainedViscosityComponents ≡ canonicalRetainedViscosityComponents
    analyticLemmas :
      List SourceViscosityAnalyticLemma
    analyticLemmasAreCanonical :
      analyticLemmas ≡ canonicalSourceViscosityAnalyticLemmas
    inequalityRows :
      List SourceViscosityInequalityRow
    inequalityRowsAreCanonical :
      inequalityRows ≡ canonicalSourceViscosityInequalityRows
    blockers :
      List SourceViscosityBlocker
    blockersAreCanonical :
      blockers ≡ canonicalSourceViscosityBlockers
    falsePromotionGuards :
      List SourceViscosityFalsePromotionGuard
    falsePromotionGuardsAreCanonical :
      falsePromotionGuards ≡ canonicalSourceViscosityFalsePromotionGuards
    summary :
      String
    summaryIsCanonical :
      summary ≡ summaryString

open NSSprint150SourceViscosityBalanceReceipt public

canonicalNSSprint150SourceViscosityBalanceReceipt :
  NSSprint150SourceViscosityBalanceReceipt
canonicalNSSprint150SourceViscosityBalanceReceipt =
  nsSprint150SourceViscosityBalanceReceipt
    canonicalSourceViscosityBalanceSurface
    refl
    canonicalSourceIntegralComponents
    refl
    canonicalRetainedViscosityComponents
    refl
    canonicalSourceViscosityAnalyticLemmas
    refl
    canonicalSourceViscosityInequalityRows
    refl
    canonicalSourceViscosityBlockers
    refl
    canonicalSourceViscosityFalsePromotionGuards
    refl
    summaryString
    refl

sourceViscosityTheoremTuple :
  (sprint150SourceViscosityLedgerClosed ≡ true)
  × (sprint149ScalingConsistencyAnchored ≡ true)
  × (sprint149ScalingConsistencyStillOpen ≡ true)
  × (sprint149ScalingConsistencyStillFalse ≡ false)
  × (sprint149NumericalSourceSupportInherited ≡ true)
  × (sprint149SourceAnalyticTheoremStillFalse ≡ false)
  × (SourceIntegralLowerBoundForMigratingMaximum ≡ false)
  × (SourceIntegralLowerBoundForMigratingMaximumOpen ≡ true)
  × (RetainedViscosityLowerBoundAtMigratingMaximum ≡ false)
  × (RetainedViscosityLowerBoundAtMigratingMaximumOpen ≡ true)
  × (SourceBeatsRetainedViscosityAtScaleDelta ≡ false)
  × (SourceBeatsRetainedViscosityAtScaleDeltaOpen ≡ true)
  × (LocalizedSourceViscosityBalanceAtMigratingMaximum ≡ false)
  × (LocalizedSourceViscosityBalanceAtMigratingMaximumOpen ≡ true)
  × (MigrationInitiationThresholdForLargeDataPromotedBySprint150 ≡ false)
  × (ScalingConsistencyForHouLuoConcentrationPromotedBySprint150 ≡ false)
  × (SymmetricHouLuoBKMFinite ≡ false)
  × (fullNavierStokesSolutionConstructed ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sourceViscosityTheoremTuple =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sourceViscosityCountPackage :
  (sourceIntegralComponentCount ≡ 8)
  × (retainedViscosityComponentCount ≡ 7)
  × (sourceViscosityAnalyticLemmaCount ≡ 9)
  × (sourceViscosityInequalityRowCount ≡ 6)
  × (sourceViscosityBlockerCount ≡ 8)
  × (sourceViscosityFalsePromotionGuardCount ≡ 7)
sourceViscosityCountPackage =
  refl , refl , refl , refl , refl , refl

sourceViscosityInequalityPackage :
  (normalizedSourceRequired ≡ normalizedSourceObserved + 18)
  × (normalizedRetainedViscosityRequired
      ≡ normalizedRetainedViscosityObserved + 54)
  × (normalizedSourceObserved ≤ normalizedSourceRequired)
  × (normalizedRetainedViscosityObserved ≤ normalizedRetainedViscosityRequired)
  × (Constants.normalizedBaselineUnit
      ≤ Constants.offAxisGainObservedUpperDemand)
  × (Constants.normalizedBaselineUnit
      ≤ Constants.logFeedbackObservedUpperDemand)
sourceViscosityInequalityPackage =
  sourceDeficitWitness ,
  retainedViscosityDeficitWitness ,
  sourceObservedBelowRequired ,
  retainedViscosityObservedBelowRequired ,
  offAxisGainAboveBaseline ,
  logFeedbackAboveBaseline

sourceViscosityFailClosedPackage :
  (SourceIntegralLowerBoundForMigratingMaximum ≡ false)
  × (RetainedViscosityLowerBoundAtMigratingMaximum ≡ false)
  × (SourceBeatsRetainedViscosityAtScaleDelta ≡ false)
  × (LocalizedSourceViscosityBalanceAtMigratingMaximum ≡ false)
  × (MigrationInitiationThresholdForLargeDataPromotedBySprint150 ≡ false)
  × (ScalingConsistencyForHouLuoConcentrationPromotedBySprint150 ≡ false)
  × (SymmetricHouLuoBKMFinite ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sourceViscosityFailClosedPackage =
  refl , refl , refl , refl , refl , refl , refl , refl , refl

sourceViscosityReceiptPackage :
  SourceViscosityBalanceSurface
  × NSSprint150SourceViscosityBalanceReceipt
  × SourceViscosityORCSLPGF
sourceViscosityReceiptPackage =
  canonicalSourceViscosityBalanceSurface ,
  canonicalNSSprint150SourceViscosityBalanceReceipt ,
  canonicalSourceViscosityORCSLPGF
