module DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS triadic angular defect sheaf leakage boundary.
--
-- This module records the corrected NS obstruction surface:
--
--   the zero-mode object is not a subset of S^2 alone;
--   it is a cascade-aware sheaf over the resonant triadic interaction
--   manifold carrying true Leray bilinear-symbol data.
--
-- The checked content is deliberately a boundary ledger:
--
--   * resonant triadic site R with input directions a,b, output c, and
--     scale ratio rho;
--   * Abel-averaged triadic interaction defect measures;
--   * leakage functional Lambda over triadic patches;
--   * output leakage functional Lambda_out through pi_out;
--   * Lei-Ren-Tian output great-circle condition as an external
--     deterministic input;
--   * positive-width dependency for the cascade-closed zero-mode
--     output projection;
--   * target theorem: a global section satisfying LRT cannot be supported
--     entirely in the cascade-closed zero-mode subsheaf.
--
-- It does not prove the sheaf leakage theorem, the bilinear square-function
-- transfer, full local defect monotonicity, mechanism exhaustion, or Clay NS.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Resonant triadic site.

data UnitSphereDirection : Set where
  inputDirectionA :
    UnitSphereDirection
  inputDirectionB :
    UnitSphereDirection
  outputDirectionC :
    UnitSphereDirection
  greatCircleNormalDirection :
    UnitSphereDirection

data PositiveScaleRatio : Set where
  equalScaleRatio :
    PositiveScaleRatio
  unequalPositiveScaleRatio :
    PositiveScaleRatio

data ResonanceConstraint : Set where
  normalizedEqualScaleSum :
    UnitSphereDirection →
    UnitSphereDirection →
    UnitSphereDirection →
    ResonanceConstraint
  normalizedRhoWeightedSum :
    PositiveScaleRatio →
    UnitSphereDirection →
    UnitSphereDirection →
    UnitSphereDirection →
    ResonanceConstraint

data TriadicResonantSite : Set where
  resonantTriadicSiteR :
    UnitSphereDirection →
    UnitSphereDirection →
    UnitSphereDirection →
    PositiveScaleRatio →
    ResonanceConstraint →
    TriadicResonantSite

canonicalTriadicResonanceConstraint : ResonanceConstraint
canonicalTriadicResonanceConstraint =
  normalizedRhoWeightedSum
    unequalPositiveScaleRatio
    inputDirectionA
    inputDirectionB
    outputDirectionC

canonicalTriadicResonantSite : TriadicResonantSite
canonicalTriadicResonantSite =
  resonantTriadicSiteR
    inputDirectionA
    inputDirectionB
    outputDirectionC
    unequalPositiveScaleRatio
    canonicalTriadicResonanceConstraint

data TriadicSiteComponent : Set where
  inputSphereA :
    TriadicSiteComponent
  inputSphereB :
    TriadicSiteComponent
  outputSphereC :
    TriadicSiteComponent
  positiveScaleRatioRho :
    TriadicSiteComponent
  resonanceEquationCEqualsNormalizedRhoAPlusB :
    TriadicSiteComponent
  divergenceFreePolarizationFiber :
    TriadicSiteComponent

canonicalTriadicSiteComponents : List TriadicSiteComponent
canonicalTriadicSiteComponents =
  inputSphereA
  ∷ inputSphereB
  ∷ outputSphereC
  ∷ positiveScaleRatioRho
  ∷ resonanceEquationCEqualsNormalizedRhoAPlusB
  ∷ divergenceFreePolarizationFiber
  ∷ []

triadicSiteComponentCount : Nat
triadicSiteComponentCount =
  listLength canonicalTriadicSiteComponents

triadicSiteComponentCountIs6 :
  triadicSiteComponentCount ≡ 6
triadicSiteComponentCountIs6 =
  refl

------------------------------------------------------------------------
-- True Leray triadic symbol and zero-mode sheaf vocabulary.

data LerayBilinearSymbolCarrier : Set where
  trueLerayProjectedBilinearSymbol :
    TriadicResonantSite →
    LerayBilinearSymbolCarrier

data StretchingProjectionCarrier : Set where
  outputStretchingProjection :
    UnitSphereDirection →
    StretchingProjectionCarrier

data TriadicDefectLaplacianCarrier : Set where
  deltaNSTriadic :
    LerayBilinearSymbolCarrier →
    StretchingProjectionCarrier →
    TriadicDefectLaplacianCarrier

data TriadicLeakageEigenvalueCarrier : Set where
  lambdaNSTriadic :
    TriadicDefectLaplacianCarrier →
    TriadicLeakageEigenvalueCarrier

data CascadeClosedZeroModeSubsheaf : Set where
  cascadeClosedZeroModeSubsheaf :
    TriadicDefectLaplacianCarrier →
    CascadeClosedZeroModeSubsheaf

canonicalLerayBilinearSymbol : LerayBilinearSymbolCarrier
canonicalLerayBilinearSymbol =
  trueLerayProjectedBilinearSymbol canonicalTriadicResonantSite

canonicalStretchingProjection : StretchingProjectionCarrier
canonicalStretchingProjection =
  outputStretchingProjection outputDirectionC

canonicalTriadicDefectLaplacian : TriadicDefectLaplacianCarrier
canonicalTriadicDefectLaplacian =
  deltaNSTriadic
    canonicalLerayBilinearSymbol
    canonicalStretchingProjection

canonicalTriadicLeakageEigenvalue : TriadicLeakageEigenvalueCarrier
canonicalTriadicLeakageEigenvalue =
  lambdaNSTriadic canonicalTriadicDefectLaplacian

canonicalCascadeClosedZeroModeSubsheaf : CascadeClosedZeroModeSubsheaf
canonicalCascadeClosedZeroModeSubsheaf =
  cascadeClosedZeroModeSubsheaf canonicalTriadicDefectLaplacian

data ZeroModeSheafLayer : Set where
  localTriadicZeroModeLayer :
    ZeroModeSheafLayer
  cascadeClosureCompatibilityLayer :
    ZeroModeSheafLayer
  outputProjectionLayer :
    ZeroModeSheafLayer
  greatCircleAvoidanceWidthLayer :
    ZeroModeSheafLayer
  leakagePositivePatchLayer :
    ZeroModeSheafLayer

canonicalZeroModeSheafLayers : List ZeroModeSheafLayer
canonicalZeroModeSheafLayers =
  localTriadicZeroModeLayer
  ∷ cascadeClosureCompatibilityLayer
  ∷ outputProjectionLayer
  ∷ greatCircleAvoidanceWidthLayer
  ∷ leakagePositivePatchLayer
  ∷ []

zeroModeSheafLayerCount : Nat
zeroModeSheafLayerCount =
  listLength canonicalZeroModeSheafLayers

zeroModeSheafLayerCountIs5 :
  zeroModeSheafLayerCount ≡ 5
zeroModeSheafLayerCountIs5 =
  refl

------------------------------------------------------------------------
-- Abel-averaged triadic interaction defect measures and functionals.

data TriadicPatch : Set where
  resonantOpenPatch :
    TriadicResonantSite →
    TriadicPatch
  outputStripPreimagePatch :
    UnitSphereDirection →
    TriadicPatch
  leakagePositiveTriadicPatch :
    TriadicLeakageEigenvalueCarrier →
    TriadicPatch
  cascadeClosedZeroModePatch :
    CascadeClosedZeroModeSubsheaf →
    TriadicPatch

data AbelTriadicInteractionDefectMeasure : Set where
  abelAveragedTriadicInteractionDefectMeasure :
    TriadicPatch →
    AbelTriadicInteractionDefectMeasure

data TriadicDefectMeasureSection : Set where
  localTriadicMeasureSection :
    TriadicPatch →
    AbelTriadicInteractionDefectMeasure →
    TriadicDefectMeasureSection
  globalAbelTriadicInteractionSection :
    TriadicResonantSite →
    AbelTriadicInteractionDefectMeasure →
    TriadicDefectMeasureSection

data LeakageFunctional : Set where
  Lambda :
    TriadicPatch →
    AbelTriadicInteractionDefectMeasure →
    TriadicLeakageEigenvalueCarrier →
    LeakageFunctional

data OutputProjection : Set where
  piOut :
    TriadicResonantSite →
    UnitSphereDirection →
    OutputProjection

data OutputLeakageFunctional : Set where
  LambdaOut :
    UnitSphereDirection →
    OutputProjection →
    LeakageFunctional →
    OutputLeakageFunctional

canonicalResonantPatch : TriadicPatch
canonicalResonantPatch =
  resonantOpenPatch canonicalTriadicResonantSite

canonicalLeakagePositivePatch : TriadicPatch
canonicalLeakagePositivePatch =
  leakagePositiveTriadicPatch canonicalTriadicLeakageEigenvalue

canonicalCascadeClosedPatch : TriadicPatch
canonicalCascadeClosedPatch =
  cascadeClosedZeroModePatch canonicalCascadeClosedZeroModeSubsheaf

canonicalAbelTriadicMeasure : AbelTriadicInteractionDefectMeasure
canonicalAbelTriadicMeasure =
  abelAveragedTriadicInteractionDefectMeasure canonicalResonantPatch

canonicalGlobalTriadicSection : TriadicDefectMeasureSection
canonicalGlobalTriadicSection =
  globalAbelTriadicInteractionSection
    canonicalTriadicResonantSite
    canonicalAbelTriadicMeasure

canonicalLeakageFunctional : LeakageFunctional
canonicalLeakageFunctional =
  Lambda
    canonicalLeakagePositivePatch
    canonicalAbelTriadicMeasure
    canonicalTriadicLeakageEigenvalue

canonicalOutputProjection : OutputProjection
canonicalOutputProjection =
  piOut canonicalTriadicResonantSite outputDirectionC

canonicalOutputLeakageFunctional : OutputLeakageFunctional
canonicalOutputLeakageFunctional =
  LambdaOut
    outputDirectionC
    canonicalOutputProjection
    canonicalLeakageFunctional

data DefectSheafFunctionalRow : Set where
  abelAveragedMeasureSectionsOnTriadicPatches :
    DefectSheafFunctionalRow
  LambdaIntegratesTriadicLeakageEigenvalue :
    DefectSheafFunctionalRow
  piOutProjectsTriadsToOutputDirections :
    DefectSheafFunctionalRow
  LambdaOutRestrictsLambdaToOutputStripPreimage :
    DefectSheafFunctionalRow
  zeroModeSubsheafSupportBoundary :
    DefectSheafFunctionalRow
  leakagePositivePatchSupportBoundary :
    DefectSheafFunctionalRow

canonicalDefectSheafFunctionalRows : List DefectSheafFunctionalRow
canonicalDefectSheafFunctionalRows =
  abelAveragedMeasureSectionsOnTriadicPatches
  ∷ LambdaIntegratesTriadicLeakageEigenvalue
  ∷ piOutProjectsTriadsToOutputDirections
  ∷ LambdaOutRestrictsLambdaToOutputStripPreimage
  ∷ zeroModeSubsheafSupportBoundary
  ∷ leakagePositivePatchSupportBoundary
  ∷ []

defectSheafFunctionalRowCount : Nat
defectSheafFunctionalRowCount =
  listLength canonicalDefectSheafFunctionalRows

defectSheafFunctionalRowCountIs6 :
  defectSheafFunctionalRowCount ≡ 6
defectSheafFunctionalRowCountIs6 =
  refl

------------------------------------------------------------------------
-- External deterministic inputs and theorem target.

data LeiRenTianOutputGreatCircleCondition : Set where
  externalDeterministicLRTOutputGreatCircleCondition :
    TriadicDefectMeasureSection →
    OutputProjection →
    LeiRenTianOutputGreatCircleCondition

data CascadeClosedZeroModePositiveWidthDependency : Set where
  positiveGreatCircleAvoidanceWidthForPiOutOfZInfinity :
    CascadeClosedZeroModeSubsheaf →
    OutputProjection →
    CascadeClosedZeroModePositiveWidthDependency

data TriadicZeroModeSheafRigidityTarget : Set where
  globalLRTSectionNotSupportedEntirelyInCascadeClosedZeroModeSubsheaf :
    TriadicDefectMeasureSection →
    LeiRenTianOutputGreatCircleCondition →
    CascadeClosedZeroModePositiveWidthDependency →
    OutputLeakageFunctional →
    TriadicZeroModeSheafRigidityTarget

canonicalLRTOutputCondition :
  LeiRenTianOutputGreatCircleCondition
canonicalLRTOutputCondition =
  externalDeterministicLRTOutputGreatCircleCondition
    canonicalGlobalTriadicSection
    canonicalOutputProjection

canonicalPositiveWidthDependency :
  CascadeClosedZeroModePositiveWidthDependency
canonicalPositiveWidthDependency =
  positiveGreatCircleAvoidanceWidthForPiOutOfZInfinity
    canonicalCascadeClosedZeroModeSubsheaf
    canonicalOutputProjection

canonicalTriadicZeroModeSheafRigidityTarget :
  TriadicZeroModeSheafRigidityTarget
canonicalTriadicZeroModeSheafRigidityTarget =
  globalLRTSectionNotSupportedEntirelyInCascadeClosedZeroModeSubsheaf
    canonicalGlobalTriadicSection
    canonicalLRTOutputCondition
    canonicalPositiveWidthDependency
    canonicalOutputLeakageFunctional

data TheoremDependencyRow : Set where
  trueLerayTriadicSymbolDependency :
    TheoremDependencyRow
  cascadeClosedZeroModeSubsheafDependency :
    TheoremDependencyRow
  positiveOutputWidthDependency :
    TheoremDependencyRow
  externalLRTGreatCircleDependency :
    TheoremDependencyRow
  abelTriadicGlobalSectionDependency :
    TheoremDependencyRow
  leakagePositivePatchDependency :
    TheoremDependencyRow
  outputLeakageFunctionalDependency :
    TheoremDependencyRow

canonicalTheoremDependencyRows : List TheoremDependencyRow
canonicalTheoremDependencyRows =
  trueLerayTriadicSymbolDependency
  ∷ cascadeClosedZeroModeSubsheafDependency
  ∷ positiveOutputWidthDependency
  ∷ externalLRTGreatCircleDependency
  ∷ abelTriadicGlobalSectionDependency
  ∷ leakagePositivePatchDependency
  ∷ outputLeakageFunctionalDependency
  ∷ []

theoremDependencyRowCount : Nat
theoremDependencyRowCount =
  listLength canonicalTheoremDependencyRows

theoremDependencyRowCountIs7 :
  theoremDependencyRowCount ≡ 7
theoremDependencyRowCountIs7 =
  refl

data OpenAnalyticGapRow : Set where
  missingProofOfCascadeClosedZeroModePositiveWidth :
    OpenAnalyticGapRow
  missingProofOfTriadicZeroModeSheafRigidity :
    OpenAnalyticGapRow
  missingLowerBoundForLambdaOutOnForcedPatch :
    OpenAnalyticGapRow
  missingAbelMeasureConstructionFromBlowupSequence :
    OpenAnalyticGapRow
  missingTriadicLeakageSquareFunctionCoercivity :
    OpenAnalyticGapRow
  missingCriticalResidualTransfer :
    OpenAnalyticGapRow
  missingMechanismExhaustionForFullClayNS :
    OpenAnalyticGapRow

canonicalOpenAnalyticGapRows : List OpenAnalyticGapRow
canonicalOpenAnalyticGapRows =
  missingProofOfCascadeClosedZeroModePositiveWidth
  ∷ missingProofOfTriadicZeroModeSheafRigidity
  ∷ missingLowerBoundForLambdaOutOnForcedPatch
  ∷ missingAbelMeasureConstructionFromBlowupSequence
  ∷ missingTriadicLeakageSquareFunctionCoercivity
  ∷ missingCriticalResidualTransfer
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ []

openAnalyticGapRowCount : Nat
openAnalyticGapRowCount =
  listLength canonicalOpenAnalyticGapRows

openAnalyticGapRowCountIs7 :
  openAnalyticGapRowCount ≡ 7
openAnalyticGapRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Fail-closed gates.

sheafRecorded : Bool
sheafRecorded =
  true

resonantTriadicSiteRecorded : Bool
resonantTriadicSiteRecorded =
  true

abelTriadicMeasureRecorded : Bool
abelTriadicMeasureRecorded =
  true

leakageFunctionalRecorded : Bool
leakageFunctionalRecorded =
  true

outputLeakageFunctionalRecorded : Bool
outputLeakageFunctionalRecorded =
  true

lrtOutputConditionRecorded : Bool
lrtOutputConditionRecorded =
  true

positiveWidthDependencyRecorded : Bool
positiveWidthDependencyRecorded =
  true

triadicZeroModeSheafRigidityTargetRecorded : Bool
triadicZeroModeSheafRigidityTargetRecorded =
  true

positiveWidthProved : Bool
positiveWidthProved =
  false

leakageTheoremProved : Bool
leakageTheoremProved =
  false

abelMeasureConstructedFromBlowupSequence : Bool
abelMeasureConstructedFromBlowupSequence =
  false

triadicLeakageSquareFunctionCoercivityProved : Bool
triadicLeakageSquareFunctionCoercivityProved =
  false

criticalResidualTransferProved : Bool
criticalResidualTransferProved =
  false

fullLocalDefectMonotonicityProved : Bool
fullLocalDefectMonotonicityProved =
  false

mechanismExhaustionForFullClayNS : Bool
mechanismExhaustionForFullClayNS =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

sheafRecordedIsTrue :
  sheafRecorded ≡ true
sheafRecordedIsTrue =
  refl

resonantTriadicSiteRecordedIsTrue :
  resonantTriadicSiteRecorded ≡ true
resonantTriadicSiteRecordedIsTrue =
  refl

abelTriadicMeasureRecordedIsTrue :
  abelTriadicMeasureRecorded ≡ true
abelTriadicMeasureRecordedIsTrue =
  refl

leakageFunctionalRecordedIsTrue :
  leakageFunctionalRecorded ≡ true
leakageFunctionalRecordedIsTrue =
  refl

outputLeakageFunctionalRecordedIsTrue :
  outputLeakageFunctionalRecorded ≡ true
outputLeakageFunctionalRecordedIsTrue =
  refl

lrtOutputConditionRecordedIsTrue :
  lrtOutputConditionRecorded ≡ true
lrtOutputConditionRecordedIsTrue =
  refl

positiveWidthDependencyRecordedIsTrue :
  positiveWidthDependencyRecorded ≡ true
positiveWidthDependencyRecordedIsTrue =
  refl

triadicZeroModeSheafRigidityTargetRecordedIsTrue :
  triadicZeroModeSheafRigidityTargetRecorded ≡ true
triadicZeroModeSheafRigidityTargetRecordedIsTrue =
  refl

positiveWidthProvedIsFalse :
  positiveWidthProved ≡ false
positiveWidthProvedIsFalse =
  refl

leakageTheoremProvedIsFalse :
  leakageTheoremProved ≡ false
leakageTheoremProvedIsFalse =
  refl

abelMeasureConstructedFromBlowupSequenceIsFalse :
  abelMeasureConstructedFromBlowupSequence ≡ false
abelMeasureConstructedFromBlowupSequenceIsFalse =
  refl

triadicLeakageSquareFunctionCoercivityProvedIsFalse :
  triadicLeakageSquareFunctionCoercivityProved ≡ false
triadicLeakageSquareFunctionCoercivityProvedIsFalse =
  refl

criticalResidualTransferProvedIsFalse :
  criticalResidualTransferProved ≡ false
criticalResidualTransferProvedIsFalse =
  refl

fullLocalDefectMonotonicityProvedIsFalse :
  fullLocalDefectMonotonicityProved ≡ false
fullLocalDefectMonotonicityProvedIsFalse =
  refl

mechanismExhaustionForFullClayNSIsFalse :
  mechanismExhaustionForFullClayNS ≡ false
mechanismExhaustionForFullClayNSIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

fullClayNSSolvedIsFalse :
  fullClayNSSolved ≡ false
fullClayNSSolvedIsFalse =
  refl

------------------------------------------------------------------------
-- ORCSLPGF summary and canonical receipt.

organizationString : String
organizationString =
  "O: Lane C records the NS triadic angular defect sheaf leakage boundary over the resonant interaction site."

requirementString : String
requirementString =
  "R: Record R, Abel triadic measures, Lambda, Lambda_out, LRT output condition, positive-width dependency, and fail-closed leakage theorem target."

codeArtifactString : String
codeArtifactString =
  "C: New Agda module exports typed carriers, dependency rows, gap rows, exact counts, flags, and a canonical receipt."

stateString : String
stateString =
  "S: sheafRecorded=true; lrtOutputConditionRecorded=true; leakageTheoremProved=false; criticalResidualTransferProved=false; clayNavierStokesPromoted=false."

latticeString : String
latticeString =
  "L: true Leray triadic site -> Abel interaction measure sheaf -> output great-circle condition plus positive width -> leakage target -> analytic transfer gaps remain false."

proposalString : String
proposalString =
  "P: Promote this module only as a boundary ledger for TriadicZeroModeSheafRigidity and TriadicAngularDefectSheafLeakage."

governanceString : String
governanceString =
  "G: External LRT and positive-width dependencies are recorded as dependencies; no theorem, residual transfer, mechanism exhaustion, or Clay promotion is claimed."

gapString : String
gapString =
  "F: Missing proofs are positive width, sheaf leakage, Abel blowup measure construction, square-function coercivity, critical-residual transfer, and full NS mechanism exhaustion."

record NSTriadicAngularDefectSheafLeakageORCSLPGF : Set where
  constructor nsTriadicAngularDefectSheafLeakageORCSLPGF
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

open NSTriadicAngularDefectSheafLeakageORCSLPGF public

canonicalNSTriadicAngularDefectSheafLeakageORCSLPGF :
  NSTriadicAngularDefectSheafLeakageORCSLPGF
canonicalNSTriadicAngularDefectSheafLeakageORCSLPGF =
  nsTriadicAngularDefectSheafLeakageORCSLPGF
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

record NSTriadicAngularDefectSheafLeakageBoundaryReceipt : Set where
  constructor nsTriadicAngularDefectSheafLeakageBoundaryReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "NSTriadicAngularDefectSheafLeakageBoundary"
    orcslpgf :
      NSTriadicAngularDefectSheafLeakageORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadicAngularDefectSheafLeakageORCSLPGF
    triadicSite :
      TriadicResonantSite
    triadicSiteIsCanonical :
      triadicSite ≡ canonicalTriadicResonantSite
    triadicSiteComponents :
      List TriadicSiteComponent
    triadicSiteComponentsAreCanonical :
      triadicSiteComponents ≡ canonicalTriadicSiteComponents
    zeroModeSheafLayers :
      List ZeroModeSheafLayer
    zeroModeSheafLayersAreCanonical :
      zeroModeSheafLayers ≡ canonicalZeroModeSheafLayers
    defectSheafFunctionalRows :
      List DefectSheafFunctionalRow
    defectSheafFunctionalRowsAreCanonical :
      defectSheafFunctionalRows ≡ canonicalDefectSheafFunctionalRows
    theoremDependencyRows :
      List TheoremDependencyRow
    theoremDependencyRowsAreCanonical :
      theoremDependencyRows ≡ canonicalTheoremDependencyRows
    openAnalyticGapRows :
      List OpenAnalyticGapRow
    openAnalyticGapRowsAreCanonical :
      openAnalyticGapRows ≡ canonicalOpenAnalyticGapRows
    globalSection :
      TriadicDefectMeasureSection
    globalSectionIsCanonical :
      globalSection ≡ canonicalGlobalTriadicSection
    leakageFunctional :
      LeakageFunctional
    leakageFunctionalIsCanonical :
      leakageFunctional ≡ canonicalLeakageFunctional
    outputLeakageFunctional :
      OutputLeakageFunctional
    outputLeakageFunctionalIsCanonical :
      outputLeakageFunctional ≡ canonicalOutputLeakageFunctional
    lrtCondition :
      LeiRenTianOutputGreatCircleCondition
    lrtConditionIsCanonical :
      lrtCondition ≡ canonicalLRTOutputCondition
    positiveWidthDependency :
      CascadeClosedZeroModePositiveWidthDependency
    positiveWidthDependencyIsCanonical :
      positiveWidthDependency ≡ canonicalPositiveWidthDependency
    theoremTarget :
      TriadicZeroModeSheafRigidityTarget
    theoremTargetIsCanonical :
      theoremTarget ≡ canonicalTriadicZeroModeSheafRigidityTarget
    triadicSiteComponentCountField :
      triadicSiteComponentCount ≡ 6
    zeroModeSheafLayerCountField :
      zeroModeSheafLayerCount ≡ 5
    defectSheafFunctionalRowCountField :
      defectSheafFunctionalRowCount ≡ 6
    theoremDependencyRowCountField :
      theoremDependencyRowCount ≡ 7
    openAnalyticGapRowCountField :
      openAnalyticGapRowCount ≡ 7
    sheafRecordedTrueField :
      sheafRecorded ≡ true
    lrtOutputConditionRecordedTrueField :
      lrtOutputConditionRecorded ≡ true
    positiveWidthDependencyRecordedTrueField :
      positiveWidthDependencyRecorded ≡ true
    leakageTheoremProvedFalseField :
      leakageTheoremProved ≡ false
    criticalResidualTransferProvedFalseField :
      criticalResidualTransferProved ≡ false
    clayNavierStokesPromotedFalseField :
      clayNavierStokesPromoted ≡ false

open NSTriadicAngularDefectSheafLeakageBoundaryReceipt public

canonicalNSTriadicAngularDefectSheafLeakageBoundaryReceipt :
  NSTriadicAngularDefectSheafLeakageBoundaryReceipt
canonicalNSTriadicAngularDefectSheafLeakageBoundaryReceipt =
  nsTriadicAngularDefectSheafLeakageBoundaryReceipt
    "NSTriadicAngularDefectSheafLeakageBoundary"
    refl
    canonicalNSTriadicAngularDefectSheafLeakageORCSLPGF
    refl
    canonicalTriadicResonantSite
    refl
    canonicalTriadicSiteComponents
    refl
    canonicalZeroModeSheafLayers
    refl
    canonicalDefectSheafFunctionalRows
    refl
    canonicalTheoremDependencyRows
    refl
    canonicalOpenAnalyticGapRows
    refl
    canonicalGlobalTriadicSection
    refl
    canonicalLeakageFunctional
    refl
    canonicalOutputLeakageFunctional
    refl
    canonicalLRTOutputCondition
    refl
    canonicalPositiveWidthDependency
    refl
    canonicalTriadicZeroModeSheafRigidityTarget
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
