module DASHI.Physics.Closure.NSA4ResidualPositiveAfterErrorsBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4UniformErrorBudgetCompositeBoundary
  as Uniform
import DASHI.Physics.Closure.NSA4ExceptionalMassCompositeBoundary
  as Exceptional
import DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary
  as Bony
import DASHI.Physics.Closure.NSLowVorticityExceptionalMassRoutingBoundary
  as LowVorticity

------------------------------------------------------------------------
-- NS A4 residual-positivity-after-errors boundary.
--
-- This is the downstream obligation left by the A4 uniform error-budget
-- ledger.  It records the exact positivity theorem still needed after
-- subtracting:
--
--   * log-window / output-strip mismatch,
--   * antipodal and null normalize-sum degeneracy losses,
--   * low-vorticity and null-output exceptional routing losses,
--   * Bony/Lipschitz angular pushforward perturbation losses.
--
-- The intended target is:
--
--   for every eta, R, M there is r0(eta,R,M) such that
--   r < r0(eta,R,M) implies
--
--     c eta
--       - E_log
--       - E_antipodal
--       - E_low/null
--       - E_Bony/Lipschitz
--     > 0.
--
-- This module is a boundary receipt only.  It records the parameter window,
-- hierarchy, theorem target, and no-promotion guards.  It does not prove
-- the residual positivity inequality and does not promote A4, A6, local
-- defect monotonicity, or Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported boundary anchors.

uniformErrorBudgetCompositeBoundaryReference : String
uniformErrorBudgetCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA4UniformErrorBudgetCompositeBoundary"

exceptionalMassCompositeBoundaryReference : String
exceptionalMassCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA4ExceptionalMassCompositeBoundary"

bonyLipschitzAngularPushforwardBoundaryReference : String
bonyLipschitzAngularPushforwardBoundaryReference =
  "DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary"

lowVorticityExceptionalMassRoutingBoundaryReference : String
lowVorticityExceptionalMassRoutingBoundaryReference =
  "DASHI.Physics.Closure.NSLowVorticityExceptionalMassRoutingBoundary"

record ImportedResidualPositiveAfterErrorsSupport : Set where
  field
    uniformBudgetSupport :
      Uniform.ImportedUniformErrorBudgetCompositeSupport
    uniformBudgetSupportIsCanonical :
      uniformBudgetSupport
        ≡ Uniform.canonicalImportedUniformErrorBudgetCompositeSupport
    uniformBudgetTarget :
      Uniform.UniformA4ErrorBudgetCompositeTarget
    uniformBudgetTargetIsCanonical :
      uniformBudgetTarget
        ≡ Uniform.canonicalUniformA4ErrorBudgetCompositeTarget
    uniformSubtractionLedger :
      Uniform.UniformA4ErrorSubtractionLedger
    uniformSubtractionLedgerIsCanonical :
      uniformSubtractionLedger
        ≡ Uniform.canonicalUniformA4ErrorSubtractionLedger
    uniformInequalityShape :
      Uniform.UniformA4ErrorBudgetInequalityShape
    uniformInequalityShapeIsCanonical :
      uniformInequalityShape
        ≡ Uniform.canonicalUniformA4ErrorBudgetInequalityShape

    exceptionalSupport :
      Exceptional.ImportedExceptionalMassCompositeSupport
    exceptionalSupportIsCanonical :
      exceptionalSupport
        ≡ Exceptional.canonicalImportedExceptionalMassCompositeSupport
    exceptionalTarget :
      Exceptional.A4ExceptionalMassCompositeTarget
    exceptionalTargetIsCanonical :
      exceptionalTarget
        ≡ Exceptional.canonicalA4ExceptionalMassCompositeTarget

    bonySupport :
      Bony.ImportedBonyLipschitzAngularPushforwardSupport
    bonySupportIsCanonical :
      bonySupport
        ≡ Bony.canonicalImportedBonyLipschitzAngularPushforwardSupport
    bonyTarget :
      Bony.BonyLipschitzAngularPushforwardTarget
    bonyTargetIsCanonical :
      bonyTarget
        ≡ Bony.canonicalBonyLipschitzAngularPushforwardTarget

    lowVorticitySupport :
      LowVorticity.ImportedLowVorticityExceptionalMassSupport
    lowVorticitySupportIsCanonical :
      lowVorticitySupport
        ≡ LowVorticity.canonicalImportedLowVorticityExceptionalMassSupport
    lowVorticityTarget :
      LowVorticity.LowVorticityExceptionalMassRoutingTarget
    lowVorticityTargetIsCanonical :
      lowVorticityTarget
        ≡ LowVorticity.canonicalLowVorticityExceptionalMassRoutingTarget

    uniformBoundaryRecorded :
      Uniform.NSA4UniformErrorBudgetCompositeBoundaryRecorded ≡ true
    exceptionalBoundaryRecorded :
      Exceptional.NSA4ExceptionalMassCompositeBoundaryRecorded ≡ true
    bonyBoundaryRecorded :
      Bony.NSBonyLipschitzAngularPushforwardBoundaryRecorded ≡ true
    lowVorticityBoundaryRecorded :
      LowVorticity.NSLowVorticityExceptionalMassRoutingBoundaryRecorded
        ≡ true

    upstreamResidualPositivityStillFalse :
      Uniform.uniformResidualPositivityProved ≡ false
    upstreamUniformBudgetTheoremStillFalse :
      Uniform.uniformA4ErrorBudgetTheoremProved ≡ false
    exceptionalCompositeStillFalse :
      Exceptional.exceptionalMassRoutingCompositeProved ≡ false
    bonyPushforwardStillFalse :
      Bony.BonyLipschitzAngularPushforwardStabilityProved ≡ false
    lowVorticityRoutingStillFalse :
      LowVorticity.A4LowVorticityExceptionalMassRoutingProved ≡ false

canonicalImportedResidualPositiveAfterErrorsSupport :
  ImportedResidualPositiveAfterErrorsSupport
canonicalImportedResidualPositiveAfterErrorsSupport =
  record
    { uniformBudgetSupport =
        Uniform.canonicalImportedUniformErrorBudgetCompositeSupport
    ; uniformBudgetSupportIsCanonical =
        refl
    ; uniformBudgetTarget =
        Uniform.canonicalUniformA4ErrorBudgetCompositeTarget
    ; uniformBudgetTargetIsCanonical =
        refl
    ; uniformSubtractionLedger =
        Uniform.canonicalUniformA4ErrorSubtractionLedger
    ; uniformSubtractionLedgerIsCanonical =
        refl
    ; uniformInequalityShape =
        Uniform.canonicalUniformA4ErrorBudgetInequalityShape
    ; uniformInequalityShapeIsCanonical =
        refl
    ; exceptionalSupport =
        Exceptional.canonicalImportedExceptionalMassCompositeSupport
    ; exceptionalSupportIsCanonical =
        refl
    ; exceptionalTarget =
        Exceptional.canonicalA4ExceptionalMassCompositeTarget
    ; exceptionalTargetIsCanonical =
        refl
    ; bonySupport =
        Bony.canonicalImportedBonyLipschitzAngularPushforwardSupport
    ; bonySupportIsCanonical =
        refl
    ; bonyTarget =
        Bony.canonicalBonyLipschitzAngularPushforwardTarget
    ; bonyTargetIsCanonical =
        refl
    ; lowVorticitySupport =
        LowVorticity.canonicalImportedLowVorticityExceptionalMassSupport
    ; lowVorticitySupportIsCanonical =
        refl
    ; lowVorticityTarget =
        LowVorticity.canonicalLowVorticityExceptionalMassRoutingTarget
    ; lowVorticityTargetIsCanonical =
        refl
    ; uniformBoundaryRecorded =
        refl
    ; exceptionalBoundaryRecorded =
        refl
    ; bonyBoundaryRecorded =
        refl
    ; lowVorticityBoundaryRecorded =
        refl
    ; upstreamResidualPositivityStillFalse =
        refl
    ; upstreamUniformBudgetTheoremStillFalse =
        refl
    ; exceptionalCompositeStillFalse =
        refl
    ; bonyPushforwardStillFalse =
        refl
    ; lowVorticityRoutingStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Parameter window and r < r0(eta,R,M) carrier.

data A4EtaParameter : Set where
  etaWindowParameter :
    Nat →
    A4EtaParameter

data A4RadiusScale : Set where
  RWindowScale :
    Nat →
    A4RadiusScale

data A4MassScale : Set where
  MWindowScale :
    Nat →
    A4MassScale

data A4SmallRadius : Set where
  rWindowRadius :
    Nat →
    A4SmallRadius

data A4ThresholdRadius : Set where
  r0OfEtaRAndM :
    A4EtaParameter →
    A4RadiusScale →
    A4MassScale →
    Nat →
    A4ThresholdRadius

data A4SmallRadiusBelowThreshold : Set where
  rLessThanR0OfEtaRAndM :
    A4SmallRadius →
    A4ThresholdRadius →
    A4SmallRadiusBelowThreshold

data A4ResidualParameterWindow : Set where
  etaRMRSmallnessWindow :
    A4EtaParameter →
    A4RadiusScale →
    A4MassScale →
    A4SmallRadius →
    A4ThresholdRadius →
    A4SmallRadiusBelowThreshold →
    A4ResidualParameterWindow

canonicalEtaParameter : A4EtaParameter
canonicalEtaParameter =
  etaWindowParameter (suc zero)

canonicalRadiusScale : A4RadiusScale
canonicalRadiusScale =
  RWindowScale (suc (suc zero))

canonicalMassScale : A4MassScale
canonicalMassScale =
  MWindowScale (suc (suc (suc zero)))

canonicalSmallRadius : A4SmallRadius
canonicalSmallRadius =
  rWindowRadius zero

canonicalThresholdRadius : A4ThresholdRadius
canonicalThresholdRadius =
  r0OfEtaRAndM
    canonicalEtaParameter
    canonicalRadiusScale
    canonicalMassScale
    (suc zero)

canonicalSmallRadiusBelowThreshold : A4SmallRadiusBelowThreshold
canonicalSmallRadiusBelowThreshold =
  rLessThanR0OfEtaRAndM
    canonicalSmallRadius
    canonicalThresholdRadius

canonicalA4ResidualParameterWindow : A4ResidualParameterWindow
canonicalA4ResidualParameterWindow =
  etaRMRSmallnessWindow
    canonicalEtaParameter
    canonicalRadiusScale
    canonicalMassScale
    canonicalSmallRadius
    canonicalThresholdRadius
    canonicalSmallRadiusBelowThreshold

------------------------------------------------------------------------
-- Error hierarchy and positivity target.

data A4ResidualPositiveErrorClass : Set where
  cEtaStripLowerBoundClass :
    A4ResidualPositiveErrorClass
  logWindowOutputStripErrorClass :
    A4ResidualPositiveErrorClass
  antipodalNullNormalizeSumErrorClass :
    A4ResidualPositiveErrorClass
  lowVorticityNullOutputDiscardErrorClass :
    A4ResidualPositiveErrorClass
  bonyLipschitzAngularPerturbationErrorClass :
    A4ResidualPositiveErrorClass
  residualPositiveRemainderClass :
    A4ResidualPositiveErrorClass

canonicalA4ResidualPositiveErrorHierarchy :
  List A4ResidualPositiveErrorClass
canonicalA4ResidualPositiveErrorHierarchy =
  cEtaStripLowerBoundClass
  ∷ logWindowOutputStripErrorClass
  ∷ antipodalNullNormalizeSumErrorClass
  ∷ lowVorticityNullOutputDiscardErrorClass
  ∷ bonyLipschitzAngularPerturbationErrorClass
  ∷ residualPositiveRemainderClass
  ∷ []

a4ResidualPositiveErrorHierarchyCount : Nat
a4ResidualPositiveErrorHierarchyCount =
  listLength canonicalA4ResidualPositiveErrorHierarchy

a4ResidualPositiveErrorHierarchyCountIs6 :
  a4ResidualPositiveErrorHierarchyCount ≡ 6
a4ResidualPositiveErrorHierarchyCountIs6 =
  refl

data A4ErrorHierarchyWitness : Set where
  hierarchyOrderedBelowCEtaStripLowerBound :
    Uniform.UniformA4PositiveMassScaleCarrier →
    Uniform.LogWindowOutputStripErrorCarrier →
    Uniform.AntipodalErrorCarrier →
    Uniform.LowVorticityErrorCarrier →
    Uniform.BonyPerturbationErrorCarrier →
    Uniform.UniformA4ErrorSubtractionLedger →
    A4ErrorHierarchyWitness

data A4ResidualPositiveAfterErrorsFormula : Set where
  cEtaMinusAllRecordedA4ErrorsRemainsPositive :
    A4ResidualParameterWindow →
    A4ErrorHierarchyWitness →
    Uniform.UniformA4ErrorBudgetInequalityShape →
    A4ResidualPositiveAfterErrorsFormula

data A4ResidualPositiveWitnessTarget : Set where
  proveResidualPositiveForEverySmallRBelowR0 :
    ImportedResidualPositiveAfterErrorsSupport →
    A4ResidualPositiveAfterErrorsFormula →
    Exceptional.A4ExceptionalMassCompositeTarget →
    Bony.BonyLipschitzAngularPushforwardTarget →
    LowVorticity.LowVorticityExceptionalMassRoutingTarget →
    A4ResidualPositiveWitnessTarget

canonicalA4ErrorHierarchyWitness : A4ErrorHierarchyWitness
canonicalA4ErrorHierarchyWitness =
  hierarchyOrderedBelowCEtaStripLowerBound
    Uniform.canonicalUniformA4PositiveMassScaleCarrier
    Uniform.canonicalLogWindowOutputStripErrorCarrier
    Uniform.canonicalAntipodalErrorCarrier
    Uniform.canonicalLowVorticityErrorCarrier
    Uniform.canonicalBonyPerturbationErrorCarrier
    Uniform.canonicalUniformA4ErrorSubtractionLedger

canonicalA4ResidualPositiveAfterErrorsFormula :
  A4ResidualPositiveAfterErrorsFormula
canonicalA4ResidualPositiveAfterErrorsFormula =
  cEtaMinusAllRecordedA4ErrorsRemainsPositive
    canonicalA4ResidualParameterWindow
    canonicalA4ErrorHierarchyWitness
    Uniform.canonicalUniformA4ErrorBudgetInequalityShape

canonicalA4ResidualPositiveWitnessTarget :
  A4ResidualPositiveWitnessTarget
canonicalA4ResidualPositiveWitnessTarget =
  proveResidualPositiveForEverySmallRBelowR0
    canonicalImportedResidualPositiveAfterErrorsSupport
    canonicalA4ResidualPositiveAfterErrorsFormula
    Exceptional.canonicalA4ExceptionalMassCompositeTarget
    Bony.canonicalBonyLipschitzAngularPushforwardTarget
    LowVorticity.canonicalLowVorticityExceptionalMassRoutingTarget

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data A4ResidualPositiveAfterErrorsObligation : Set where
  importUniformExceptionalBonyAndLowVorticityBoundaries :
    A4ResidualPositiveAfterErrorsObligation
  quantifyEtaRMRSmallnessWindow :
    A4ResidualPositiveAfterErrorsObligation
  defineR0OfEtaRAndM :
    A4ResidualPositiveAfterErrorsObligation
  assumeRLessThanR0EtaRM :
    A4ResidualPositiveAfterErrorsObligation
  orderLogWindowAntipodalLowNullAndBonyErrors :
    A4ResidualPositiveAfterErrorsObligation
  dominateTotalErrorByStrictFractionOfCEta :
    A4ResidualPositiveAfterErrorsObligation
  proveResidualPositiveAfterAllSubtractions :
    A4ResidualPositiveAfterErrorsObligation
  feedPositiveResidualOnlyToFailClosedA4Budget :
    A4ResidualPositiveAfterErrorsObligation
  keepA4A6LocalDefectClayAndTerminalPromotionsClosed :
    A4ResidualPositiveAfterErrorsObligation

canonicalA4ResidualPositiveAfterErrorsObligations :
  List A4ResidualPositiveAfterErrorsObligation
canonicalA4ResidualPositiveAfterErrorsObligations =
  importUniformExceptionalBonyAndLowVorticityBoundaries
  ∷ quantifyEtaRMRSmallnessWindow
  ∷ defineR0OfEtaRAndM
  ∷ assumeRLessThanR0EtaRM
  ∷ orderLogWindowAntipodalLowNullAndBonyErrors
  ∷ dominateTotalErrorByStrictFractionOfCEta
  ∷ proveResidualPositiveAfterAllSubtractions
  ∷ feedPositiveResidualOnlyToFailClosedA4Budget
  ∷ keepA4A6LocalDefectClayAndTerminalPromotionsClosed
  ∷ []

a4ResidualPositiveAfterErrorsObligationCount : Nat
a4ResidualPositiveAfterErrorsObligationCount =
  listLength canonicalA4ResidualPositiveAfterErrorsObligations

a4ResidualPositiveAfterErrorsObligationCountIs9 :
  a4ResidualPositiveAfterErrorsObligationCount ≡ 9
a4ResidualPositiveAfterErrorsObligationCountIs9 =
  refl

data A4ResidualPositiveAfterErrorsBlocker : Set where
  missingQuantitativeR0EtaRMConstruction :
    A4ResidualPositiveAfterErrorsBlocker
  missingUniformCEtaStripLowerBoundProof :
    A4ResidualPositiveAfterErrorsBlocker
  missingLogWindowOutputStripSmallnessRate :
    A4ResidualPositiveAfterErrorsBlocker
  missingAntipodalNullNormalizeSumSmallnessRate :
    A4ResidualPositiveAfterErrorsBlocker
  missingLowVorticityNullOutputDiscardSmallnessRate :
    A4ResidualPositiveAfterErrorsBlocker
  missingBonyLipschitzPerturbationSmallnessRate :
    A4ResidualPositiveAfterErrorsBlocker
  missingTotalErrorDominatedByCEtaMargin :
    A4ResidualPositiveAfterErrorsBlocker
  missingResidualPositiveWitness :
    A4ResidualPositiveAfterErrorsBlocker
  promotionsRemainClosed :
    A4ResidualPositiveAfterErrorsBlocker

canonicalA4ResidualPositiveAfterErrorsBlockers :
  List A4ResidualPositiveAfterErrorsBlocker
canonicalA4ResidualPositiveAfterErrorsBlockers =
  missingQuantitativeR0EtaRMConstruction
  ∷ missingUniformCEtaStripLowerBoundProof
  ∷ missingLogWindowOutputStripSmallnessRate
  ∷ missingAntipodalNullNormalizeSumSmallnessRate
  ∷ missingLowVorticityNullOutputDiscardSmallnessRate
  ∷ missingBonyLipschitzPerturbationSmallnessRate
  ∷ missingTotalErrorDominatedByCEtaMargin
  ∷ missingResidualPositiveWitness
  ∷ promotionsRemainClosed
  ∷ []

a4ResidualPositiveAfterErrorsBlockerCount : Nat
a4ResidualPositiveAfterErrorsBlockerCount =
  listLength canonicalA4ResidualPositiveAfterErrorsBlockers

a4ResidualPositiveAfterErrorsBlockerCountIs9 :
  a4ResidualPositiveAfterErrorsBlockerCount ≡ 9
a4ResidualPositiveAfterErrorsBlockerCountIs9 =
  refl

data A4ResidualPositiveAfterErrorsStatusRow : Set where
  residualBoundaryRecordedStatus :
    A4ResidualPositiveAfterErrorsStatusRow
  fourInputBoundariesConsumedStatus :
    A4ResidualPositiveAfterErrorsStatusRow
  etaRMRWindowRecordedStatus :
    A4ResidualPositiveAfterErrorsStatusRow
  rLessThanR0GuardRecordedStatus :
    A4ResidualPositiveAfterErrorsStatusRow
  errorHierarchyRecordedStatus :
    A4ResidualPositiveAfterErrorsStatusRow
  positivityWitnessTargetRecordedStatus :
    A4ResidualPositiveAfterErrorsStatusRow
  residualProofStillOpenStatus :
    A4ResidualPositiveAfterErrorsStatusRow
  noPromotionGuardsRecordedStatus :
    A4ResidualPositiveAfterErrorsStatusRow

canonicalA4ResidualPositiveAfterErrorsStatusRows :
  List A4ResidualPositiveAfterErrorsStatusRow
canonicalA4ResidualPositiveAfterErrorsStatusRows =
  residualBoundaryRecordedStatus
  ∷ fourInputBoundariesConsumedStatus
  ∷ etaRMRWindowRecordedStatus
  ∷ rLessThanR0GuardRecordedStatus
  ∷ errorHierarchyRecordedStatus
  ∷ positivityWitnessTargetRecordedStatus
  ∷ residualProofStillOpenStatus
  ∷ noPromotionGuardsRecordedStatus
  ∷ []

a4ResidualPositiveAfterErrorsStatusRowCount : Nat
a4ResidualPositiveAfterErrorsStatusRowCount =
  listLength canonicalA4ResidualPositiveAfterErrorsStatusRows

a4ResidualPositiveAfterErrorsStatusRowCountIs8 :
  a4ResidualPositiveAfterErrorsStatusRowCount ≡ 8
a4ResidualPositiveAfterErrorsStatusRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data A4ResidualPositiveAfterErrorsPromotion : Set where

a4ResidualPositiveAfterErrorsPromotionImpossibleHere :
  A4ResidualPositiveAfterErrorsPromotion →
  ⊥
a4ResidualPositiveAfterErrorsPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSA4ResidualPositiveAfterErrorsBoundaryRecorded : Bool
NSA4ResidualPositiveAfterErrorsBoundaryRecorded =
  true

etaRMRParameterWindowRecorded : Bool
etaRMRParameterWindowRecorded =
  true

rLessThanR0EtaRMGuardRecorded : Bool
rLessThanR0EtaRMGuardRecorded =
  true

errorHierarchyRecorded : Bool
errorHierarchyRecorded =
  true

positivityWitnessTargetRecorded : Bool
positivityWitnessTargetRecorded =
  true

residualPositiveAfterErrorsProved : Bool
residualPositiveAfterErrorsProved =
  false

quantitativeR0EtaRMConstructed : Bool
quantitativeR0EtaRMConstructed =
  false

totalErrorDominatedByCEtaMarginProved : Bool
totalErrorDominatedByCEtaMarginProved =
  false

A4TheoremPromoted : Bool
A4TheoremPromoted =
  false

A6TheoremPromoted : Bool
A6TheoremPromoted =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
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

recordsBoundary :
  NSA4ResidualPositiveAfterErrorsBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsEtaRMRParameterWindow :
  etaRMRParameterWindowRecorded ≡ true
recordsEtaRMRParameterWindow =
  refl

recordsRLessThanR0EtaRMGuard :
  rLessThanR0EtaRMGuardRecorded ≡ true
recordsRLessThanR0EtaRMGuard =
  refl

recordsErrorHierarchy :
  errorHierarchyRecorded ≡ true
recordsErrorHierarchy =
  refl

recordsPositivityWitnessTarget :
  positivityWitnessTargetRecorded ≡ true
recordsPositivityWitnessTarget =
  refl

keepsResidualPositiveAfterErrorsFalse :
  residualPositiveAfterErrorsProved ≡ false
keepsResidualPositiveAfterErrorsFalse =
  refl

keepsQuantitativeR0EtaRMFalse :
  quantitativeR0EtaRMConstructed ≡ false
keepsQuantitativeR0EtaRMFalse =
  refl

keepsTotalErrorDominatedFalse :
  totalErrorDominatedByCEtaMarginProved ≡ false
keepsTotalErrorDominatedFalse =
  refl

keepsA4TheoremPromotionFalse :
  A4TheoremPromoted ≡ false
keepsA4TheoremPromotionFalse =
  refl

keepsA6TheoremPromotionFalse :
  A6TheoremPromoted ≡ false
keepsA6TheoremPromotionFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: NSA4ResidualPositiveAfterErrorsBoundary is worker-3's disjoint A4 boundary for the residual positivity obligation after the recorded error subtractions."

requirementString : String
requirementString =
  "R: Consume the uniform error budget, exceptional mass composite, Bony/Lipschitz angular pushforward, and low-vorticity routing boundaries; record r < r0(eta,R,M), the error hierarchy, and the target c eta minus all errors > 0."

codeArtifactString : String
codeArtifactString =
  "C: The module exports imported support, eta/R/M/r/r0 carriers, an r<r0 guard, an ordered error hierarchy, a positivity witness target, blockers, statuses, and false-promotion guards."

stateString : String
stateString =
  "S: The boundary, parameter window, r<r0 guard, error hierarchy, and target are recorded true; quantitative r0, total-error domination, residual positivity, A4, A6, Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: eta,R,M choose r0 > require r<r0 > consume c eta strip lower bound > subtract log-window/output-strip > subtract antipodal/null normalize-sum > subtract low-vorticity/null-output > subtract Bony/Lipschitz > target positive residual."

proposalString : String
proposalString =
  "P: Promote this boundary only after constructing r0(eta,R,M) and proving the sum of all recorded error classes is strictly below the c eta strip margin."

governanceString : String
governanceString =
  "G: This receipt is no-promotion: it records the residual positivity obligation and preserves every upstream false theorem/promotion flag."

gapString : String
gapString =
  "F: Missing quantitative r0(eta,R,M), uniform c eta lower-bound proof, log-window/output-strip rate, antipodal/null rate, low-vorticity/null-output rate, Bony/Lipschitz rate, total-error domination, and residual positive witness."

------------------------------------------------------------------------
-- Canonical receipt.

record NSA4ResidualPositiveAfterErrorsBoundary : Set where
  field
    O-organization :
      String
    R-requirement :
      String
    C-artifact :
      String
    S-state :
      String
    L-lattice :
      String
    P-proposal :
      String
    G-governance :
      String
    F-gap :
      String
    importedSupport :
      ImportedResidualPositiveAfterErrorsSupport
    parameterWindow :
      A4ResidualParameterWindow
    errorHierarchy :
      List A4ResidualPositiveErrorClass
    errorHierarchyCountIs6 :
      a4ResidualPositiveErrorHierarchyCount ≡ 6
    hierarchyWitness :
      A4ErrorHierarchyWitness
    positivityFormula :
      A4ResidualPositiveAfterErrorsFormula
    positivityWitnessTarget :
      A4ResidualPositiveWitnessTarget
    obligations :
      List A4ResidualPositiveAfterErrorsObligation
    obligationCountIs9 :
      a4ResidualPositiveAfterErrorsObligationCount ≡ 9
    blockers :
      List A4ResidualPositiveAfterErrorsBlocker
    blockerCountIs9 :
      a4ResidualPositiveAfterErrorsBlockerCount ≡ 9
    statusRows :
      List A4ResidualPositiveAfterErrorsStatusRow
    statusRowCountIs8 :
      a4ResidualPositiveAfterErrorsStatusRowCount ≡ 8
    boundaryRecordedTrue :
      NSA4ResidualPositiveAfterErrorsBoundaryRecorded ≡ true
    etaRMRWindowRecordedTrue :
      etaRMRParameterWindowRecorded ≡ true
    rLessThanR0GuardRecordedTrue :
      rLessThanR0EtaRMGuardRecorded ≡ true
    errorHierarchyRecordedTrue :
      errorHierarchyRecorded ≡ true
    positivityWitnessTargetRecordedTrue :
      positivityWitnessTargetRecorded ≡ true
    residualPositiveStillFalse :
      residualPositiveAfterErrorsProved ≡ false
    quantitativeR0StillFalse :
      quantitativeR0EtaRMConstructed ≡ false
    totalErrorDominationStillFalse :
      totalErrorDominatedByCEtaMarginProved ≡ false
    upstreamResidualPositivityStillFalse :
      Uniform.uniformResidualPositivityProved ≡ false
    upstreamUniformBudgetTheoremStillFalse :
      Uniform.uniformA4ErrorBudgetTheoremProved ≡ false
    a4PromotionStillFalse :
      A4TheoremPromoted ≡ false
    a6PromotionStillFalse :
      A6TheoremPromoted ≡ false
    localDefectStillFalse :
      fullLocalDefectMonotonicity ≡ false
    claySolvedStillFalse :
      fullClayNSSolved ≡ false
    clayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSA4ResidualPositiveAfterErrorsBoundary :
  NSA4ResidualPositiveAfterErrorsBoundary
canonicalNSA4ResidualPositiveAfterErrorsBoundary =
  record
    { O-organization =
        organizationString
    ; R-requirement =
        requirementString
    ; C-artifact =
        codeArtifactString
    ; S-state =
        stateString
    ; L-lattice =
        latticeString
    ; P-proposal =
        proposalString
    ; G-governance =
        governanceString
    ; F-gap =
        gapString
    ; importedSupport =
        canonicalImportedResidualPositiveAfterErrorsSupport
    ; parameterWindow =
        canonicalA4ResidualParameterWindow
    ; errorHierarchy =
        canonicalA4ResidualPositiveErrorHierarchy
    ; errorHierarchyCountIs6 =
        refl
    ; hierarchyWitness =
        canonicalA4ErrorHierarchyWitness
    ; positivityFormula =
        canonicalA4ResidualPositiveAfterErrorsFormula
    ; positivityWitnessTarget =
        canonicalA4ResidualPositiveWitnessTarget
    ; obligations =
        canonicalA4ResidualPositiveAfterErrorsObligations
    ; obligationCountIs9 =
        refl
    ; blockers =
        canonicalA4ResidualPositiveAfterErrorsBlockers
    ; blockerCountIs9 =
        refl
    ; statusRows =
        canonicalA4ResidualPositiveAfterErrorsStatusRows
    ; statusRowCountIs8 =
        refl
    ; boundaryRecordedTrue =
        refl
    ; etaRMRWindowRecordedTrue =
        refl
    ; rLessThanR0GuardRecordedTrue =
        refl
    ; errorHierarchyRecordedTrue =
        refl
    ; positivityWitnessTargetRecordedTrue =
        refl
    ; residualPositiveStillFalse =
        refl
    ; quantitativeR0StillFalse =
        refl
    ; totalErrorDominationStillFalse =
        refl
    ; upstreamResidualPositivityStillFalse =
        refl
    ; upstreamUniformBudgetTheoremStillFalse =
        refl
    ; a4PromotionStillFalse =
        refl
    ; a6PromotionStillFalse =
        refl
    ; localDefectStillFalse =
        refl
    ; claySolvedStillFalse =
        refl
    ; clayPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }
