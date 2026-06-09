module DASHI.Physics.Closure.NSQuantitativeStationarityRateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary
  as Stationarity
import DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary
  as Transfer

------------------------------------------------------------------------
-- NS A3.3 quantitative stationarity-rate boundary.
--
-- This surface records the intended quantitative route only:
--
--   W_r = U_r - U_infty,
--   derive an energy ODE for W_r,
--   import Seregin/ESS compactness-rate authority,
--   use those inputs to target delta_r -> 0,
--   and only then feed the conditional transfer consequence
--
--     |Bias(mu_r)| <= delta_r * sqrt(11/60).
--
-- The rate theorem and delta_r convergence are not proved here.  The
-- sqrt(11/60) bias bound is recorded as a conditional downstream
-- consequence only, inherited from the transfer-operator bias-neutrality
-- receipt.  No Clay Navier-Stokes or terminal promotion is introduced.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Imported anchors.

abelStationarityBoundaryReference : String
abelStationarityBoundaryReference =
  "DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary"

transferBiasNeutralityBoundaryReference : String
transferBiasNeutralityBoundaryReference =
  "DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary"

sereginESSCompactnessRateAuthorityReference : String
sereginESSCompactnessRateAuthorityReference =
  "Seregin/ESS compactness-rate input for quantitative stationarity"

abelStationarityBoundaryImported : Bool
abelStationarityBoundaryImported =
  true

transferBiasNeutralityBoundaryImported : Bool
transferBiasNeutralityBoundaryImported =
  true

SereginRateImported : Bool
SereginRateImported =
  true

SereginRateAuthorityRecorded : Bool
SereginRateAuthorityRecorded =
  true

record ImportedQuantitativeStationaritySupport : Set where
  field
    abelStationarityBoundary :
      Stationarity.NSAbelTriadicStationarityConstructionBoundary
    abelStationarityBoundaryIsCanonical :
      abelStationarityBoundary
        ≡ Stationarity.canonicalNSAbelTriadicStationarityConstructionBoundary
    transferBiasNeutralityBoundary :
      Transfer.NSTransferOperatorBiasNeutralityBoundary
    transferBiasNeutralityBoundaryIsCanonical :
      transferBiasNeutralityBoundary
        ≡ Transfer.canonicalNSTransferOperatorBiasNeutralityBoundary
    abelStationarityBoundaryImportedIsTrue :
      abelStationarityBoundaryImported ≡ true
    transferBiasNeutralityBoundaryImportedIsTrue :
      transferBiasNeutralityBoundaryImported ≡ true
    sereginRateImportedIsTrue :
      SereginRateImported ≡ true
    sereginRateAuthorityRecordedIsTrue :
      SereginRateAuthorityRecorded ≡ true

canonicalImportedQuantitativeStationaritySupport :
  ImportedQuantitativeStationaritySupport
canonicalImportedQuantitativeStationaritySupport =
  record
    { abelStationarityBoundary =
        Stationarity.canonicalNSAbelTriadicStationarityConstructionBoundary
    ; abelStationarityBoundaryIsCanonical =
        refl
    ; transferBiasNeutralityBoundary =
        Transfer.canonicalNSTransferOperatorBiasNeutralityBoundary
    ; transferBiasNeutralityBoundaryIsCanonical =
        refl
    ; abelStationarityBoundaryImportedIsTrue =
        refl
    ; transferBiasNeutralityBoundaryImportedIsTrue =
        refl
    ; sereginRateImportedIsTrue =
        refl
    ; sereginRateAuthorityRecordedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- W_r = U_r - U_infty energy-ODE route.

data QuantitativeStationarityObject : Set where
  renormalizedProfileUr :
    QuantitativeStationarityObject
  limitingStationaryProfileUInfinity :
    QuantitativeStationarityObject
  profileDifferenceWrEqualsUrMinusUInfinity :
    QuantitativeStationarityObject
  stationarityDefectDeltaR :
    QuantitativeStationarityObject
  transferOutputMeasureMuR :
    QuantitativeStationarityObject
  biasFunctionalBiasMuR :
    QuantitativeStationarityObject

canonicalQuantitativeStationarityObjects :
  List QuantitativeStationarityObject
canonicalQuantitativeStationarityObjects =
  renormalizedProfileUr
  ∷ limitingStationaryProfileUInfinity
  ∷ profileDifferenceWrEqualsUrMinusUInfinity
  ∷ stationarityDefectDeltaR
  ∷ transferOutputMeasureMuR
  ∷ biasFunctionalBiasMuR
  ∷ []

quantitativeStationarityObjectCount : Nat
quantitativeStationarityObjectCount =
  listLength canonicalQuantitativeStationarityObjects

quantitativeStationarityObjectCountIs6 :
  quantitativeStationarityObjectCount ≡ 6
quantitativeStationarityObjectCountIs6 =
  refl

data EnergyODERouteClause : Set where
  defineWrAsUrMinusUInfinity :
    EnergyODERouteClause
  subtractStationaryLimitEquation :
    EnergyODERouteClause
  testDifferenceEquationAgainstWr :
    EnergyODERouteClause
  isolateCoerciveDissipationTerm :
    EnergyODERouteClause
  boundTransportPressureAndCommutatorErrors :
    EnergyODERouteClause
  convertDifferentialInequalityToQuantitativeDeltaRRate :
    EnergyODERouteClause

canonicalEnergyODERouteClauses :
  List EnergyODERouteClause
canonicalEnergyODERouteClauses =
  defineWrAsUrMinusUInfinity
  ∷ subtractStationaryLimitEquation
  ∷ testDifferenceEquationAgainstWr
  ∷ isolateCoerciveDissipationTerm
  ∷ boundTransportPressureAndCommutatorErrors
  ∷ convertDifferentialInequalityToQuantitativeDeltaRRate
  ∷ []

energyODERouteClauseCount : Nat
energyODERouteClauseCount =
  listLength canonicalEnergyODERouteClauses

energyODERouteClauseCountIs6 :
  energyODERouteClauseCount ≡ 6
energyODERouteClauseCountIs6 =
  refl

data SereginESSCompactnessRateInput : Set where
  localEnergyCompactnessRate :
    SereginESSCompactnessRateInput
  epsilonRegularityScaleControl :
    SereginESSCompactnessRateInput
  ancientSolutionRigidityRate :
    SereginESSCompactnessRateInput
  pressureDecompositionCompactnessRate :
    SereginESSCompactnessRateInput
  rateConstantsMustBeUniformInR :
    SereginESSCompactnessRateInput

canonicalSereginESSCompactnessRateInputs :
  List SereginESSCompactnessRateInput
canonicalSereginESSCompactnessRateInputs =
  localEnergyCompactnessRate
  ∷ epsilonRegularityScaleControl
  ∷ ancientSolutionRigidityRate
  ∷ pressureDecompositionCompactnessRate
  ∷ rateConstantsMustBeUniformInR
  ∷ []

sereginESSCompactnessRateInputCount : Nat
sereginESSCompactnessRateInputCount =
  listLength canonicalSereginESSCompactnessRateInputs

sereginESSCompactnessRateInputCountIs5 :
  sereginESSCompactnessRateInputCount ≡ 5
sereginESSCompactnessRateInputCountIs5 =
  refl

data QuantitativeStationarityRateConsequence : Set where
  deltaRRateWouldUpgradeApproximateStationarity :
    QuantitativeStationarityRateConsequence
  deltaRTendsToZeroWouldDischargeA3LimitBlocker :
    QuantitativeStationarityRateConsequence
  biasBoundWouldBeConditionalOnTransferNeutrality :
    QuantitativeStationarityRateConsequence
  displayedConditionalBiasBoundUsesSqrtElevenSixtieth :
    QuantitativeStationarityRateConsequence
  noUnconditionalResidualOrClayConsequence :
    QuantitativeStationarityRateConsequence

canonicalQuantitativeStationarityRateConsequences :
  List QuantitativeStationarityRateConsequence
canonicalQuantitativeStationarityRateConsequences =
  deltaRRateWouldUpgradeApproximateStationarity
  ∷ deltaRTendsToZeroWouldDischargeA3LimitBlocker
  ∷ biasBoundWouldBeConditionalOnTransferNeutrality
  ∷ displayedConditionalBiasBoundUsesSqrtElevenSixtieth
  ∷ noUnconditionalResidualOrClayConsequence
  ∷ []

quantitativeStationarityRateConsequenceCount : Nat
quantitativeStationarityRateConsequenceCount =
  listLength canonicalQuantitativeStationarityRateConsequences

quantitativeStationarityRateConsequenceCountIs5 :
  quantitativeStationarityRateConsequenceCount ≡ 5
quantitativeStationarityRateConsequenceCountIs5 =
  refl

conditionalBiasBoundText : String
conditionalBiasBoundText =
  "Conditional only: |Bias(mu_r)| <= delta_r * sqrt(11/60)"

energyODERouteText : String
energyODERouteText =
  "W_r = U_r - U_infty; derive a closed energy ODE for W_r and turn it into a quantitative stationarity-defect rate."

data QuantitativeStationarityRateBlocker : Set where
  missingClosedEnergyODEForWr :
    QuantitativeStationarityRateBlocker
  missingUniformSereginESSRateConstants :
    QuantitativeStationarityRateBlocker
  missingPressureAndCommutatorErrorRate :
    QuantitativeStationarityRateBlocker
  missingDeltaRToZeroProof :
    QuantitativeStationarityRateBlocker
  missingUnconditionalTransferBiasNeutrality :
    QuantitativeStationarityRateBlocker
  missingCriticalRegularityAndResidualClosure :
    QuantitativeStationarityRateBlocker

canonicalQuantitativeStationarityRateBlockers :
  List QuantitativeStationarityRateBlocker
canonicalQuantitativeStationarityRateBlockers =
  missingClosedEnergyODEForWr
  ∷ missingUniformSereginESSRateConstants
  ∷ missingPressureAndCommutatorErrorRate
  ∷ missingDeltaRToZeroProof
  ∷ missingUnconditionalTransferBiasNeutrality
  ∷ missingCriticalRegularityAndResidualClosure
  ∷ []

quantitativeStationarityRateBlockerCount : Nat
quantitativeStationarityRateBlockerCount =
  listLength canonicalQuantitativeStationarityRateBlockers

quantitativeStationarityRateBlockerCountIs6 :
  quantitativeStationarityRateBlockerCount ≡ 6
quantitativeStationarityRateBlockerCountIs6 =
  refl

------------------------------------------------------------------------
-- Fail-closed public flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

NSQuantitativeStationarityRateBoundaryRecorded : Bool
NSQuantitativeStationarityRateBoundaryRecorded =
  true

energyODERecorded : Bool
energyODERecorded =
  true

sereginRateImported : Bool
sereginRateImported =
  SereginRateImported

sereginRateAuthorityRecorded : Bool
sereginRateAuthorityRecorded =
  SereginRateAuthorityRecorded

quantitativeStationarityRateProved : Bool
quantitativeStationarityRateProved =
  false

deltaRTendsToZeroProved : Bool
deltaRTendsToZeroProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSQuantitativeStationarityRatePromotion : Set where

nsQuantitativeStationarityRatePromotionImpossibleHere :
  NSQuantitativeStationarityRatePromotion →
  ⊥
nsQuantitativeStationarityRatePromotionImpossibleHere ()

recordsBoundary :
  boundaryRecorded ≡ true
recordsBoundary =
  refl

recordsNamedBoundary :
  NSQuantitativeStationarityRateBoundaryRecorded ≡ true
recordsNamedBoundary =
  refl

recordsEnergyODE :
  energyODERecorded ≡ true
recordsEnergyODE =
  refl

recordsSereginRateImported :
  sereginRateImported ≡ true
recordsSereginRateImported =
  refl

recordsSereginAuthority :
  sereginRateAuthorityRecorded ≡ true
recordsSereginAuthority =
  refl

keepsQuantitativeRateUnproved :
  quantitativeStationarityRateProved ≡ false
keepsQuantitativeRateUnproved =
  refl

keepsDeltaRTendsToZeroFalse :
  deltaRTendsToZeroProved ≡ false
keepsDeltaRTendsToZeroFalse =
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
  "O: NS A3.3 records the quantitative stationarity-rate target from W_r = U_r - U_infty through an energy-ODE route and Seregin/ESS compactness-rate input."

requirementString : String
requirementString =
  "R: Keep the boundary fail-closed: record the route and authority inputs while leaving the quantitative rate, delta_r -> 0, Clay, and terminal promotion false."

codeArtifactString : String
codeArtifactString =
  "C: NSQuantitativeStationarityRateBoundary imports the Abel stationarity and transfer bias-neutrality boundaries, records W_r energy-ODE clauses, Seregin/ESS inputs, blockers, and the conditional sqrt(11/60) consequence."

stateString : String
stateString =
  "S: Boundary, energy ODE, and Seregin/ESS authority are recorded; quantitative stationarity rate and delta_r convergence remain open."

latticeString : String
latticeString =
  "L: Abel A3 stationarity receipt -> W_r energy ODE plus Seregin/ESS rate authority -> delta_r -> 0 blocker -> conditional transfer bias bound."

proposalString : String
proposalString =
  "P: Use this as the A3.3 receipt until a closed W_r energy inequality and uniform compactness-rate constants discharge delta_r -> 0."

governanceString : String
governanceString =
  "G: The sqrt(11/60) bias statement is conditional only; no downstream PDE, Clay, or terminal theorem may read this module as an unconditional proof."

gapString : String
gapString =
  "F: Open blockers are the closed W_r energy ODE, Seregin/ESS uniform rate extraction, pressure/commutator rate control, delta_r -> 0, and unconditional transfer to critical regularity."

------------------------------------------------------------------------
-- Canonical receipt.

record NSQuantitativeStationarityRateBoundary : Set where
  constructor nsQuantitativeStationarityRateBoundary
  field
    importedSupport :
      ImportedQuantitativeStationaritySupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedQuantitativeStationaritySupport
    objects :
      List QuantitativeStationarityObject
    objectsAreCanonical :
      objects ≡ canonicalQuantitativeStationarityObjects
    objectCountIsSix :
      quantitativeStationarityObjectCount ≡ 6
    energyODERoute :
      List EnergyODERouteClause
    energyODERouteIsCanonical :
      energyODERoute ≡ canonicalEnergyODERouteClauses
    energyODERouteCountIsSix :
      energyODERouteClauseCount ≡ 6
    sereginESSInputs :
      List SereginESSCompactnessRateInput
    sereginESSInputsAreCanonical :
      sereginESSInputs ≡ canonicalSereginESSCompactnessRateInputs
    sereginESSInputCountIsFive :
      sereginESSCompactnessRateInputCount ≡ 5
    consequences :
      List QuantitativeStationarityRateConsequence
    consequencesAreCanonical :
      consequences ≡ canonicalQuantitativeStationarityRateConsequences
    consequenceCountIsFive :
      quantitativeStationarityRateConsequenceCount ≡ 5
    blockers :
      List QuantitativeStationarityRateBlocker
    blockersAreCanonical :
      blockers ≡ canonicalQuantitativeStationarityRateBlockers
    blockerCountIsSix :
      quantitativeStationarityRateBlockerCount ≡ 6
    energyODERouteSummary :
      String
    energyODERouteSummaryIsCanonical :
      energyODERouteSummary ≡ energyODERouteText
    conditionalBiasBoundSummary :
      String
    conditionalBiasBoundSummaryIsCanonical :
      conditionalBiasBoundSummary ≡ conditionalBiasBoundText
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
    boundaryRecordedIsTrue :
      boundaryRecorded ≡ true
    namedBoundaryRecordedIsTrue :
      NSQuantitativeStationarityRateBoundaryRecorded ≡ true
    energyODERecordedIsTrue :
      energyODERecorded ≡ true
    sereginRateImportedIsTrue :
      sereginRateImported ≡ true
    sereginRateAuthorityRecordedIsTrue :
      sereginRateAuthorityRecorded ≡ true
    quantitativeRateProvedIsFalse :
      quantitativeStationarityRateProved ≡ false
    deltaRTendsToZeroProvedIsFalse :
      deltaRTendsToZeroProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

open NSQuantitativeStationarityRateBoundary public

canonicalNSQuantitativeStationarityRateBoundary :
  NSQuantitativeStationarityRateBoundary
canonicalNSQuantitativeStationarityRateBoundary =
  nsQuantitativeStationarityRateBoundary
    canonicalImportedQuantitativeStationaritySupport
    refl
    canonicalQuantitativeStationarityObjects
    refl
    refl
    canonicalEnergyODERouteClauses
    refl
    refl
    canonicalSereginESSCompactnessRateInputs
    refl
    refl
    canonicalQuantitativeStationarityRateConsequences
    refl
    refl
    canonicalQuantitativeStationarityRateBlockers
    refl
    refl
    energyODERouteText
    refl
    conditionalBiasBoundText
    refl
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
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
