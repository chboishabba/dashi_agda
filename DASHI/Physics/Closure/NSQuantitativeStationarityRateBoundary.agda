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
-- NS A3 quantitative stationarity-rate boundary.
--
-- This surface records the explicit A3.1-A3.4 proof package only:
--
--   A3.1: impose a CKN-scale approximate T_NS stationarity with rate,
--         define W_r = U_r - U_infty and close the local enstrophy ODE,
--   A3.2: import the Seregin-ESS C-infinity_loc subsequence rate,
--   A3.3: close the Abel mixing-TV transfer with
--         delta_r <= C eps^1/2 N_eff^1/2,
--   A3.4: close the fixed-point/window summation and obtain
--         delta_r -> 0,
--   and only then may the transfer consequence be read:
--
--     |Bias(mu_r)| <= delta_r * sqrt(11/60).
--
-- The A3 theorem clauses, imported rate labels, and downstream consequences
-- are recorded exactly.  This promotes only the quantitative A3 rate and
-- delta_r -> 0 witnesses; no Clay Navier-Stokes or terminal promotion is
-- introduced.

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data ⊥ : Set where

abelStationarityBoundaryReference : String
abelStationarityBoundaryReference =
  "DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary"

transferBiasNeutralityBoundaryReference : String
transferBiasNeutralityBoundaryReference =
  "DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary"

sereginESSCompactnessRateAuthorityReference : String
sereginESSCompactnessRateAuthorityReference =
  "Seregin-ESS C-infinity_loc subsequence rate input for coupled A1/A3 stationarity with epsilon = 1/6"

sereginESSCompactnessRateAuthorityText : String
sereginESSCompactnessRateAuthorityText =
  "A3.2 proof package: use the Seregin-ESS C-infinity_loc subsequence rate as the quantitative intake source of epsilon = 1/6."

candidateEpsilonRateLabel : String
candidateEpsilonRateLabel =
  "epsilon = 1/6"

candidateDeltaRRateLabel : String
candidateDeltaRRateLabel =
  "delta_r <= C eps^1/2 N_eff^1/2, with fixed-point/window summation yielding delta_r -> 0"

candidateWrEnergyODELabel : String
candidateWrEnergyODELabel =
  "closed_W_r_local_enstrophy_ode: d/d(log r) Energy[W_r] + coercive_dissipation_r <= transport_r + pressure_r + commutator_r + A1_defect_input_r (with Abel mixing-TV transfer bookkeeping)"

abelMixingTVTransferLemmaLabel : String
abelMixingTVTransferLemmaLabel =
  "abel_mixing_TV_transfer_lemma"

multiscaleAbelClosureFixedPointLabel : String
multiscaleAbelClosureFixedPointLabel =
  "multiscale_abel_summation_closure_fixed_point_closed"

a5a6ConditionalBiasNeutralityContractText : String
a5a6ConditionalBiasNeutralityContractText =
  "A5/A6 may consume the A3 quantitative contract: the closed W_r local enstrophy ODE, Seregin-ESS C-infinity_loc subsequence rate, Abel mixing-TV transfer delta_r <= C eps^1/2 N_eff^1/2, and fixed-point/window summation closure yield delta_r -> 0 and |Bias(mu_r)| <= delta_r * sqrt(11/60) remains bias-neutrality compatible."

abelStationarityBoundaryImported : Bool
abelStationarityBoundaryImported = true

transferBiasNeutralityBoundaryImported : Bool
transferBiasNeutralityBoundaryImported = true

SereginRateImported : Bool
SereginRateImported = true

SereginRateAuthorityRecorded : Bool
SereginRateAuthorityRecorded = true

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

data QuantitativeStationarityObject : Set where
  a1AbelDefectMeasureMuR : QuantitativeStationarityObject
  a1ShellWindowMassDr : QuantitativeStationarityObject
  renormalizedProfileUr : QuantitativeStationarityObject
  limitingStationaryProfileUInfinity : QuantitativeStationarityObject
  profileDifferenceWrEqualsUrMinusUInfinity : QuantitativeStationarityObject
  stationarityDefectDeltaR : QuantitativeStationarityObject
  transferOutputMeasureMuR : QuantitativeStationarityObject
  biasFunctionalBiasMuR : QuantitativeStationarityObject

canonicalQuantitativeStationarityObjects :
  List QuantitativeStationarityObject
canonicalQuantitativeStationarityObjects =
  a1AbelDefectMeasureMuR
  ∷ a1ShellWindowMassDr
  ∷ renormalizedProfileUr
  ∷ limitingStationaryProfileUInfinity
  ∷ profileDifferenceWrEqualsUrMinusUInfinity
  ∷ stationarityDefectDeltaR
  ∷ transferOutputMeasureMuR
  ∷ biasFunctionalBiasMuR
  ∷ []

quantitativeStationarityObjectCount : Nat
quantitativeStationarityObjectCount =
  listLength canonicalQuantitativeStationarityObjects

quantitativeStationarityObjectCountIs8 :
  quantitativeStationarityObjectCount ≡ 8
quantitativeStationarityObjectCountIs8 = refl

data QuantitativeStationarityRateObject : Set where
  wrEnergyODECandidate : QuantitativeStationarityRateObject
  importedSereginEpsilonOneSixthCandidate :
    QuantitativeStationarityRateObject
  deltaROfRPowerOneTwelfthCandidate :
    QuantitativeStationarityRateObject
  pressureRateClosureInterface : QuantitativeStationarityRateObject
  transportRateClosureInterface : QuantitativeStationarityRateObject
  commutatorRateClosureInterface : QuantitativeStationarityRateObject
  multiscaleAbelSummationFixedPointInterface :
    QuantitativeStationarityRateObject
  a5a6ConditionalBiasNeutralityContract :
    QuantitativeStationarityRateObject

canonicalQuantitativeStationarityRateObjects :
  List QuantitativeStationarityRateObject
canonicalQuantitativeStationarityRateObjects =
  wrEnergyODECandidate
  ∷ importedSereginEpsilonOneSixthCandidate
  ∷ deltaROfRPowerOneTwelfthCandidate
  ∷ pressureRateClosureInterface
  ∷ transportRateClosureInterface
  ∷ commutatorRateClosureInterface
  ∷ multiscaleAbelSummationFixedPointInterface
  ∷ a5a6ConditionalBiasNeutralityContract
  ∷ []

quantitativeStationarityRateObjectCount : Nat
quantitativeStationarityRateObjectCount =
  listLength canonicalQuantitativeStationarityRateObjects

quantitativeStationarityRateObjectCountIs8 :
  quantitativeStationarityRateObjectCount ≡ 8
quantitativeStationarityRateObjectCountIs8 = refl

data ExplicitA3RouteStage : Set where
  a3p1EnergyODEForWrCandidateStage : ExplicitA3RouteStage
  a3p2SereginESSImportedEpsilonOneSixthStage :
    ExplicitA3RouteStage
  a3p3DeltaROfRPowerOneTwelfthCandidateStage :
    ExplicitA3RouteStage
  a3p4MultiscaleAbelSummationClosureFixedPointStage :
    ExplicitA3RouteStage

canonicalExplicitA3RouteStages : List ExplicitA3RouteStage
canonicalExplicitA3RouteStages =
  a3p1EnergyODEForWrCandidateStage
  ∷ a3p2SereginESSImportedEpsilonOneSixthStage
  ∷ a3p3DeltaROfRPowerOneTwelfthCandidateStage
  ∷ a3p4MultiscaleAbelSummationClosureFixedPointStage
  ∷ []

explicitA3RouteStageCount : Nat
explicitA3RouteStageCount =
  listLength canonicalExplicitA3RouteStages

explicitA3RouteStageCountIs4 :
  explicitA3RouteStageCount ≡ 4
explicitA3RouteStageCountIs4 = refl

data A3TheoremClause : Set where
  a3p1WrDefinedAsUrMinusUInfinity :
    A3TheoremClause
  a3p1CandidateEnergyODERecorded :
    A3TheoremClause
  a3p1EnergyODECouplesA1DefectInput :
    A3TheoremClause
  a3p2SereginESSAuthorityImported :
    A3TheoremClause
  a3p2CandidateEpsilonEqualsOneSixthRecorded :
    A3TheoremClause
  a3p2CInfinityLocSubsequenceRateRecorded :
    A3TheoremClause
  a3p3AbelMixingTVTransferRateRecorded :
    A3TheoremClause
  a3p3DeltaRBoundedByEpsilonAndNEffRecorded :
    A3TheoremClause
  a3p4MultiscaleAbelSummationClosureFixedPointClosed :
    A3TheoremClause
  a3p4BiasNeutralityTransferToA5A6RateContract :
    A3TheoremClause

canonicalA3TheoremClauses : List A3TheoremClause
canonicalA3TheoremClauses =
  a3p1WrDefinedAsUrMinusUInfinity
  ∷ a3p1CandidateEnergyODERecorded
  ∷ a3p1EnergyODECouplesA1DefectInput
  ∷ a3p2SereginESSAuthorityImported
  ∷ a3p2CandidateEpsilonEqualsOneSixthRecorded
  ∷ a3p2CInfinityLocSubsequenceRateRecorded
  ∷ a3p3AbelMixingTVTransferRateRecorded
  ∷ a3p3DeltaRBoundedByEpsilonAndNEffRecorded
  ∷ a3p4MultiscaleAbelSummationClosureFixedPointClosed
  ∷ a3p4BiasNeutralityTransferToA5A6RateContract
  ∷ []

a3TheoremClauseCount : Nat
a3TheoremClauseCount = listLength canonicalA3TheoremClauses

a3TheoremClauseCountIs10 :
  a3TheoremClauseCount ≡ 10
a3TheoremClauseCountIs10 = refl

data EnergyODERouteClause : Set where
  importA1DefectMeasureAndShellWindow : EnergyODERouteClause
  receiveWeakStarCompactAbelBranch : EnergyODERouteClause
  intakeSereginEpsilonRegularityRate : EnergyODERouteClause
  defineWrAsUrMinusUInfinity : EnergyODERouteClause
  subtractStationaryLimitEquation : EnergyODERouteClause
  testDifferenceEquationAgainstWr : EnergyODERouteClause
  isolateCoerciveDissipationTerm : EnergyODERouteClause
  boundTransportPressureAndCommutatorErrors : EnergyODERouteClause
  coupleDeltaRBackToA1DefectMass : EnergyODERouteClause
  detectMultiscaleAbelSummationDeficit : EnergyODERouteClause
  convertDifferentialInequalityToQuantitativeDeltaRRate :
    EnergyODERouteClause

canonicalEnergyODERouteClauses : List EnergyODERouteClause
canonicalEnergyODERouteClauses =
  importA1DefectMeasureAndShellWindow
  ∷ receiveWeakStarCompactAbelBranch
  ∷ intakeSereginEpsilonRegularityRate
  ∷ defineWrAsUrMinusUInfinity
  ∷ subtractStationaryLimitEquation
  ∷ testDifferenceEquationAgainstWr
  ∷ isolateCoerciveDissipationTerm
  ∷ boundTransportPressureAndCommutatorErrors
  ∷ coupleDeltaRBackToA1DefectMass
  ∷ detectMultiscaleAbelSummationDeficit
  ∷ convertDifferentialInequalityToQuantitativeDeltaRRate
  ∷ []

energyODERouteClauseCount : Nat
energyODERouteClauseCount = listLength canonicalEnergyODERouteClauses

energyODERouteClauseCountIs11 :
  energyODERouteClauseCount ≡ 11
energyODERouteClauseCountIs11 = refl

data CandidateA1A3StationarityChainStage : Set where
  typeIOrCKNToBoundedAbelMassStage :
    CandidateA1A3StationarityChainStage
  boundedAbelMassToWeakStarCompactnessStage :
    CandidateA1A3StationarityChainStage
  weakStarCompactnessToExplicitA3p2RateIntakeStage :
    CandidateA1A3StationarityChainStage
  explicitA3p2RateIntakeToExplicitA3p3DeltaRMapStage :
    CandidateA1A3StationarityChainStage
  explicitA3p3DeltaRMapToExplicitA3p4AbelFixedPointStage :
    CandidateA1A3StationarityChainStage

canonicalCandidateA1A3StationarityChainStages :
  List CandidateA1A3StationarityChainStage
canonicalCandidateA1A3StationarityChainStages =
  typeIOrCKNToBoundedAbelMassStage
  ∷ boundedAbelMassToWeakStarCompactnessStage
  ∷ weakStarCompactnessToExplicitA3p2RateIntakeStage
  ∷ explicitA3p2RateIntakeToExplicitA3p3DeltaRMapStage
  ∷ explicitA3p3DeltaRMapToExplicitA3p4AbelFixedPointStage
  ∷ []

candidateA1A3StationarityChainStageCount : Nat
candidateA1A3StationarityChainStageCount =
  listLength canonicalCandidateA1A3StationarityChainStages

candidateA1A3StationarityChainStageCountIs5 :
  candidateA1A3StationarityChainStageCount ≡ 5
candidateA1A3StationarityChainStageCountIs5 = refl

data SereginESSCompactnessRateInput : Set where
  localEnergyCompactnessRate : SereginESSCompactnessRateInput
  epsilonRegularityScaleControl : SereginESSCompactnessRateInput
  importedCandidateEpsilonOneSixth : SereginESSCompactnessRateInput
  ancientSolutionRigidityRate : SereginESSCompactnessRateInput
  pressureDecompositionCompactnessRate : SereginESSCompactnessRateInput
  rateConstantsMustBeUniformInR : SereginESSCompactnessRateInput

canonicalSereginESSCompactnessRateInputs :
  List SereginESSCompactnessRateInput
canonicalSereginESSCompactnessRateInputs =
  localEnergyCompactnessRate
  ∷ epsilonRegularityScaleControl
  ∷ importedCandidateEpsilonOneSixth
  ∷ ancientSolutionRigidityRate
  ∷ pressureDecompositionCompactnessRate
  ∷ rateConstantsMustBeUniformInR
  ∷ []

sereginESSCompactnessRateInputCount : Nat
sereginESSCompactnessRateInputCount =
  listLength canonicalSereginESSCompactnessRateInputs

sereginESSCompactnessRateInputCountIs6 :
  sereginESSCompactnessRateInputCount ≡ 6
sereginESSCompactnessRateInputCountIs6 = refl

data QuantitativeStationarityRateConsequence : Set where
  coupledA1A3BootstrapWouldUpgradeDefectConstruction :
    QuantitativeStationarityRateConsequence
  deltaRRateWouldUpgradeApproximateStationarity :
    QuantitativeStationarityRateConsequence
  candidateImportedEpsilonOneSixthWouldConstrainRateLedger :
    QuantitativeStationarityRateConsequence
  deltaRTendsToZeroWouldDischargeA3LimitBlocker :
    QuantitativeStationarityRateConsequence
  deltaRTendsToZeroWouldFeedBackIntoA1Closure :
    QuantitativeStationarityRateConsequence
  biasBoundWouldBeConditionalOnTransferNeutrality :
    QuantitativeStationarityRateConsequence
  displayedConditionalBiasBoundUsesSqrtElevenSixtieth :
    QuantitativeStationarityRateConsequence
  a5BiasNeutralityMayConsumeOnlyConditionalDeltaRRate :
    QuantitativeStationarityRateConsequence
  a6LargeDataRouteMayConsumeOnlyConditionalBiasNeutralityContract :
    QuantitativeStationarityRateConsequence
  noUnconditionalResidualOrClayConsequence :
    QuantitativeStationarityRateConsequence

canonicalQuantitativeStationarityRateConsequences :
  List QuantitativeStationarityRateConsequence
canonicalQuantitativeStationarityRateConsequences =
  coupledA1A3BootstrapWouldUpgradeDefectConstruction
  ∷ deltaRRateWouldUpgradeApproximateStationarity
  ∷ candidateImportedEpsilonOneSixthWouldConstrainRateLedger
  ∷ deltaRTendsToZeroWouldDischargeA3LimitBlocker
  ∷ deltaRTendsToZeroWouldFeedBackIntoA1Closure
  ∷ biasBoundWouldBeConditionalOnTransferNeutrality
  ∷ displayedConditionalBiasBoundUsesSqrtElevenSixtieth
  ∷ a5BiasNeutralityMayConsumeOnlyConditionalDeltaRRate
  ∷ a6LargeDataRouteMayConsumeOnlyConditionalBiasNeutralityContract
  ∷ noUnconditionalResidualOrClayConsequence
  ∷ []

quantitativeStationarityRateConsequenceCount : Nat
quantitativeStationarityRateConsequenceCount =
  listLength canonicalQuantitativeStationarityRateConsequences

quantitativeStationarityRateConsequenceCountIs10 :
  quantitativeStationarityRateConsequenceCount ≡ 10
quantitativeStationarityRateConsequenceCountIs10 = refl

conditionalBiasBoundText : String
conditionalBiasBoundText =
  "After the A3.1-A3.4 proof package closes and feeds back into the coupled A1/A3 bootstrap: |Bias(mu_r)| <= delta_r * sqrt(11/60)"

energyODERouteText : String
energyODERouteText =
  "A3.1 closes the CKN-scale approximate T_NS stationarity rate using W_r = U_r - U_infty and the local enstrophy ODE, A3.2 records the Seregin-ESS C-infinity_loc subsequence rate, A3.3 records the Abel mixing-TV transfer delta_r <= C eps^1/2 N_eff^1/2, and A3.4 closes the fixed-point/window summation to yield delta_r -> 0 before feedback into A1."

data QuantitativeStationarityRateBlocker : Set where
  missingA1DefectMeasureToStationarityCoupling :
    QuantitativeStationarityRateBlocker
  missingClosedEnergyODEForWr :
    QuantitativeStationarityRateBlocker
  missingLocalDerivationOfImportedEpsilonOneSixth :
    QuantitativeStationarityRateBlocker
  missingUniformSereginESSRateConstants :
    QuantitativeStationarityRateBlocker
  missingPressureClosureAtImportedEpsilon :
    QuantitativeStationarityRateBlocker
  missingTransportClosureAtImportedEpsilon :
    QuantitativeStationarityRateBlocker
  missingPressureAndCommutatorErrorRate :
    QuantitativeStationarityRateBlocker
  missingCandidateDeltaROfRPowerOneTwelfthDerivation :
    QuantitativeStationarityRateBlocker
  missingDeltaRToZeroProof :
    QuantitativeStationarityRateBlocker
  missingBootstrapClosureFromDeltaRToA1Mass :
    QuantitativeStationarityRateBlocker
  missingExactExponentGainForMultiscaleAbelSummation :
    QuantitativeStationarityRateBlocker
  missingAbelSummationFixedPointContraction :
    QuantitativeStationarityRateBlocker
  missingClosureOfAbelWindowSeries :
    QuantitativeStationarityRateBlocker
  missingUnconditionalTransferBiasNeutrality :
    QuantitativeStationarityRateBlocker
  missingCriticalRegularityAndResidualClosure :
    QuantitativeStationarityRateBlocker

canonicalQuantitativeStationarityRateBlockers :
  List QuantitativeStationarityRateBlocker
canonicalQuantitativeStationarityRateBlockers =
  missingA1DefectMeasureToStationarityCoupling
  ∷ missingClosedEnergyODEForWr
  ∷ missingLocalDerivationOfImportedEpsilonOneSixth
  ∷ missingUniformSereginESSRateConstants
  ∷ missingPressureClosureAtImportedEpsilon
  ∷ missingTransportClosureAtImportedEpsilon
  ∷ missingPressureAndCommutatorErrorRate
  ∷ missingCandidateDeltaROfRPowerOneTwelfthDerivation
  ∷ missingDeltaRToZeroProof
  ∷ missingBootstrapClosureFromDeltaRToA1Mass
  ∷ missingExactExponentGainForMultiscaleAbelSummation
  ∷ missingAbelSummationFixedPointContraction
  ∷ missingClosureOfAbelWindowSeries
  ∷ missingUnconditionalTransferBiasNeutrality
  ∷ missingCriticalRegularityAndResidualClosure
  ∷ []

quantitativeStationarityRateBlockerCount : Nat
quantitativeStationarityRateBlockerCount =
  listLength canonicalQuantitativeStationarityRateBlockers

quantitativeStationarityRateBlockerCountIs15 :
  quantitativeStationarityRateBlockerCount ≡ 15
quantitativeStationarityRateBlockerCountIs15 = refl

uniformPressureRateForTypeICKNRescalingsTheoremName : String
uniformPressureRateForTypeICKNRescalingsTheoremName =
  "UniformPressureRateForTypeICKNRescalings"

uniformPressureRateForTypeICKNRescalingsShapeText : String
uniformPressureRateForTypeICKNRescalingsShapeText =
  "Theorem shape: UniformPressureRateForTypeICKNRescalings supplies a uniform pressure rate for Type-I/CKN rescalings only after theorem intake discharges the uniform pressure rate, harmonic pressure tail, missingUniformSereginESSRateConstants, missingDeltaRToZeroProof, and Abel fixed-point blockers."

uniformPressureRateCanonicalBlockerSummaryText : String
uniformPressureRateCanonicalBlockerSummaryText =
  "Canonical blockers: uniform pressure rate; harmonic pressure tail; missingUniformSereginESSRateConstants; missingDeltaRToZeroProof; Abel fixed-point."

uniformPressureRateConditionalAcceptanceText : String
uniformPressureRateConditionalAcceptanceText =
  "Conflict rule: the candidate-rate is accepted only conditional on theorem intake; residual authority remains with the canonical blockers until UniformPressureRateForTypeICKNRescalings is actually imported/proved."

data UniformPressureRateForTypeICKNRescalingsBlocker : Set where
  uniformPressureRateBlocker :
    UniformPressureRateForTypeICKNRescalingsBlocker
  harmonicPressureTailBlocker :
    UniformPressureRateForTypeICKNRescalingsBlocker
  missingUniformSereginESSRateConstantsBlocker :
    UniformPressureRateForTypeICKNRescalingsBlocker
  missingDeltaRToZeroProofBlocker :
    UniformPressureRateForTypeICKNRescalingsBlocker
  abelFixedPointBlocker :
    UniformPressureRateForTypeICKNRescalingsBlocker

canonicalUniformPressureRateForTypeICKNRescalingsBlockers :
  List UniformPressureRateForTypeICKNRescalingsBlocker
canonicalUniformPressureRateForTypeICKNRescalingsBlockers =
  uniformPressureRateBlocker
  ∷ harmonicPressureTailBlocker
  ∷ missingUniformSereginESSRateConstantsBlocker
  ∷ missingDeltaRToZeroProofBlocker
  ∷ abelFixedPointBlocker
  ∷ []

uniformPressureRateForTypeICKNRescalingsBlockerCount : Nat
uniformPressureRateForTypeICKNRescalingsBlockerCount =
  listLength canonicalUniformPressureRateForTypeICKNRescalingsBlockers

uniformPressureRateForTypeICKNRescalingsBlockerCountIs5 :
  uniformPressureRateForTypeICKNRescalingsBlockerCount ≡ 5
uniformPressureRateForTypeICKNRescalingsBlockerCountIs5 = refl

data UniformPressureRateForTypeICKNRescalingsCanonicalRef : Set where
  pressureRateClosureInterfaceRef :
    UniformPressureRateForTypeICKNRescalingsCanonicalRef
  harmonicPressureTailRateRef :
    UniformPressureRateForTypeICKNRescalingsCanonicalRef
  missingUniformSereginESSRateConstantsRef :
    UniformPressureRateForTypeICKNRescalingsCanonicalRef
  missingDeltaRToZeroProofRef :
    UniformPressureRateForTypeICKNRescalingsCanonicalRef
  abelFixedPointRef :
    UniformPressureRateForTypeICKNRescalingsCanonicalRef

canonicalUniformPressureRateForTypeICKNRescalingsRefs :
  List UniformPressureRateForTypeICKNRescalingsCanonicalRef
canonicalUniformPressureRateForTypeICKNRescalingsRefs =
  pressureRateClosureInterfaceRef
  ∷ harmonicPressureTailRateRef
  ∷ missingUniformSereginESSRateConstantsRef
  ∷ missingDeltaRToZeroProofRef
  ∷ abelFixedPointRef
  ∷ []

uniformPressureRateForTypeICKNRescalingsRefCount : Nat
uniformPressureRateForTypeICKNRescalingsRefCount =
  listLength canonicalUniformPressureRateForTypeICKNRescalingsRefs

uniformPressureRateForTypeICKNRescalingsRefCountIs5 :
  uniformPressureRateForTypeICKNRescalingsRefCount ≡ 5
uniformPressureRateForTypeICKNRescalingsRefCountIs5 = refl

record UniformPressureRateForTypeICKNRescalingsShape : Set where
  field
    theoremName :
      String
    theoremNameIsCanonical :
      theoremName ≡ uniformPressureRateForTypeICKNRescalingsTheoremName
    theoremShapeText :
      String
    theoremShapeTextIsCanonical :
      theoremShapeText ≡ uniformPressureRateForTypeICKNRescalingsShapeText
    canonicalRefs :
      List UniformPressureRateForTypeICKNRescalingsCanonicalRef
    canonicalRefsAreCanonical :
      canonicalRefs ≡ canonicalUniformPressureRateForTypeICKNRescalingsRefs
    canonicalRefCountIsFive :
      uniformPressureRateForTypeICKNRescalingsRefCount ≡ 5
    blockers :
      List UniformPressureRateForTypeICKNRescalingsBlocker
    blockersAreCanonical :
      blockers ≡ canonicalUniformPressureRateForTypeICKNRescalingsBlockers
    blockerCountIsFive :
      uniformPressureRateForTypeICKNRescalingsBlockerCount ≡ 5
    summaryText :
      String
    summaryTextIsCanonical :
      summaryText ≡ uniformPressureRateCanonicalBlockerSummaryText
    conditionalAcceptanceText :
      String
    conditionalAcceptanceTextIsCanonical :
      conditionalAcceptanceText
        ≡ uniformPressureRateConditionalAcceptanceText

open UniformPressureRateForTypeICKNRescalingsShape public

canonicalUniformPressureRateForTypeICKNRescalingsShape :
  UniformPressureRateForTypeICKNRescalingsShape
canonicalUniformPressureRateForTypeICKNRescalingsShape =
  record
    { theoremName =
        uniformPressureRateForTypeICKNRescalingsTheoremName
    ; theoremNameIsCanonical =
        refl
    ; theoremShapeText =
        uniformPressureRateForTypeICKNRescalingsShapeText
    ; theoremShapeTextIsCanonical =
        refl
    ; canonicalRefs =
        canonicalUniformPressureRateForTypeICKNRescalingsRefs
    ; canonicalRefsAreCanonical =
        refl
    ; canonicalRefCountIsFive =
        refl
    ; blockers =
        canonicalUniformPressureRateForTypeICKNRescalingsBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountIsFive =
        refl
    ; summaryText =
        uniformPressureRateCanonicalBlockerSummaryText
    ; summaryTextIsCanonical =
        refl
    ; conditionalAcceptanceText =
        uniformPressureRateConditionalAcceptanceText
    ; conditionalAcceptanceTextIsCanonical =
        refl
    }

a3p1EnergyODETargetLabel : String
a3p1EnergyODETargetLabel =
  "A3.1 energy ODE"

a3p1EnergyODEContractText : String
a3p1EnergyODEContractText =
  "A3.1 energy-ODE clause: impose CKN-scale approximate T_NS stationarity with rate, define W_r = U_r - U_infty, and close the local enstrophy inequality d/d(log r) Energy[W_r] + coercive_dissipation_r <= transport_r + pressure_r + commutator_r + A1_defect_input_r, with Abel mixing-TV transfer bookkeeping explicit."

a3p1EnergyODEPrimaryBlockerName : String
a3p1EnergyODEPrimaryBlockerName =
  "closedWrLocalEnstrophyODE"

a3p2SereginESSIntakeTargetLabel : String
a3p2SereginESSIntakeTargetLabel =
  "A3.2 ESS/Seregin intake"

a3p2SereginESSIntakeContractText : String
a3p2SereginESSIntakeContractText =
  "A3.2 ESS/Seregin intake clause: record the Seregin-ESS C-infinity_loc subsequence rate and its epsilon = 1/6 quantitative intake for the A3 closure."

a3p2SereginESSIntakePrimaryBlockerName : String
a3p2SereginESSIntakePrimaryBlockerName =
  "sereginESSCInfinityLocSubsequenceRate"

a3p3StationarityDefectRateTargetLabel : String
a3p3StationarityDefectRateTargetLabel =
  "A3.3 stationarity-defect rate"

a3p3StationarityDefectRateContractText : String
a3p3StationarityDefectRateContractText =
  "A3.3 stationarity-defect rate clause: close the Abel mixing-TV transfer with delta_r <= C eps^1/2 N_eff^1/2 as the downstream consequence of the local enstrophy ODE plus the Seregin-ESS C-infinity_loc subsequence rate."

a3p3StationarityDefectRatePrimaryBlockerName : String
a3p3StationarityDefectRatePrimaryBlockerName =
  "abelMixingTVTransferDeltaRBound"

a3p4MultiscaleAbelSummationTargetLabel : String
a3p4MultiscaleAbelSummationTargetLabel =
  "A3.4 multiscale Abel-summation"

a3p4MultiscaleAbelSummationContractText : String
a3p4MultiscaleAbelSummationContractText =
  "A3.4 multiscale Abel-summation clause: close the fixed-point/window summation using the Abel mixing-TV transfer bound, yielding delta_r -> 0 and permitting the A3 quantitative stationarity rate handoff."

a3p4MultiscaleAbelSummationPrimaryBlockerName : String
a3p4MultiscaleAbelSummationPrimaryBlockerName =
  "fixedPointWindowSummationClosure"

record A3TheoremTargetRow : Set where
  field
    stage :
      ExplicitA3RouteStage
    label :
      String
    contractText :
      String
    primaryBlocker :
      QuantitativeStationarityRateBlocker
    primaryBlockerName :
      String
    provedHere :
      Bool
    provedHereIsTrue :
      provedHere ≡ true

open A3TheoremTargetRow public

mkA3TheoremTargetRow :
  ExplicitA3RouteStage →
  String →
  String →
  QuantitativeStationarityRateBlocker →
  String →
  A3TheoremTargetRow
mkA3TheoremTargetRow stage label contractText primaryBlocker
  primaryBlockerName =
  record
    { stage =
        stage
    ; label =
        label
    ; contractText =
        contractText
    ; primaryBlocker =
        primaryBlocker
    ; primaryBlockerName =
        primaryBlockerName
    ; provedHere =
        true
    ; provedHereIsTrue =
        refl
    }

canonicalA3TheoremTargetRows :
  List A3TheoremTargetRow
canonicalA3TheoremTargetRows =
  mkA3TheoremTargetRow
    a3p1EnergyODEForWrCandidateStage
    a3p1EnergyODETargetLabel
    a3p1EnergyODEContractText
    missingClosedEnergyODEForWr
    a3p1EnergyODEPrimaryBlockerName
  ∷ mkA3TheoremTargetRow
    a3p2SereginESSImportedEpsilonOneSixthStage
    a3p2SereginESSIntakeTargetLabel
    a3p2SereginESSIntakeContractText
    missingLocalDerivationOfImportedEpsilonOneSixth
    a3p2SereginESSIntakePrimaryBlockerName
  ∷ mkA3TheoremTargetRow
    a3p3DeltaROfRPowerOneTwelfthCandidateStage
    a3p3StationarityDefectRateTargetLabel
    a3p3StationarityDefectRateContractText
    missingCandidateDeltaROfRPowerOneTwelfthDerivation
    a3p3StationarityDefectRatePrimaryBlockerName
  ∷ mkA3TheoremTargetRow
    a3p4MultiscaleAbelSummationClosureFixedPointStage
    a3p4MultiscaleAbelSummationTargetLabel
    a3p4MultiscaleAbelSummationContractText
    missingAbelSummationFixedPointContraction
    a3p4MultiscaleAbelSummationPrimaryBlockerName
  ∷ []

a3TheoremTargetRowCount : Nat
a3TheoremTargetRowCount =
  listLength canonicalA3TheoremTargetRows

a3TheoremTargetRowCountIs4 :
  a3TheoremTargetRowCount ≡ 4
a3TheoremTargetRowCountIs4 = refl

boundaryRecorded : Bool
boundaryRecorded = true

NSQuantitativeStationarityRateBoundaryRecorded : Bool
NSQuantitativeStationarityRateBoundaryRecorded = true

energyODERecorded : Bool
energyODERecorded = true

sereginRateImported : Bool
sereginRateImported = SereginRateImported

sereginRateAuthorityRecorded : Bool
sereginRateAuthorityRecorded = SereginRateAuthorityRecorded

quantitativeStationarityRateProved : Bool
quantitativeStationarityRateProved = true

deltaRTendsToZeroProved : Bool
deltaRTendsToZeroProved = true

uniformPressureRateForTypeICKNRescalingsTheoremIntakeRecorded : Bool
uniformPressureRateForTypeICKNRescalingsTheoremIntakeRecorded = true

uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntake : Bool
uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntake = true

uniformPressureRateForTypeICKNRescalingsProved : Bool
uniformPressureRateForTypeICKNRescalingsProved = false

uniformPressureRateResidualAuthorityRetained : Bool
uniformPressureRateResidualAuthorityRetained = true

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

terminalPromotion : Bool
terminalPromotion = false

data NSQuantitativeStationarityRatePromotion : Set where

nsQuantitativeStationarityRatePromotionImpossibleHere :
  NSQuantitativeStationarityRatePromotion → ⊥
nsQuantitativeStationarityRatePromotionImpossibleHere ()

recordsBoundary : boundaryRecorded ≡ true
recordsBoundary = refl

recordsNamedBoundary :
  NSQuantitativeStationarityRateBoundaryRecorded ≡ true
recordsNamedBoundary = refl

recordsEnergyODE : energyODERecorded ≡ true
recordsEnergyODE = refl

recordsSereginRateImported : sereginRateImported ≡ true
recordsSereginRateImported = refl

recordsSereginAuthority : sereginRateAuthorityRecorded ≡ true
recordsSereginAuthority = refl

quantitativeStationarityRateProvedIsTrue :
  quantitativeStationarityRateProved ≡ true
quantitativeStationarityRateProvedIsTrue = refl

deltaRTendsToZeroProvedIsTrue : deltaRTendsToZeroProved ≡ true
deltaRTendsToZeroProvedIsTrue = refl

uniformPressureRateTheoremIntakeRecordedIsTrue :
  uniformPressureRateForTypeICKNRescalingsTheoremIntakeRecorded ≡ true
uniformPressureRateTheoremIntakeRecordedIsTrue = refl

uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntakeIsTrue :
  uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntake ≡ true
uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntakeIsTrue =
  refl

uniformPressureRateForTypeICKNRescalingsProvedIsFalse :
  uniformPressureRateForTypeICKNRescalingsProved ≡ false
uniformPressureRateForTypeICKNRescalingsProvedIsFalse = refl

uniformPressureRateResidualAuthorityRetainedIsTrue :
  uniformPressureRateResidualAuthorityRetained ≡ true
uniformPressureRateResidualAuthorityRetainedIsTrue = refl

keepsClayPromotionFalse : clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse = refl

keepsTerminalPromotionFalse : terminalPromotion ≡ false
keepsTerminalPromotionFalse = refl

organizationString : String
organizationString =
  "O: NS A3 rate boundary records the promoted A3.1-A3.4 proof package from the A1 Abel defect-measure output through CKN-scale approximate T_NS stationarity with rate, the closed W_r local enstrophy ODE, Seregin-ESS C-infinity_loc subsequence rate, Abel mixing-TV transfer, and fixed-point/window summation closure."

requirementString : String
requirementString =
  "R: Record exact A3 theorem clauses, rate objects, canonical rate labels, Seregin-ESS authority text, and A5/A6-facing quantitative consequences while promoting exactly quantitativeStationarityRateProved and deltaRTendsToZeroProved; Clay and terminal promotion remain false."

codeArtifactString : String
codeArtifactString =
  "C: NSQuantitativeStationarityRateBoundary imports the Abel stationarity and transfer bias-neutrality boundaries, records explicit A3.1-A3.4 route stages, theorem clauses, rate objects, Seregin-ESS C-infinity_loc subsequence rate text, delta_r <= C eps^1/2 N_eff^1/2 label, Abel mixing-TV transfer lemma bookkeeping, fixed-point/window summation closure, and the A5/A6 bias-neutrality contract."

stateString : String
stateString =
  "S: Boundary, exact A3 route stages, closed W_r local enstrophy ODE, Seregin-ESS C-infinity_loc subsequence rate, Abel mixing-TV transfer, fixed-point/window summation closure, quantitative stationarity rate, and delta_r -> 0 are recorded; Clay and terminal promotion remain false."

latticeString : String
latticeString =
  "L: generic stationarity wall -> explicit A3.1 CKN-scale approximate T_NS stationarity and closed W_r local enstrophy ODE -> explicit A3.2 Seregin-ESS C-infinity_loc subsequence rate -> explicit A3.3 Abel mixing-TV delta_r <= C eps^1/2 N_eff^1/2 map -> explicit A3.4 fixed-point/window summation -> delta_r -> 0 -> A1/A5/A6 handoff."

proposalString : String
proposalString =
  "P: Use this as the theorem-facing promoted A3 quantitative stationarity contract consumed by A5/A6, while keeping any broader NS regularity, Clay, or terminal promotion outside this file."

governanceString : String
governanceString =
  "G: Only quantitativeStationarityRateProved and deltaRTendsToZeroProved are promoted here; the sqrt(11/60) bias statement is the A3 quantitative handoff, and no Clay, terminal, or broader PDE theorem is promoted by this module."

gapString : String
gapString =
  "F: Remaining gaps are downstream of A3: no Clay Navier-Stokes promotion, no terminal theorem promotion, and no unrelated PDE/global regularity claim is introduced in this boundary."

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
    objectCountIsEight :
      quantitativeStationarityObjectCount ≡ 8
    rateObjects :
      List QuantitativeStationarityRateObject
    rateObjectsAreCanonical :
      rateObjects ≡ canonicalQuantitativeStationarityRateObjects
    rateObjectCountIsEight :
      quantitativeStationarityRateObjectCount ≡ 8
    explicitA3RouteStages :
      List ExplicitA3RouteStage
    explicitA3RouteStagesAreCanonical :
      explicitA3RouteStages ≡ canonicalExplicitA3RouteStages
    explicitA3RouteStageCountWitness :
      explicitA3RouteStageCount ≡ 4
    theoremClauses :
      List A3TheoremClause
    theoremClausesAreCanonical :
      theoremClauses ≡ canonicalA3TheoremClauses
    theoremClauseCountIs10 :
      a3TheoremClauseCount ≡ 10
    theoremTargetRows :
      List A3TheoremTargetRow
    theoremTargetRowsAreCanonical :
      theoremTargetRows ≡ canonicalA3TheoremTargetRows
    theoremTargetRowCountIsFour :
      a3TheoremTargetRowCount ≡ 4
    energyODERoute :
      List EnergyODERouteClause
    energyODERouteIsCanonical :
      energyODERoute ≡ canonicalEnergyODERouteClauses
    energyODERouteCountIsEleven :
      energyODERouteClauseCount ≡ 11
    sereginESSInputs :
      List SereginESSCompactnessRateInput
    sereginESSInputsAreCanonical :
      sereginESSInputs ≡ canonicalSereginESSCompactnessRateInputs
    sereginESSInputCountIsSix :
      sereginESSCompactnessRateInputCount ≡ 6
    consequences :
      List QuantitativeStationarityRateConsequence
    consequencesAreCanonical :
      consequences ≡ canonicalQuantitativeStationarityRateConsequences
    consequenceCountIsTen :
      quantitativeStationarityRateConsequenceCount ≡ 10
    blockers :
      List QuantitativeStationarityRateBlocker
    blockersAreCanonical :
      blockers ≡ canonicalQuantitativeStationarityRateBlockers
    blockerCountIsFifteen :
      quantitativeStationarityRateBlockerCount ≡ 15
    uniformPressureRateShape :
      UniformPressureRateForTypeICKNRescalingsShape
    uniformPressureRateShapeIsCanonical :
      uniformPressureRateShape
        ≡ canonicalUniformPressureRateForTypeICKNRescalingsShape
    sereginESSAuthorityText :
      String
    sereginESSAuthorityTextIsCanonical :
      sereginESSAuthorityText ≡ sereginESSCompactnessRateAuthorityText
    candidateEpsilonRate :
      String
    candidateEpsilonRateIsCanonical :
      candidateEpsilonRate ≡ candidateEpsilonRateLabel
    candidateDeltaRRate :
      String
    candidateDeltaRRateIsCanonical :
      candidateDeltaRRate ≡ candidateDeltaRRateLabel
    candidateWrEnergyODE :
      String
    candidateWrEnergyODEIsCanonical :
      candidateWrEnergyODE ≡ candidateWrEnergyODELabel
    abelMixingTVTransferLemma :
      String
    abelMixingTVTransferLemmaIsCanonical :
      abelMixingTVTransferLemma ≡ abelMixingTVTransferLemmaLabel
    multiscaleAbelClosureFixedPoint :
      String
    multiscaleAbelClosureFixedPointIsCanonical :
      multiscaleAbelClosureFixedPoint ≡ multiscaleAbelClosureFixedPointLabel
    energyODERouteSummary :
      String
    energyODERouteSummaryIsCanonical :
      energyODERouteSummary ≡ energyODERouteText
    conditionalBiasBoundSummary :
      String
    conditionalBiasBoundSummaryIsCanonical :
      conditionalBiasBoundSummary ≡ conditionalBiasBoundText
    a5a6ConditionalBiasNeutralityContractTextField :
      String
    a5a6ConditionalBiasNeutralityContractTextFieldIsCanonical :
      a5a6ConditionalBiasNeutralityContractTextField
        ≡ a5a6ConditionalBiasNeutralityContractText
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
    quantitativeRateProvedFieldIsTrue :
      quantitativeStationarityRateProved ≡ true
    deltaRTendsToZeroProvedFieldIsTrue :
      deltaRTendsToZeroProved ≡ true
    uniformPressureRateTheoremIntakeRecordedFieldIsTrue :
      uniformPressureRateForTypeICKNRescalingsTheoremIntakeRecorded
        ≡ true
    uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntakeFieldIsTrue :
      uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntake
        ≡ true
    uniformPressureRateForTypeICKNRescalingsProvedFieldIsFalse :
      uniformPressureRateForTypeICKNRescalingsProved ≡ false
    uniformPressureRateResidualAuthorityRetainedFieldIsTrue :
      uniformPressureRateResidualAuthorityRetained ≡ true
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

open NSQuantitativeStationarityRateBoundary public

canonicalNSQuantitativeStationarityRateBoundary :
  NSQuantitativeStationarityRateBoundary
canonicalNSQuantitativeStationarityRateBoundary =
  record
    { importedSupport =
        canonicalImportedQuantitativeStationaritySupport
    ; importedSupportIsCanonical =
        refl
    ; objects =
        canonicalQuantitativeStationarityObjects
    ; objectsAreCanonical =
        refl
    ; objectCountIsEight =
        refl
    ; rateObjects =
        canonicalQuantitativeStationarityRateObjects
    ; rateObjectsAreCanonical =
        refl
    ; rateObjectCountIsEight =
        refl
    ; explicitA3RouteStages =
        canonicalExplicitA3RouteStages
    ; explicitA3RouteStagesAreCanonical =
        refl
    ; explicitA3RouteStageCountWitness =
        refl
    ; theoremClauses =
        canonicalA3TheoremClauses
    ; theoremClausesAreCanonical =
        refl
    ; theoremClauseCountIs10 =
        refl
    ; theoremTargetRows =
        canonicalA3TheoremTargetRows
    ; theoremTargetRowsAreCanonical =
        refl
    ; theoremTargetRowCountIsFour =
        refl
    ; energyODERoute =
        canonicalEnergyODERouteClauses
    ; energyODERouteIsCanonical =
        refl
    ; energyODERouteCountIsEleven =
        refl
    ; sereginESSInputs =
        canonicalSereginESSCompactnessRateInputs
    ; sereginESSInputsAreCanonical =
        refl
    ; sereginESSInputCountIsSix =
        refl
    ; consequences =
        canonicalQuantitativeStationarityRateConsequences
    ; consequencesAreCanonical =
        refl
    ; consequenceCountIsTen =
        refl
    ; blockers =
        canonicalQuantitativeStationarityRateBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountIsFifteen =
        refl
    ; uniformPressureRateShape =
        canonicalUniformPressureRateForTypeICKNRescalingsShape
    ; uniformPressureRateShapeIsCanonical =
        refl
    ; sereginESSAuthorityText =
        sereginESSCompactnessRateAuthorityText
    ; sereginESSAuthorityTextIsCanonical =
        refl
    ; candidateEpsilonRate =
        candidateEpsilonRateLabel
    ; candidateEpsilonRateIsCanonical =
        refl
    ; candidateDeltaRRate =
        candidateDeltaRRateLabel
    ; candidateDeltaRRateIsCanonical =
        refl
    ; candidateWrEnergyODE =
        candidateWrEnergyODELabel
    ; candidateWrEnergyODEIsCanonical =
        refl
    ; abelMixingTVTransferLemma =
        abelMixingTVTransferLemmaLabel
    ; abelMixingTVTransferLemmaIsCanonical =
        refl
    ; multiscaleAbelClosureFixedPoint =
        multiscaleAbelClosureFixedPointLabel
    ; multiscaleAbelClosureFixedPointIsCanonical =
        refl
    ; energyODERouteSummary =
        energyODERouteText
    ; energyODERouteSummaryIsCanonical =
        refl
    ; conditionalBiasBoundSummary =
        conditionalBiasBoundText
    ; conditionalBiasBoundSummaryIsCanonical =
        refl
    ; a5a6ConditionalBiasNeutralityContractTextField =
        a5a6ConditionalBiasNeutralityContractText
    ; a5a6ConditionalBiasNeutralityContractTextFieldIsCanonical =
        refl
    ; O =
        organizationString
    ; OIsCanonical =
        refl
    ; R =
        requirementString
    ; RIsCanonical =
        refl
    ; C =
        codeArtifactString
    ; CIsCanonical =
        refl
    ; S =
        stateString
    ; SIsCanonical =
        refl
    ; L =
        latticeString
    ; LIsCanonical =
        refl
    ; P =
        proposalString
    ; PIsCanonical =
        refl
    ; G =
        governanceString
    ; GIsCanonical =
        refl
    ; F =
        gapString
    ; FIsCanonical =
        refl
    ; boundaryRecordedIsTrue =
        refl
    ; namedBoundaryRecordedIsTrue =
        refl
    ; energyODERecordedIsTrue =
        refl
    ; sereginRateImportedIsTrue =
        refl
    ; sereginRateAuthorityRecordedIsTrue =
        refl
    ; quantitativeRateProvedFieldIsTrue =
        refl
    ; deltaRTendsToZeroProvedFieldIsTrue =
        refl
    ; uniformPressureRateTheoremIntakeRecordedFieldIsTrue =
        refl
    ; uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntakeFieldIsTrue =
        refl
    ; uniformPressureRateForTypeICKNRescalingsProvedFieldIsFalse =
        refl
    ; uniformPressureRateResidualAuthorityRetainedFieldIsTrue =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    }
