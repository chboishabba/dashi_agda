module DASHI.Physics.Foundations.CabarlahSignalInferenceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A finite model of the signals-intelligence operation described in the
-- attached formalism.  Multiple traces can support the same inferred network,
-- so inference from emissions is not a lossless recovery of the emitting world.

data SignalTrace : Set where
  firstRadioTrace : SignalTrace
  secondRadioTrace : SignalTrace
  radarTrace : SignalTrace
  networkTimingTrace : SignalTrace

data InferredEnemyStructure : Set where
  communicationsNetwork : InferredEnemyStructure
  radarOrder : InferredEnemyStructure
  activityPattern : InferredEnemyStructure

inferStructure : SignalTrace → InferredEnemyStructure
inferStructure firstRadioTrace = communicationsNetwork
inferStructure secondRadioTrace = communicationsNetwork
inferStructure radarTrace = radarOrder
inferStructure networkTimingTrace = activityPattern

radioTracesHaveSameInference :
  inferStructure firstRadioTrace
  ≡ inferStructure secondRadioTrace
radioTracesHaveSameInference = refl

firstAndSecondRadioTracesDistinct :
  firstRadioTrace ≡ secondRadioTrace → ⊥
firstAndSecondRadioTracesDistinct ()

SignalInferenceInjective : Set
SignalInferenceInjective =
  (x y : SignalTrace) →
  inferStructure x ≡ inferStructure y →
  x ≡ y

signalInferenceIsNotInjective : ¬ SignalInferenceInjective
signalInferenceIsNotInjective injective =
  firstAndSecondRadioTracesDistinct
    (injective firstRadioTrace secondRadioTrace refl)

------------------------------------------------------------------------
-- Observation, identification, policy, and moral authority are distinct
-- carriers.  No coercion from one stage to the next is supplied.

data ObservationResult : Set where
  traceObserved : ObservationResult

data IdentificationResult : Set where
  boundedNetworkHypothesis : IdentificationResult

data PolicyResult : Set where
  militaryActionAuthorised : PolicyResult

data MoralResult : Set where
  actionJustified : MoralResult

observe : SignalTrace → ObservationResult
observe _ = traceObserved

identify : SignalTrace → IdentificationResult
identify _ = boundedNetworkHypothesis

record SignalInferenceBoundary : Set where
  constructor signalInferenceBoundary
  field
    observationDeterminesExactWorld : Bool
    observationDeterminesExactWorldIsFalse :
      observationDeterminesExactWorld ≡ false

    networkHypothesisAuthorisesMilitaryAction : Bool
    networkHypothesisAuthorisesMilitaryActionIsFalse :
      networkHypothesisAuthorisesMilitaryAction ≡ false

    militaryCapabilityProvesMoralJustification : Bool
    militaryCapabilityProvesMoralJustificationIsFalse :
      militaryCapabilityProvesMoralJustification ≡ false

    interpretiveAnalogyProvesEtymology : Bool
    interpretiveAnalogyProvesEtymologyIsFalse :
      interpretiveAnalogyProvesEtymology ≡ false

    signalInferenceProvesSpecificStrikeChain : Bool
    signalInferenceProvesSpecificStrikeChainIsFalse :
      signalInferenceProvesSpecificStrikeChain ≡ false

open SignalInferenceBoundary public

canonicalSignalInferenceBoundary : SignalInferenceBoundary
canonicalSignalInferenceBoundary =
  signalInferenceBoundary
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- The comparison between interpreting signs and interpreting military signals
-- is recorded only as a declared structural analogy.

data InterpretationDomain : Set where
  theologicalSignInterpretation : InterpretationDomain
  militarySignalInterpretation : InterpretationDomain

data ComparisonAuthority : Set where
  structuralComparisonOnly : ComparisonAuthority
  etymologicalDerivation : ComparisonAuthority
  causalIdentity : ComparisonAuthority

interpretationComparison :
  InterpretationDomain → InterpretationDomain → ComparisonAuthority
interpretationComparison theologicalSignInterpretation militarySignalInterpretation =
  structuralComparisonOnly
interpretationComparison militarySignalInterpretation theologicalSignInterpretation =
  structuralComparisonOnly
interpretationComparison theologicalSignInterpretation theologicalSignInterpretation =
  causalIdentity
interpretationComparison militarySignalInterpretation militarySignalInterpretation =
  causalIdentity

crossDomainComparisonIsStructuralOnly :
  interpretationComparison
    theologicalSignInterpretation
    militarySignalInterpretation
  ≡ structuralComparisonOnly
crossDomainComparisonIsStructuralOnly = refl

structuralComparisonIsNotEtymology :
  structuralComparisonOnly ≡ etymologicalDerivation → ⊥
structuralComparisonIsNotEtymology ()
