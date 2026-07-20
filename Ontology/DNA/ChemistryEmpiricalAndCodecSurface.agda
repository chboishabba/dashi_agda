module Ontology.DNA.ChemistryEmpiricalAndCodecSurface where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base; A; C; G; T; FlatDNA256)
open import Ontology.DNA.ChemistryTernaryQuantizer using (Trit; minus; neutral; plus)
open import Ontology.DNA.StreamingEncoderSurface using
  (EncoderState; initState; stepAdmissible; streamUpdate)
open import Ontology.DNA.OperationalChemistryQuotient using
  (OperationalChemistryFeature; operationalFeatureMap)

------------------------------------------------------------------------
-- Versioned empirical chemistry inputs.  These are authority-bearing data
-- sockets, not universal hard-coded constants.

record ChemistryEnvironment : Set where
  field
    temperatureBin : Nat
    ionicStrengthBin : Nat
    polymeraseBin : Nat

record VersionedChemistryParameters : Set₁ where
  field
    version : Nat
    nearestNeighbourDG : ChemistryEnvironment → Base → Base → Nat
    mismatchPenalty : ChemistryEnvironment → Nat → Nat
    loopPenalty : ChemistryEnvironment → Nat → Nat
    dimerPenalty : ChemistryEnvironment → Nat → Nat
    synthesisRisk : OperationalChemistryFeature → Nat
    sequencingRisk : OperationalChemistryFeature → Nat

record AssayObservation : Set where
  field
    synthesisDropout : Nat
    amplificationBias : Nat
    substitutionCount : Nat
    indelCount : Nat
    recovered : Bool

record EmpiricalValidationCertificate : Set₁ where
  field
    parameters : VersionedChemistryParameters
    ObservationId : Set
    sequence : ObservationId → FlatDNA256
    outcome : ObservationId → AssayObservation
    featureDistance : OperationalChemistryFeature → OperationalChemistryFeature → Nat
    outcomeDistance : AssayObservation → AssayObservation → Nat
    sufficiencyTolerance : Nat
    validationStatement : Set

------------------------------------------------------------------------
-- Exact baseline trit codec and the adaptive chemistry-aware policy boundary.

encodeTritBase : Trit → Base
encodeTritBase minus = A
encodeTritBase neutral = C
encodeTritBase plus = G

decodeTritBase : Base → Trit
decodeTritBase A = minus
decodeTritBase C = neutral
decodeTritBase G = plus
decodeTritBase T = neutral

trit-roundtrip : ∀ t → decodeTritBase (encodeTritBase t) ≡ t
trit-roundtrip minus = refl
trit-roundtrip neutral = refl
trit-roundtrip plus = refl

data ChoiceArity : Set where
  twoChoices threeChoices fourChoices blocked : ChoiceArity

data CapacityAction : Set where
  consumeTrit emitEscape emitExtraBit failClosed : CapacityAction

record AdaptiveChoicePolicy : Set₁ where
  field
    arity : ∀ {n} → EncoderState n → ChoiceArity
    orderedChoice : ∀ {n} → EncoderState n → Trit → Base
    action : ChoiceArity → CapacityAction
    allowed : ∀ {n} (st : EncoderState n) (t : Trit) →
      stepAdmissible st (orderedChoice st t) ≡ true
    recover : Base → Trit
    localInverse : ∀ {n} (st : EncoderState n) (t : Trit) →
      recover (orderedChoice st t) ≡ t

record StreamingCodecTheorem : Set₁ where
  field
    policy : AdaptiveChoicePolicy
    finiteStateSufficient : Set
    checksumCorrect : Set
    channelRecoveryCorrect : Set
    payloadRateBound : Set

-- The direct baseline is exactly invertible but does not claim chemistry
-- admissibility.  A production inhabitant must supply AdaptiveChoicePolicy.
record BaselineCodecReceipt : Set where
  field
    inverse : ∀ t → decodeTritBase (encodeTritBase t) ≡ t

baselineCodecReceipt : BaselineCodecReceipt
baselineCodecReceipt = record { inverse = trit-roundtrip }
