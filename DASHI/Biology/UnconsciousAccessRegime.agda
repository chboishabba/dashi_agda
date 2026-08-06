module DASHI.Biology.UnconsciousAccessRegime where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessCoalition as Access
import DASHI.Biology.StateDependentMultiplexTransducer as Stateful

------------------------------------------------------------------------
-- The unconscious is represented as an access/control regime, not a second
-- substance or a storage compartment whose contents possess intrinsic
-- unconsciousness.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data MemoryKind : Set where
  declarativeMemoryKind : MemoryKind
  proceduralMemoryKind : MemoryKind
  perceptualTraceKind : MemoryKind
  interoceptiveTraceKind : MemoryKind

record MemoryTrace : Set where
  constructor memoryTrace
  field
    traceKind : MemoryKind
    traceValue : Bool

open MemoryTrace public

record AccessAvoidanceRegime : Set₁ where
  field
    Representation : Set
    generatedRepresentation : Representation
    comparisonRepresentation : Representation

    accessGate : Representation → Bool
    actionReadout : Representation → Bool

    generatedYetBlocked :
      accessGate generatedRepresentation ≡ false

    comparisonAlsoBlocked :
      accessGate comparisonRepresentation ≡ false

    blockedRepresentationStillChangesAction :
      actionReadout generatedRepresentation
      ≢
      actionReadout comparisonRepresentation

    stableAccessAvoidancePolicy : Bool
    stableAccessAvoidancePolicyIsTrue :
      stableAccessAvoidancePolicy ≡ true

open AccessAvoidanceRegime public

closedGate : Bool → Bool
closedGate _ = false

identityAction : Bool → Bool
identityAction x = x

canonicalAccessAvoidanceRegime : AccessAvoidanceRegime
canonicalAccessAvoidanceRegime =
  record
    { Representation = Bool
    ; generatedRepresentation = true
    ; comparisonRepresentation = false
    ; accessGate = closedGate
    ; actionReadout = identityAction
    ; generatedYetBlocked = refl
    ; comparisonAlsoBlocked = refl
    ; blockedRepresentationStillChangesAction = Stateful.true≢false
    ; stableAccessAvoidancePolicy = true
    ; stableAccessAvoidancePolicyIsTrue = refl
    }

canonicalGeneratedRepresentationBlocked :
  accessGate canonicalAccessAvoidanceRegime
    (generatedRepresentation canonicalAccessAvoidanceRegime)
  ≡
  false
canonicalGeneratedRepresentationBlocked =
  generatedYetBlocked canonicalAccessAvoidanceRegime

canonicalBlockedRepresentationCausallyEffective :
  actionReadout canonicalAccessAvoidanceRegime
    (generatedRepresentation canonicalAccessAvoidanceRegime)
  ≢
  actionReadout canonicalAccessAvoidanceRegime
    (comparisonRepresentation canonicalAccessAvoidanceRegime)
canonicalBlockedRepresentationCausallyEffective =
  blockedRepresentationStillChangesAction canonicalAccessAvoidanceRegime

------------------------------------------------------------------------
-- Memory kind does not determine access.  The same trace can be unavailable
-- in a restricted context and available in a recurrent global context.

canonicalDeclarativeTrace : MemoryTrace
canonicalDeclarativeTrace =
  memoryTrace declarativeMemoryKind false

canonicalDeclarativeTraceRestricted :
  Access.available Access.canonicalAccessRelation
    Access.localRestrictedContext
    (traceValue canonicalDeclarativeTrace)
  ≡
  false
canonicalDeclarativeTraceRestricted = refl

canonicalDeclarativeTraceAvailable :
  Access.available Access.canonicalAccessRelation
    Access.recurrentGlobalContext
    (traceValue canonicalDeclarativeTrace)
  ≡
  true
canonicalDeclarativeTraceAvailable = refl

record UnconsciousRegimeBoundary : Set where
  constructor unconsciousRegimeBoundary
  field
    unconsciousIsSeparateSubstance : Bool
    unconsciousIsSeparateSubstanceIsFalse :
      unconsciousIsSeparateSubstance ≡ false

    memoryKindDeterminesConsciousness : Bool
    memoryKindDeterminesConsciousnessIsFalse :
      memoryKindDeterminesConsciousness ≡ false

    accessBlockedMeansCausallyInert : Bool
    accessBlockedMeansCausallyInertIsFalse :
      accessBlockedMeansCausallyInert ≡ false

    psychoanalyticDiagnosisPromoted : Bool
    psychoanalyticDiagnosisPromotedIsFalse :
      psychoanalyticDiagnosisPromoted ≡ false

canonicalUnconsciousRegimeBoundary : UnconsciousRegimeBoundary
canonicalUnconsciousRegimeBoundary =
  unconsciousRegimeBoundary
    false refl
    false refl
    false refl
    false refl
