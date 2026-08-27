module DASHI.Core.RecognitionConstitutionNonfactorabilityExact where

open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer

------------------------------------------------------------------------
-- RECOGNITION != CONSTITUTION
--
-- Generic DASHI theorem shape.  A recognitional observer may be useful for a
-- declared consumer without thereby constituting the authority/existence it
-- observes.  Source-specific feminist, Indigenous-sovereignty, accounting and
-- institutional bridges are interpretations of this owner, not its authors.
------------------------------------------------------------------------

record RecognitionSystem (State Recognition Authority : Set) : Set₁ where
  constructor recognitionSystem
  field
    recognize : State → Recognition
    authority : State → Authority

open RecognitionSystem public

record RecognitionCollision
  {State Recognition Authority : Set}
  (system : RecognitionSystem State Recognition Authority) : Set where
  constructor recognitionCollision
  field
    left right : State
    sameRecognition : recognize system left ≡ recognize system right
    differentAuthority : authority system left ≡ authority system right → ⊥

open RecognitionCollision public

collisionGivesConsumerNonDescent :
  ∀ {State Recognition Authority : Set}
    {system : RecognitionSystem State Recognition Authority} →
  RecognitionCollision system →
  Consumer.ConsumerNonDescentWitness
    (recognize system)
    (authority system)
collisionGivesConsumerNonDescent witness =
  Consumer.consumerNonDescentWitness
    (left witness)
    (right witness)
    (sameRecognition witness)
    (differentAuthority witness)

collisionBlocksAuthorityFactorization :
  ∀ {State Recognition Authority : Set}
    {system : RecognitionSystem State Recognition Authority} →
  RecognitionCollision system →
  Consumer.FactorsThrough (recognize system) (authority system) → ⊥
collisionBlocksAuthorityFactorization witness =
  Consumer.nonDescentWitnessBlocksFactorization
    (collisionGivesConsumerNonDescent witness)

FactorsThroughRecognition :
  ∀ {State Recognition Authority : Set} →
  RecognitionSystem State Recognition Authority → Set₁
FactorsThroughRecognition system =
  Consumer.FactorsThrough (recognize system) (authority system)

------------------------------------------------------------------------
-- Finite regression witness: lack of recognition does not determine absence
-- of authority.  These constructors have no domain semantics by themselves.
------------------------------------------------------------------------

data DemoState : Set where
  unrecognizedWithoutAuthority unrecognizedWithAuthority recognizedWithAuthority : DemoState

data DemoRecognition : Set where
  unrecognized recognized : DemoRecognition

data DemoAuthority : Set where
  absentAuthority presentAuthority : DemoAuthority

demoRecognition : DemoState → DemoRecognition
demoRecognition unrecognizedWithoutAuthority = unrecognized
demoRecognition unrecognizedWithAuthority = unrecognized
demoRecognition recognizedWithAuthority = recognized

demoAuthority : DemoState → DemoAuthority
demoAuthority unrecognizedWithoutAuthority = absentAuthority
demoAuthority unrecognizedWithAuthority = presentAuthority
demoAuthority recognizedWithAuthority = presentAuthority

demoSystem : RecognitionSystem DemoState DemoRecognition DemoAuthority
demoSystem = recognitionSystem demoRecognition demoAuthority

unrecognizedCollision : RecognitionCollision demoSystem
unrecognizedCollision =
  recognitionCollision unrecognizedWithoutAuthority unrecognizedWithAuthority refl (λ ())

recognitionDoesNotRecoverAuthority : FactorsThroughRecognition demoSystem → ⊥
recognitionDoesNotRecoverAuthority =
  collisionBlocksAuthorityFactorization unrecognizedCollision

record RecognitionConstitutionBoundary : Set where
  constructor recognitionConstitutionBoundary
  field
    recognitionConstitutesAuthorityByDefault : Bool
    recognitionConstitutesAuthorityByDefaultIsFalse :
      recognitionConstitutesAuthorityByDefault ≡ false
    nonRecognitionProvesAuthorityAbsent : Bool
    nonRecognitionProvesAuthorityAbsentIsFalse :
      nonRecognitionProvesAuthorityAbsent ≡ false
    authorityRequiresRecognitionToExist : Bool
    authorityRequiresRecognitionToExistIsFalse :
      authorityRequiresRecognitionToExist ≡ false

canonicalRecognitionConstitutionBoundary : RecognitionConstitutionBoundary
canonicalRecognitionConstitutionBoundary =
  recognitionConstitutionBoundary false refl false refl false refl
