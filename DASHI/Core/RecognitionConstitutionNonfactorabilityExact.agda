module DASHI.Core.RecognitionConstitutionNonfactorabilityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RECOGNITION != CONSTITUTION
--
-- Generic DASHI theorem shape.  A recognitional observer may be useful for a
-- declared consumer without thereby constituting the authority/existence it
-- observes.  Source-specific feminist, Indigenous-sovereignty, accounting and
-- institutional bridges are interpretations of this owner, not its authors.
------------------------------------------------------------------------

record RecognitionSystem (State Recognition Authority : Set) : Set where
  constructor recognitionSystem
  field
    recognize : State → Recognition
    authority : State → Authority

record RecognitionCollision
  {State Recognition Authority : Set}
  (system : RecognitionSystem State Recognition Authority) : Set where
  constructor recognitionCollision
  field
    left right : State
    sameRecognition : RecognitionSystem.recognize system left ≡
                      RecognitionSystem.recognize system right
    differentAuthority : RecognitionSystem.authority system left ≡
                         RecognitionSystem.authority system right → ⊥

FactorsThroughRecognition :
  {State Recognition Authority : Set} →
  RecognitionSystem State Recognition Authority → Set
FactorsThroughRecognition {Recognition = Recognition} {Authority = Authority} system =
  Σ (Recognition → Authority) (λ recover →
    (x : _) → recover (RecognitionSystem.recognize system x) ≡
              RecognitionSystem.authority system x)

collisionBlocksAuthorityFactorization :
  {State Recognition Authority : Set} →
  {system : RecognitionSystem State Recognition Authority} →
  RecognitionCollision system →
  FactorsThroughRecognition system → ⊥
collisionBlocksAuthorityFactorization witness (recover , factors) =
  RecognitionCollision.differentAuthority witness
    (trans
      (sym (factors (RecognitionCollision.left witness)))
      (trans
        (cong recover (RecognitionCollision.sameRecognition witness))
        (factors (RecognitionCollision.right witness))))

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
