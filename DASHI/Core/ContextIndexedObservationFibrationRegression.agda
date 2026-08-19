module DASHI.Core.ContextIndexedObservationFibrationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ContextIndexedObservationFibrationExact as Indexed
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ProjectionCategory as Cat
import DASHI.Core.TopDownObservationCalculusExact as Top

------------------------------------------------------------------------
-- Two-context exact model.
--
-- public -> situated is a base-context refinement.  Contravariant restriction
-- forgets the hidden situated coordinate.  The same public observer is
-- sufficient for one consumer but not for the situated hidden-coordinate
-- consumer.
------------------------------------------------------------------------

data DemoContext : Set where
  publicContext situatedContext : DemoContext

data DemoHom : DemoContext → DemoContext → Set where
  publicId : DemoHom publicContext publicContext
  situatedId : DemoHom situatedContext situatedContext
  publicToSituated : DemoHom publicContext situatedContext

demoIdentity : ∀ {context} → DemoHom context context
demoIdentity {publicContext} = publicId
demoIdentity {situatedContext} = situatedId

demoCompose :
  ∀ {A B C} → DemoHom B C → DemoHom A B → DemoHom A C
demoCompose publicId publicId = publicId
demoCompose publicToSituated publicId = publicToSituated
demoCompose situatedId publicToSituated = publicToSituated
demoCompose situatedId situatedId = situatedId

demoIdLeft :
  ∀ {A B} (f : DemoHom A B) → demoCompose demoIdentity f ≡ f
demoIdLeft publicId = refl
demoIdLeft situatedId = refl
demoIdLeft publicToSituated = refl

demoIdRight :
  ∀ {A B} (f : DemoHom A B) → demoCompose f demoIdentity ≡ f
demoIdRight publicId = refl
demoIdRight situatedId = refl
demoIdRight publicToSituated = refl

demoAssoc :
  ∀ {A B C D}
    (f : DemoHom C D)
    (g : DemoHom B C)
    (h : DemoHom A B) →
  demoCompose (demoCompose f g) h ≡ demoCompose f (demoCompose g h)
demoAssoc publicId publicId publicId = refl
demoAssoc publicToSituated publicId publicId = refl
demoAssoc situatedId publicToSituated publicId = refl
demoAssoc situatedId situatedId publicToSituated = refl
demoAssoc situatedId situatedId situatedId = refl

demoCategory : Cat.ProjectionCategory
demoCategory = record
  { Cat.Obj = DemoContext
  ; Cat.Hom = DemoHom
  ; Cat.id = demoIdentity
  ; Cat._∘_ = demoCompose
  ; Cat.id-left = demoIdLeft
  ; Cat.id-right = demoIdRight
  ; Cat.assoc = demoAssoc
  ; Cat.categoryReading = "Two-context public/situated regression category."
  }

DemoFine : DemoContext → Set
DemoFine publicContext = Top.Bit2
DemoFine situatedContext = Top.Bit2 × Top.Bit2

DemoSurface : DemoContext → Set
DemoSurface publicContext = Top.Bit2
DemoSurface situatedContext = Top.Bit2

restrictDemoFine :
  ∀ {A B} → DemoHom A B → DemoFine B → DemoFine A
restrictDemoFine publicId x = x
restrictDemoFine situatedId x = x
restrictDemoFine publicToSituated x = proj₁ x

restrictDemoSurface :
  ∀ {A B} → DemoHom A B → DemoSurface B → DemoSurface A
restrictDemoSurface publicId x = x
restrictDemoSurface situatedId x = x
restrictDemoSurface publicToSituated x = x

observeDemo : (context : DemoContext) → DemoFine context → DemoSurface context
observeDemo publicContext x = x
observeDemo situatedContext x = proj₁ x

fineIdentityLaw :
  ∀ {A} (x : DemoFine A) → restrictDemoFine demoIdentity x ≡ x
fineIdentityLaw {publicContext} x = refl
fineIdentityLaw {situatedContext} x = refl

surfaceIdentityLaw :
  ∀ {A} (x : DemoSurface A) → restrictDemoSurface demoIdentity x ≡ x
surfaceIdentityLaw {publicContext} x = refl
surfaceIdentityLaw {situatedContext} x = refl

fineCompositionLaw :
  ∀ {A B C}
    (first : DemoHom A B)
    (second : DemoHom B C)
    (x : DemoFine C) →
  restrictDemoFine (demoCompose second first) x
  ≡ restrictDemoFine first (restrictDemoFine second x)
fineCompositionLaw publicId publicId x = refl
fineCompositionLaw publicId publicToSituated x = refl
fineCompositionLaw publicToSituated situatedId x = refl
fineCompositionLaw situatedId situatedId x = refl

surfaceCompositionLaw :
  ∀ {A B C}
    (first : DemoHom A B)
    (second : DemoHom B C)
    (x : DemoSurface C) →
  restrictDemoSurface (demoCompose second first) x
  ≡ restrictDemoSurface first (restrictDemoSurface second x)
surfaceCompositionLaw publicId publicId x = refl
surfaceCompositionLaw publicId publicToSituated x = refl
surfaceCompositionLaw publicToSituated situatedId x = refl
surfaceCompositionLaw situatedId situatedId x = refl

observationNaturalityLaw :
  ∀ {A B}
    (change : DemoHom A B)
    (x : DemoFine B) →
  observeDemo A (restrictDemoFine change x)
  ≡ restrictDemoSurface change (observeDemo B x)
observationNaturalityLaw publicId x = refl
observationNaturalityLaw situatedId x = refl
observationNaturalityLaw publicToSituated x = refl

demoIndexedObservation : Indexed.ContextIndexedObservation demoCategory
demoIndexedObservation = record
  { Indexed.Fine = DemoFine
  ; Indexed.Surface = DemoSurface
  ; Indexed.restrictFine = restrictDemoFine
  ; Indexed.restrictSurface = restrictDemoSurface
  ; Indexed.observe = observeDemo
  ; Indexed.restrictFineIdentity = fineIdentityLaw
  ; Indexed.restrictSurfaceIdentity = surfaceIdentityLaw
  ; Indexed.restrictFineComposition = fineCompositionLaw
  ; Indexed.restrictSurfaceComposition = surfaceCompositionLaw
  ; Indexed.observationNaturality = observationNaturalityLaw
  }

DemoOutcome : DemoContext → Set
DemoOutcome publicContext = Top.Bit2
DemoOutcome situatedContext = Top.Bit2

consumeDemo : (context : DemoContext) → DemoFine context → DemoOutcome context
consumeDemo publicContext x = x
consumeDemo situatedContext x = proj₂ x

demoConsumer : Indexed.ContextConsumer demoIndexedObservation
demoConsumer = record
  { Indexed.Outcome = DemoOutcome
  ; Indexed.consume = consumeDemo
  }

publicObservationIsAdequate :
  Indexed.AdequateAt demoConsumer publicContext
publicObservationIsAdequate left right same = same

situatedConsumerNonDescent :
  Descent.ConsumerNonDescentWitness
    (Indexed.observe demoIndexedObservation situatedContext)
    (Indexed.consume demoConsumer situatedContext)
situatedConsumerNonDescent =
  Descent.consumerNonDescentWitness
    (Top.bit0 , Top.bit0)
    (Top.bit0 , Top.bit1)
    refl
    Top.bit0NotBit1

situatedObservationIsNotAdequate :
  Indexed.AdequateAt demoConsumer situatedContext → ⊥
situatedObservationIsNotAdequate =
  Descent.nonDescentWitnessBlocksSufficiency situatedConsumerNonDescent

publicToSituatedLiftCommutesWithObservation :
  (state : DemoFine situatedContext) →
  observeDemo publicContext (restrictDemoFine publicToSituated state)
  ≡ restrictDemoSurface publicToSituated (observeDemo situatedContext state)
publicToSituatedLiftCommutesWithObservation =
  Indexed.observationCommutesWithCartesianLift
    demoIndexedObservation publicToSituated
