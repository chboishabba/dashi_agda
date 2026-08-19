module DASHI.Core.ContextIndexedObservationFibrationExact where

------------------------------------------------------------------------
-- CONTEXT-INDEXED OBSERVATION AS A SPLIT FIBRATION / PRESHEAF PRESENTATION
--
-- DASHI repeatedly has data whose meaningful carrier changes with context,
-- query, consumer or authority frame.  This module puts that pattern above the
-- individual hyperfabric and observer instances.
--
-- A base ProjectionCategory supplies context changes.  Fine and public surface
-- carriers are contravariantly restricted along those changes, and observation
-- is required to commute with restriction.  The resulting indexed family has
-- canonical split cartesian lifts: restriction along a composite factors
-- through restriction along each stage.
--
-- SOURCE / METHOD CALIBRATION
--
-- Jean Benabou,
-- "Fibered Categories and the Foundations of Naive Category Theory",
-- Journal of Symbolic Logic 50(1), 1985, 10--37.
-- DOI: 10.2307/2273784.
--
-- Saunders Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
-- Springer, 1998. DOI: 10.1007/978-1-4757-4721-8.
--
-- The code below is a strict split indexed presentation over DASHI's existing
-- ProjectionCategory.  It does not claim that every semantic context system in
-- the repository has already been supplied with these laws, nor does it claim
-- the full Grothendieck equivalence between fibrations and pseudofunctors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ProjectionCategory as Cat

record ContextIndexedObservation
    (base : Cat.ProjectionCategory) : Set₁ where
  field
    Fine : Cat.Obj base → Set
    Surface : Cat.Obj base → Set

    restrictFine :
      ∀ {A B} → Cat.Hom base A B → Fine B → Fine A
    restrictSurface :
      ∀ {A B} → Cat.Hom base A B → Surface B → Surface A

    observe : (context : Cat.Obj base) → Fine context → Surface context

    restrictFineIdentity :
      ∀ {A} (x : Fine A) →
      restrictFine (Cat.id base) x ≡ x
    restrictSurfaceIdentity :
      ∀ {A} (y : Surface A) →
      restrictSurface (Cat.id base) y ≡ y

    restrictFineComposition :
      ∀ {A B C}
        (first : Cat.Hom base A B)
        (second : Cat.Hom base B C)
        (x : Fine C) →
      restrictFine (Cat._∘_ base second first) x
      ≡ restrictFine first (restrictFine second x)

    restrictSurfaceComposition :
      ∀ {A B C}
        (first : Cat.Hom base A B)
        (second : Cat.Hom base B C)
        (y : Surface C) →
      restrictSurface (Cat._∘_ base second first) y
      ≡ restrictSurface first (restrictSurface second y)

    observationNaturality :
      ∀ {A B}
        (change : Cat.Hom base A B)
        (x : Fine B) →
      observe A (restrictFine change x)
      ≡ restrictSurface change (observe B x)

open ContextIndexedObservation public

FineTotal :
  ∀ {base : Cat.ProjectionCategory} →
  ContextIndexedObservation base → Set
FineTotal {base} indexed = Σ (Cat.Obj base) (Fine indexed)

SurfaceTotal :
  ∀ {base : Cat.ProjectionCategory} →
  ContextIndexedObservation base → Set
SurfaceTotal {base} indexed = Σ (Cat.Obj base) (Surface indexed)

observeTotal :
  ∀ {base : Cat.ProjectionCategory}
    (indexed : ContextIndexedObservation base) →
  FineTotal indexed → SurfaceTotal indexed
observeTotal indexed (context , x) = context , observe indexed context x

record TotalFineArrow
    {base : Cat.ProjectionCategory}
    (indexed : ContextIndexedObservation base)
    (source target : FineTotal indexed) : Set where
  constructor totalFineArrow
  field
    baseArrow : Cat.Hom base (proj₁ source) (proj₁ target)
    sourceIsRestriction :
      proj₂ source ≡ restrictFine indexed baseArrow (proj₂ target)

open TotalFineArrow public

cartesianSource :
  ∀ {base : Cat.ProjectionCategory}
    (indexed : ContextIndexedObservation base)
    {A B : Cat.Obj base} →
  Cat.Hom base A B → Fine indexed B → FineTotal indexed
cartesianSource indexed {A} change target =
  A , restrictFine indexed change target

canonicalSplitCartesianLift :
  ∀ {base : Cat.ProjectionCategory}
    (indexed : ContextIndexedObservation base)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B)
    (target : Fine indexed B) →
  TotalFineArrow indexed
    (cartesianSource indexed change target)
    (B , target)
canonicalSplitCartesianLift indexed change target =
  totalFineArrow change refl

-- Universal factorisation equation for the chosen split lifts.  If a source
-- state reaches target x over the composite second-after-first context map,
-- then it reaches the canonical lift over second by first restricting along
-- second and then along first.
splitCartesianFactorization :
  ∀ {base : Cat.ProjectionCategory}
    (indexed : ContextIndexedObservation base)
    {A B C : Cat.Obj base}
    (first : Cat.Hom base A B)
    (second : Cat.Hom base B C)
    (source : Fine indexed A)
    (target : Fine indexed C) →
  source ≡
    restrictFine indexed (Cat._∘_ base second first) target →
  source ≡
    restrictFine indexed first (restrictFine indexed second target)
splitCartesianFactorization indexed first second source target sourceComposite =
  trans
    sourceComposite
    (restrictFineComposition indexed first second target)

observationCommutesWithCartesianLift :
  ∀ {base : Cat.ProjectionCategory}
    (indexed : ContextIndexedObservation base)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B)
    (target : Fine indexed B) →
  observe indexed A (restrictFine indexed change target)
  ≡ restrictSurface indexed change (observe indexed B target)
observationCommutesWithCartesianLift indexed = observationNaturality indexed

------------------------------------------------------------------------
-- Context-indexed consumer adequacy.
------------------------------------------------------------------------

record ContextConsumer
    {base : Cat.ProjectionCategory}
    (indexed : ContextIndexedObservation base) : Set₁ where
  field
    Outcome : Cat.Obj base → Set
    consume : (context : Cat.Obj base) → Fine indexed context → Outcome context

open ContextConsumer public

AdequateAt :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : ContextIndexedObservation base} →
  ContextConsumer indexed →
  (context : Cat.Obj base) → Set
AdequateAt {indexed = indexed} consumer context =
  Descent.ConsumerSufficient
    (observe indexed context)
    (consume consumer context)

adequacyIsContextLocal :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : ContextIndexedObservation base}
    (consumer : ContextConsumer indexed)
    (context : Cat.Obj base) →
  AdequateAt consumer context →
  Descent.FibreConstantFor
    (observe indexed context)
    (consume consumer context)
adequacyIsContextLocal consumer context =
  Descent.consumerSufficientIsFibreConstant

record ContextIndexedObservationFibrationBoundary : Set where
  constructor contextIndexedObservationFibrationBoundary
  field
    fineCarrierMayDependOnContext : Bool
    surfaceCarrierMayDependOnContext : Bool
    contextChangeHasTypedRestriction : Bool
    observationMustCommuteWithRestriction : Bool
    splitCartesianFactorizationConstructed : Bool
    adequacyIsConsumerAndContextIndexed : Bool
    localAdequacyImpliesWorldCompleteness : Bool
    arbitraryContextChangesAutomaticallySatisfyFibrationLaws : Bool

canonicalContextIndexedObservationFibrationBoundary :
  ContextIndexedObservationFibrationBoundary
canonicalContextIndexedObservationFibrationBoundary =
  contextIndexedObservationFibrationBoundary
    true true true true true true false false
