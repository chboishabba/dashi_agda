module DASHI.Cognition.CognitiveProjectionCategory where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.ProjectionCategory as PC

------------------------------------------------------------------------
-- Objects are the layers used throughout the cognition formalism.
------------------------------------------------------------------------

data CognitiveLayer : Set where
  physicalLayer       : CognitiveLayer
  configurationLayer  : CognitiveLayer
  derivationLayer     : CognitiveLayer
  classLayer          : CognitiveLayer
  observableLayer     : CognitiveLayer
  visualGeneratorLayer : CognitiveLayer

------------------------------------------------------------------------
-- Generating morphisms.  Paths below form the free category on this graph,
-- so category laws are proved rather than stored as unchecked booleans.
------------------------------------------------------------------------

data CognitiveEdge : CognitiveLayer → CognitiveLayer → Set where
  physicalEvolutionEdge : CognitiveEdge physicalLayer physicalLayer
  physicalRealisationEdge : CognitiveEdge physicalLayer configurationLayer
  admissibleTransitionEdge : CognitiveEdge configurationLayer configurationLayer
  derivationReadoutEdge : CognitiveEdge configurationLayer derivationLayer
  classQuotientEdge : CognitiveEdge derivationLayer classLayer
  coarseGrainEdge : CognitiveEdge classLayer classLayer
  involutionEdge : CognitiveEdge classLayer classLayer
  observationEdge : CognitiveEdge classLayer observableLayer
  visualGeneratorEdge : CognitiveEdge configurationLayer visualGeneratorLayer
  visualDeformationEdge : CognitiveEdge visualGeneratorLayer visualGeneratorLayer
  visualReportEdge : CognitiveEdge visualGeneratorLayer observableLayer

data CognitivePath : CognitiveLayer → CognitiveLayer → Set where
  idPath : ∀ {A} → CognitivePath A A
  _▻_ : ∀ {A B C} →
    CognitivePath A B → CognitiveEdge B C → CognitivePath A C

infixl 7 _▻_
infixr 6 _∘p_

_∘p_ : ∀ {A B C} →
  CognitivePath B C → CognitivePath A B → CognitivePath A C
idPath ∘p f = f
(g ▻ edge) ∘p f = (g ∘p f) ▻ edge

id-left : ∀ {A B} (f : CognitivePath A B) → idPath ∘p f ≡ f
id-left f = refl

id-right : ∀ {A B} (f : CognitivePath A B) → f ∘p idPath ≡ f
id-right idPath = refl
id-right (f ▻ edge) = cong (λ path → path ▻ edge) (id-right f)

assoc :
  ∀ {A B C D}
  (f : CognitivePath C D)
  (g : CognitivePath B C)
  (h : CognitivePath A B) →
  (f ∘p g) ∘p h ≡ f ∘p (g ∘p h)
assoc idPath g h = refl
assoc (f ▻ edge) g h =
  cong (λ path → path ▻ edge) (assoc f g h)

cognitiveProjectionCategory : PC.ProjectionCategory
cognitiveProjectionCategory = record
  { Obj = CognitiveLayer
  ; Hom = CognitivePath
  ; id = idPath
  ; _∘_ = _∘p_
  ; id-left = id-left
  ; id-right = id-right
  ; assoc = assoc
  ; categoryReading =
      "Free DASHI cognition category: physical evolution, guarded derivation, class quotient, coarse-graining, observation, and visual-generator deformation."
  }

physicalToObservation : CognitivePath physicalLayer observableLayer
physicalToObservation =
  idPath
  ▻ physicalRealisationEdge
  ▻ derivationReadoutEdge
  ▻ classQuotientEdge
  ▻ observationEdge

visualToObservation : CognitivePath configurationLayer observableLayer
visualToObservation =
  idPath
  ▻ visualGeneratorEdge
  ▻ visualDeformationEdge
  ▻ visualReportEdge
