module DASHI.Cognition.PNF.ContextualDecisionSubspaceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Literature calibration:
-- Valerio Mante, David Sussillo, Krishna V. Shenoy, William T. Newsome,
-- "Context-dependent computation by recurrent dynamics in prefrontal cortex",
-- Nature (2013), DOI 10.1038/nature12742.
--
-- The empirical paper finds that context selection need not be early deletion
-- of irrelevant input: mixed population activity can retain both inputs while
-- recurrent geometry makes only the context-relevant dimension drive choice.
-- The finite theorem below captures only that representation/readout split.
------------------------------------------------------------------------

data Context : Set where
  readSupport readCounter : Context

record MixedInputState : Set where
  constructor mixedInputState
  field
    supportSignal : Bool
    counterSignal : Bool

open MixedInputState public

bothDimensionsRepresented : MixedInputState → Bool × Bool
bothDimensionsRepresented state = true , true

choiceReadout : Context → MixedInputState → Bool
choiceReadout readSupport state = supportSignal state
choiceReadout readCounter state = counterSignal state

baseState : MixedInputState
baseState = mixedInputState true false

counterPerturbedState : MixedInputState
counterPerturbedState = mixedInputState true true

counterInformationReallyDiffers :
  counterSignal baseState ≡ counterSignal counterPerturbedState → ⊥
counterInformationReallyDiffers ()

irrelevantDimensionCanRemainRepresentedButChoiceOrthogonal :
  bothDimensionsRepresented baseState ≡ bothDimensionsRepresented counterPerturbedState
  × choiceReadout readSupport baseState ≡ choiceReadout readSupport counterPerturbedState
  × (counterSignal baseState ≡ counterSignal counterPerturbedState → ⊥)
irrelevantDimensionCanRemainRepresentedButChoiceOrthogonal =
  refl , (refl , counterInformationReallyDiffers)

contextRotationExposesPreviouslyOrthogonalDimension :
  choiceReadout readCounter baseState
  ≡ choiceReadout readCounter counterPerturbedState → ⊥
contextRotationExposesPreviouslyOrthogonalDimension ()

record ContextualDecisionSubspaceBoundary : Set where
  constructor contextualDecisionSubspaceBoundary
  field
    choiceIrrelevanceMeansRepresentationDeletion : Bool
    oneReadoutExhaustsFineState : Bool
    contextCanChangeDecisionProjection : Bool

canonicalContextualDecisionSubspaceBoundary : ContextualDecisionSubspaceBoundary
canonicalContextualDecisionSubspaceBoundary =
  contextualDecisionSubspaceBoundary false false true
