module DASHI.Physics.ThreeBody.Regime where

------------------------------------------------------------------------
-- Regime classifier for the Dashi reading of three-body dynamics.

data ThreeBodyRegime : Set where
  contractiveRegion : ThreeBodyRegime
  coneBoundaryRegion : ThreeBodyRegime
  nonContractingRegion : ThreeBodyRegime

record ThreeBodyRegimeClassifier
  (State : Set)
  : Set₁ where
  field
    classify : State → ThreeBodyRegime
    inContractiveRegion : State → Set
    onConeBoundary : State → Set
    inNonContractingRegion : State → Set

open ThreeBodyRegimeClassifier public
