module Ontology.Hecke.DirectedCorrelationMDLPromotion where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)

open import MDL.Core using (CodeLength)
open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using (CurrentSaturatedGenerator)

------------------------------------------------------------------------
-- MDL-governed refinement promotion.
--
-- A richer invariant is not promoted merely because it can be computed.  It
-- must discharge a separation obligation and pay for its additional model
-- description.  This is the Hecke-side specialization of the wider
-- ZKP/DASHI rule that proposal generation is softer than promotion.

data RefinementLevel : Set where
  flatHistogram        : RefinementLevel
  triadHistogram       : RefinementLevel
  symmetricCorrelation : RefinementLevel
  directedCorrelation  : RefinementLevel

------------------------------------------------------------------------
-- The admissible refinement ladder.  There is deliberately no arbitrary jump
-- or reverse edge: each promotion must explain why the immediately cheaper
-- summary was insufficient.

data NextRefinement : RefinementLevel → RefinementLevel → Set where
  flat→triad       : NextRefinement flatHistogram triadHistogram
  triad→symmetric  : NextRefinement triadHistogram symmetricCorrelation
  symmetric→directed :
    NextRefinement symmetricCorrelation directedCorrelation

------------------------------------------------------------------------
-- Cumulative structural description costs for the current finite carrier.
-- These are bookkeeping costs, not empirical claims about optimal coding.

modelCost : RefinementLevel → CodeLength
modelCost flatHistogram        = 3
modelCost triadHistogram       = 9
modelCost symmetricCorrelation = 12
modelCost directedCorrelation  = 39

record RefinementScore (level : RefinementLevel) : Set where
  constructor refinementScore
  field
    residualCost : CodeLength

  totalCost : CodeLength
  totalCost = modelCost level + residualCost

open RefinementScore public

------------------------------------------------------------------------
-- A separation witness is pair-specific.  The actual inequality proof lives
-- in the corresponding computation module; this record only governs when it
-- is allowed to promote the resulting invariant.

record PairSeparationWitness (level : RefinementLevel) : Set₁ where
  field
    left       : CurrentSaturatedGenerator
    right      : CurrentSaturatedGenerator
    separated  : Set

open PairSeparationWitness public

record PromotionReceipt
  (from to : RefinementLevel)
  (fromScore : RefinementScore from)
  (toScore : RefinementScore to)
  : Set₁ where
  field
    next               : NextRefinement from to
    sourceExhausted    : Set
    targetSeparates    : PairSeparationWitness to
    mdlNonWorse        : totalCost toScore ≤ totalCost fromScore

open PromotionReceipt public

------------------------------------------------------------------------
-- The speedrun decision surface.
--
-- Either directed correlation earns promotion by separating a current pair
-- without increasing total MDL, or it remains an unpromoted diagnostic.  No
-- Monster or physics authority follows from inhabiting this record alone.

DirectedPromotionTarget : Set₁
DirectedPromotionTarget =
  ∀ (symmetricScore : RefinementScore symmetricCorrelation)
    (directedScore : RefinementScore directedCorrelation) →
  PromotionReceipt
    symmetricCorrelation
    directedCorrelation
    symmetricScore
    directedScore
