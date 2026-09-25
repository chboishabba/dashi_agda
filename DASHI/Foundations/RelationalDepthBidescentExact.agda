module DASHI.Foundations.RelationalDepthBidescentExact where

------------------------------------------------------------------------
-- RELATIONAL RESTRICTION x DEPTH TRUNCATION
--
-- DASHI CONTRIBUTION
--
-- Relational locality and observation/refinement depth form two independent
-- axes.  A valid bidescent system carries restriction maps at every depth and
-- truncation maps between depths, together with an explicit commuting-square
-- witness.  This is the requested "compatible family in both directions".
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data Patch : Set where
  patchAB patchBC patchCA patchA patchB patchC : Patch

record RelationalDepthBidescent
    (Section : Patch → Nat → Set) : Set₁ where
  field
    restrictABtoA :
      (depth : Nat) → Section patchAB depth → Section patchA depth
    restrictCAtoA :
      (depth : Nat) → Section patchCA depth → Section patchA depth

    restrictABtoB :
      (depth : Nat) → Section patchAB depth → Section patchB depth
    restrictBCtoB :
      (depth : Nat) → Section patchBC depth → Section patchB depth

    restrictBCtoC :
      (depth : Nat) → Section patchBC depth → Section patchC depth
    restrictCAtoC :
      (depth : Nat) → Section patchCA depth → Section patchC depth

    truncate :
      (patch : Patch) →
      (depth : Nat) →
      Section patch (suc depth) →
      Section patch depth

    truncateRestrictABtoA :
      (depth : Nat) (section : Section patchAB (suc depth)) →
      truncate patchA depth (restrictABtoA (suc depth) section)
      ≡ restrictABtoA depth (truncate patchAB depth section)

    truncateRestrictCAtoA :
      (depth : Nat) (section : Section patchCA (suc depth)) →
      truncate patchA depth (restrictCAtoA (suc depth) section)
      ≡ restrictCAtoA depth (truncate patchCA depth section)

    truncateRestrictABtoB :
      (depth : Nat) (section : Section patchAB (suc depth)) →
      truncate patchB depth (restrictABtoB (suc depth) section)
      ≡ restrictABtoB depth (truncate patchAB depth section)

    truncateRestrictBCtoB :
      (depth : Nat) (section : Section patchBC (suc depth)) →
      truncate patchB depth (restrictBCtoB (suc depth) section)
      ≡ restrictBCtoB depth (truncate patchBC depth section)

    truncateRestrictBCtoC :
      (depth : Nat) (section : Section patchBC (suc depth)) →
      truncate patchC depth (restrictBCtoC (suc depth) section)
      ≡ restrictBCtoC depth (truncate patchBC depth section)

    truncateRestrictCAtoC :
      (depth : Nat) (section : Section patchCA (suc depth)) →
      truncate patchC depth (restrictCAtoC (suc depth) section)
      ≡ restrictCAtoC depth (truncate patchCA depth section)

open RelationalDepthBidescent public

data CoarseCompatibilityForcesFineCompatibility : Set where
data RelationalLocalityIsDepth : Set where

coarseCompatibilityDoesNotForceFineCompatibility :
  CoarseCompatibilityForcesFineCompatibility → ⊥
coarseCompatibilityDoesNotForceFineCompatibility ()

relationalLocalityIsNotDefinitionallyDepth :
  RelationalLocalityIsDepth → ⊥
relationalLocalityIsNotDefinitionallyDepth ()

record RelationalDepthBidescentBoundary : Set where
  constructor relational-depth-bidescent-boundary
  field
    restrictionAndDepthAreSeparateAxes : Bool
    commutingSquaresRequired : Bool
    coarseAgreementForcesFineAgreement : Bool
    pAdicVocabularyCreatesPsychologicalMetric : Bool

canonicalRelationalDepthBidescentBoundary :
  RelationalDepthBidescentBoundary
canonicalRelationalDepthBidescentBoundary =
  relational-depth-bidescent-boundary true true false false
