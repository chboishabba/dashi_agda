module DASHI.Core.CompiledInversePlusOneCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set; Set₁)

------------------------------------------------------------------------
-- Exact logical core of the DASHI chart / residual / +1 account.
--
-- A compiled inverse is a chart-local adapter.  It is not assumed globally
-- invertible.  A residual witness records whether the current world still
-- glues to that adapter.  A failed chart produces a typed carry request for a
-- successor chart; the +1 seed is a local handle, not a cure or factorisation.

record CompiledInverseSystem : Set₁ where
  field
    World : Set
    Chart : Set
    Identity : Chart → Set
    Residual : World → Chart → Set
    PlusOneSeed : World → Chart → Set
    SuccessorChart : Chart → Set

    chartGlues : World → (j : Chart) → Set
    chartFails : World → (j : Chart) → Set

    gluingProducesIdentity :
      (w : World) →
      (j : Chart) →
      chartGlues w j →
      Identity j

    failureProducesResidual :
      (w : World) →
      (j : Chart) →
      chartFails w j →
      Residual w j

    residualProducesPlusOne :
      (w : World) →
      (j : Chart) →
      Residual w j →
      PlusOneSeed w j

    plusOneProducesSuccessorRequest :
      (w : World) →
      (j : Chart) →
      PlusOneSeed w j →
      SuccessorChart j

open CompiledInverseSystem public

failureRequiresSuccessorChart :
  (S : CompiledInverseSystem) →
  (w : World S) →
  (j : Chart S) →
  chartFails S w j →
  SuccessorChart S j
failureRequiresSuccessorChart S w j fails =
  plusOneProducesSuccessorRequest S w j
    (residualProducesPlusOne S w j
      (failureProducesResidual S w j fails))

record PlusOneGovernance : Set where
  constructor mkPlusOneGovernance
  field
    curePromotion : Bool
    curePromotionIsFalse : curePromotion ≡ false

    diagnosisPromotion : Bool
    diagnosisPromotionIsFalse : diagnosisPromotion ≡ false

    forcedDisclosurePromotion : Bool
    forcedDisclosurePromotionIsFalse : forcedDisclosurePromotion ≡ false

    fullFactorisationPromotion : Bool
    fullFactorisationPromotionIsFalse : fullFactorisationPromotion ≡ false

open PlusOneGovernance public

canonicalPlusOneGovernance : PlusOneGovernance
canonicalPlusOneGovernance =
  mkPlusOneGovernance
    false refl
    false refl
    false refl
    false refl
