module DASHI.Physics.Closure.NSTriadKNPositiveRateLaplaceAuthorityRound490Exact where

------------------------------------------------------------------------
-- ROUND490 / STANDARD POSITIVE-RATE LAPLACE AUTHORITY
--
-- The R299/R440 heat factorization needs the standard identity
--
--   1 / (x + y) = ∫ exp(-s x) exp(-s y) ds,     x,y > 0,
--
-- but that theorem is not Navier--Stokes-specific.  This module therefore
-- isolates it as a typed analysis authority instead of making the Clay proof
-- search re-prove real exponential integration.
--
-- IMPORTANT: declaring the authority interface does NOT inhabit it.  The
-- physical lane must still supply an actual authority object and a same-object
-- weld identifying its reciprocal with the literal Cauchy kernel used by the
-- R440/R299 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _<_; _+_)

------------------------------------------------------------------------
-- Generic scalar authority.
------------------------------------------------------------------------

record PositiveRateLaplaceAuthority : Set₁ where
  field
    HeatParameter : Set
    heatWeight : ℚ → HeatParameter → ℚ
    Integral : (HeatParameter → ℚ) → ℚ
    reciprocal : ℚ → ℚ → ℚ

    laplaceResolventIdentity :
      (x y : ℚ) →
      0 < x → 0 < y →
      reciprocal x y
      ≡ Integral (λ s → heatWeight x s * heatWeight y s)

open PositiveRateLaplaceAuthority public

------------------------------------------------------------------------
-- Same-object realization packet.
--
-- The caller supplies the literal pair kernel it wants to realize.  This keeps
-- standard analysis authority separate from the representation theorem saying
-- that the authority's reciprocal is exactly that repository object.
------------------------------------------------------------------------

record PositiveRateKernelLaplaceRealization
    (kernel : ℚ → ℚ → ℚ) : Set₁ where
  field
    authority : PositiveRateLaplaceAuthority
    reciprocalIsKernel :
      (x y : ℚ) →
      0 < x → 0 < y →
      reciprocal authority x y ≡ kernel x y

open PositiveRateKernelLaplaceRealization public

kernelLaplaceIdentity :
  ∀ {kernel} →
  (R : PositiveRateKernelLaplaceRealization kernel) →
  (x y : ℚ) →
  (xPositive : 0 < x) →
  (yPositive : 0 < y) →
  kernel x y
  ≡ Integral (authority R)
      (λ s → heatWeight (authority R) x s * heatWeight (authority R) y s)
kernelLaplaceIdentity R x y xPositive yPositive =
  let
    A = authority R
    standard = laplaceResolventIdentity A x y xPositive yPositive
    sameObject = reciprocalIsKernel R x y xPositive yPositive
  in
  trans (sym sameObject) standard
  where
  open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Trust / proof-search boundary.
------------------------------------------------------------------------

round490StandardLaplaceTheoremIsAuthorityLayer : Bool
round490StandardLaplaceTheoremIsAuthorityLayer = true

round490AuthorityInterfaceCreatesAuthorityInhabitant : Bool
round490AuthorityInterfaceCreatesAuthorityInhabitant = false

round490SameObjectKernelWeldRequired : Bool
round490SameObjectKernelWeldRequired = true

round490PhysicalSignedSpacetimeEstimatePaid : Bool
round490PhysicalSignedSpacetimeEstimatePaid = false

round490R423SignedCompanionBudgetClosed : Bool
round490R423SignedCompanionBudgetClosed = false

round490ClayPromotion : Bool
round490ClayPromotion = false

round490StandardLaplaceTheoremIsAuthorityLayerIsTrue :
  round490StandardLaplaceTheoremIsAuthorityLayer ≡ true
round490StandardLaplaceTheoremIsAuthorityLayerIsTrue = refl

round490AuthorityInterfaceCreatesAuthorityInhabitantIsFalse :
  round490AuthorityInterfaceCreatesAuthorityInhabitant ≡ false
round490AuthorityInterfaceCreatesAuthorityInhabitantIsFalse = refl

round490ClayPromotionIsFalse : round490ClayPromotion ≡ false
round490ClayPromotionIsFalse = refl
