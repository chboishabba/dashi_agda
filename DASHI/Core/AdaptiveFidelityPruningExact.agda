module DASHI.Core.AdaptiveFidelityPruningExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- A cheap model may prune an expensive candidate only when its certified lower
-- bound is already worse than the incumbent.  The theorem is order-generic and
-- does not depend on floating-point arithmetic, Gaussian error assumptions, or
-- a particular surrogate family.
--
-- REFERENCE / MOTIVATION
--
-- Natalia M. Alexandrov, J. E. Dennis Jr., Robert M. Lewis, Virginia Torczon,
-- "A trust-region framework for managing the use of approximation models in
-- optimization", Structural Optimization 15 (1998), 16-23.
-- DOI: 10.1007/BF01197433.
--
-- The source motivates local high/low-fidelity model management.  The exact
-- pruning theorem below is a DASHI construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

record OrderedScore (Score : Set) : Set₁ where
  field
    _≤s_ _<s_ : Score → Score → Set
    <-trans : ∀ {a b c} → a <s b → b <s c → a <s c
    <-≤-trans : ∀ {a b c} → a <s b → b ≤s c → a <s c
    <-irrefl : ∀ value → ¬ (value <s value)

open OrderedScore public

record CertifiedLowerBound
    {Score : Set}
    (order : OrderedScore Score)
    (actual lower : Score) : Set where
  constructor certifiedLowerBound
  field
    lowerIsValid : _≤s_ order lower actual

open CertifiedLowerBound public

record SafeMinimisationPrune
    {Score : Set}
    (order : OrderedScore Score)
    (incumbent actual lower : Score) : Set where
  constructor safeMinimisationPrune
  field
    certified : CertifiedLowerBound order actual lower
    incumbentStrictlyBelowLower : _<s_ order incumbent lower

open SafeMinimisationPrune public

safePruneRefutesImprovement :
  ∀ {Score}
    (order : OrderedScore Score)
    {incumbent actual lower : Score} →
  SafeMinimisationPrune order incumbent actual lower →
  _<s_ order actual incumbent →
  ⊥
safePruneRefutesImprovement order prune actualImproves =
  <-irrefl order actual
    (<-≤-trans order
      (<-trans order
        actualImproves
        (incumbentStrictlyBelowLower prune))
      (lowerIsValid (certified prune)))

------------------------------------------------------------------------
-- Adaptive materialisation is therefore justified exactly at the uncertainty
-- boundary: if a safe-prune proof is unavailable, the theorem does not permit
-- pruning.  A runtime may then materialise the high-fidelity candidate.
------------------------------------------------------------------------

data FidelityDecision : Set where
  prune materialise : FidelityDecision

record FidelityAllocationBoundary : Set where
  constructor fidelityAllocationBoundary
  field
    cheapPredictionAloneDoesNotJustifyPruning : Bool
    certifiedBoundCanJustifyPruning : Bool
    unavailablePruneCertificateLeavesMaterialisationOpen : Bool
    fidelityChoiceIsSeparateFromAuthorityPromotion : Bool

canonicalFidelityAllocationBoundary : FidelityAllocationBoundary
canonicalFidelityAllocationBoundary =
  fidelityAllocationBoundary true true true true
