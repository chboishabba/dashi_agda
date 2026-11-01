module DASHI.Physics.Closure.NSTriadKNCanonicalG2Round240W2Round250Exact where

------------------------------------------------------------------------
-- ROUND250 / CANONICAL G2 NUMERIC DISSIPATION -> SAME ROUND240 W2
--
-- R245 correctly separates two facts:
--   (1) project the authoritative canonical G2 energy theorem to a numeric
--       integrated-dissipation bound;
--   (2) identify that numeric quantity with the dissipation observable used
--       by the same physical Round240 trajectory.
--
-- This file bundles those two receipts into one exact W2 authority and proves
-- the inequality consumed by R243.  It does not introduce another energy law.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete
import DASHI.Physics.Closure.NSTriadKNCanonicalG2NumericDissipationRound245Exact as R245

record CanonicalG2SamePhysicalW2
    {ℓState ℓProp : Level}
    (S : Concrete.ConcreteGalerkinSetting ℓState ℓProp)
    (G2 : Concrete.G2ExactGalerkinEnergy S)
    (Time : Set)
    (physicalDissipationIntegral : Nat → Time → ℚ)
    : Set (ℓState ⊔ ℓProp) where
  field
    numericProjection :
      R245.CanonicalG2NumericDissipationProjection S G2 Time

    samePhysicalObservable :
      R245.SameTrajectoryDissipationIdentification
        numericProjection physicalDissipationIntegral

open CanonicalG2SamePhysicalW2 public

canonicalG2SamePhysicalIntegratedDissipationBound :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    {G2 : Concrete.G2ExactGalerkinEnergy S}
    {Time : Set}
    {physicalDissipationIntegral : Nat → Time → ℚ} →
  (W2 : CanonicalG2SamePhysicalW2 S G2 Time physicalDissipationIntegral) →
  (N : Nat) (terminal : Time) →
  physicalDissipationIntegral N terminal
  ≤ R245.dissipationBound (numericProjection W2)
canonicalG2SamePhysicalIntegratedDissipationBound W2 =
  R245.identifiedPhysicalDissipationBound (samePhysicalObservable W2)

round250CanonicalG2AuthorityReused : Bool
round250CanonicalG2AuthorityReused = true

round250NumericProjectionAndRound240IdentificationUnified : Bool
round250NumericProjectionAndRound240IdentificationUnified = true

round250W2CompilerClosed : Bool
round250W2CompilerClosed = true

round250ConcreteAnalyticG2NumericProjectionKernelDerivedHere : Bool
round250ConcreteAnalyticG2NumericProjectionKernelDerivedHere = false

round250PackageAClosed : Bool
round250PackageAClosed = false

round250ClayPromotion : Bool
round250ClayPromotion = false

round250W2CompilerClosedIsTrue : round250W2CompilerClosed ≡ true
round250W2CompilerClosedIsTrue = refl

round250ConcreteAnalyticG2NumericProjectionKernelDerivedHereIsFalse :
  round250ConcreteAnalyticG2NumericProjectionKernelDerivedHere ≡ false
round250ConcreteAnalyticG2NumericProjectionKernelDerivedHereIsFalse = refl

round250ClayPromotionIsFalse : round250ClayPromotion ≡ false
round250ClayPromotionIsFalse = refl
