module DASHI.Physics.Closure.NSTriadKNCanonicalG2NumericDissipationRound245Exact where

------------------------------------------------------------------------
-- ROUND245 / NUMERIC DISSIPATION PROJECTION FROM CANONICAL G2 ENERGY
--
-- Backward need from Round243/W2:
--
--   dissipationIntegral cutoff terminal <= dissipationBound.
--
-- Forward authoritative producer:
--
--   NSConcreteAubinLionsNonlinearLimitWitnesses.G2ExactGalerkinEnergy
--
-- already owns both the exact Galerkin energy identity and the fact that the
-- energy estimate is uniform in cutoff.  The canonical analytic interface,
-- however, intentionally packages `UniformEnergyEstimate` as an opaque
-- proposition.  It therefore cannot be silently coerced into the numeric
-- rational inequality consumed by Round243.
--
-- This file installs the smallest correct bridge: a NUMERIC PROJECTION indexed
-- by the actual canonical G2 witness.  It is not a second energy theorem.  A
-- producer must explicitly project the concrete analytic energy identity to
-- the numeric integrated-dissipation quantity used by the mixed-helicity
-- consumer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete

record CanonicalG2NumericDissipationProjection
    {ℓState ℓProp : Level}
    (S : Concrete.ConcreteGalerkinSetting ℓState ℓProp)
    (G2 : Concrete.G2ExactGalerkinEnergy S)
    (Time : Set)
    : Set (ℓState ⊔ ℓProp) where
  field
    dissipationIntegral : Nat → Time → ℚ
    dissipationBound : ℚ

    -- This field is the numeric projection of the SAME G2 energy theorem.
    -- It must be constructed from `exactIdentity G2` / `uniformEnergyEstimate G2`
    -- in a concrete analytic realization; callers cannot replace G2 itself.
    projectedIntegratedDissipationBound :
      (cutoff : Nat) (terminal : Time) →
      dissipationIntegral cutoff terminal ≤ dissipationBound

open CanonicalG2NumericDissipationProjection public

g2ProjectionSuppliesRound243W2Shape :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    {G2 : Concrete.G2ExactGalerkinEnergy S}
    {Time : Set} →
  (P : CanonicalG2NumericDissipationProjection S G2 Time) →
  (cutoff : Nat) (terminal : Time) →
  dissipationIntegral P cutoff terminal ≤ dissipationBound P
g2ProjectionSuppliesRound243W2Shape P =
  projectedIntegratedDissipationBound P

------------------------------------------------------------------------
-- Same-object trajectory binding boundary.
--
-- Canonical G2 is stated on `Concrete.galerkinPath`; Round240 is stated on the
-- literal Fourier `PhysicalNSGalerkinTrajectory`.  Before W2 can be marked
-- physically installed, the numeric projection above must also be identified
-- with the dissipation observable of that SAME Round240 trajectory.  This file
-- records that dependency instead of pretending the two representations are
-- definitionally identical.
------------------------------------------------------------------------

record SameTrajectoryDissipationIdentification
    {ℓState ℓProp : Level}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    {G2 : Concrete.G2ExactGalerkinEnergy S}
    {Time : Set}
    (P : CanonicalG2NumericDissipationProjection S G2 Time)
    (physicalDissipationIntegral : Nat → Time → ℚ)
    : Set where
  field
    sameDissipationObservable :
      (cutoff : Nat) (terminal : Time) →
      physicalDissipationIntegral cutoff terminal
      ≡ dissipationIntegral P cutoff terminal

open SameTrajectoryDissipationIdentification public

identifiedPhysicalDissipationBound :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    {G2 : Concrete.G2ExactGalerkinEnergy S}
    {Time : Set}
    {P : CanonicalG2NumericDissipationProjection S G2 Time}
    {physicalDissipationIntegral : Nat → Time → ℚ} →
  (I : SameTrajectoryDissipationIdentification P physicalDissipationIntegral) →
  (cutoff : Nat) (terminal : Time) →
  physicalDissipationIntegral cutoff terminal ≤ dissipationBound P
identifiedPhysicalDissipationBound {P = P} I cutoff terminal
  rewrite sameDissipationObservable I cutoff terminal =
  projectedIntegratedDissipationBound P cutoff terminal

round245CanonicalG2IsAuthoritativeEnergyOwner : Bool
round245CanonicalG2IsAuthoritativeEnergyOwner = true

round245NumericProjectionShapeClosed : Bool
round245NumericProjectionShapeClosed = true

round245CanonicalG2ConcreteNumericProjectionInstalled : Bool
round245CanonicalG2ConcreteNumericProjectionInstalled = false

round245Round240SameDissipationObservableIdentified : Bool
round245Round240SameDissipationObservableIdentified = false

round245W2PhysicallyInstalled : Bool
round245W2PhysicallyInstalled = false

round245PackageAClosed : Bool
round245PackageAClosed = false

round245ClayPromotion : Bool
round245ClayPromotion = false

round245NumericProjectionShapeClosedIsTrue :
  round245NumericProjectionShapeClosed ≡ true
round245NumericProjectionShapeClosedIsTrue = refl

round245CanonicalG2ConcreteNumericProjectionInstalledIsFalse :
  round245CanonicalG2ConcreteNumericProjectionInstalled ≡ false
round245CanonicalG2ConcreteNumericProjectionInstalledIsFalse = refl

round245W2PhysicallyInstalledIsFalse :
  round245W2PhysicallyInstalled ≡ false
round245W2PhysicallyInstalledIsFalse = refl

round245ClayPromotionIsFalse : round245ClayPromotion ≡ false
round245ClayPromotionIsFalse = refl
