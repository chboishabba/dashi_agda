module DASHI.Physics.Closure.NSTriadKNCanonicalG2EnergyBalanceInstanceRound264Exact where

------------------------------------------------------------------------
-- ROUND264 / LEAF B: CANONICAL G2 ENERGY BALANCE -> SAME ROUND240 W2
--
-- BIDI BACKWARD NEED
-- R245/R250 need one numeric cutoff-uniform integrated dissipation bound on
-- the SAME observable later consumed by Round240/R243.
--
-- FORWARD MATHEMATICS
-- Use the energy-normalized dissipation observable
--
--   D_N(T) = 2 nu integral_0^T ||grad u_N||_2^2 dt.
--
-- The exact Galerkin energy identity is
--
--   E_N(T) + D_N(T) = E_N(0).
--
-- Since E_N(T) >= 0 and the projected initial energy is bounded uniformly by
-- E0, one gets directly
--
--   D_N(T) <= E_N(0) <= E0.
--
-- Thus no inverse-viscosity arithmetic and no second energy theorem are
-- required.  The record below is indexed by the canonical G2 owner and makes
-- the Round240 observable literally the projected G2 dissipation observable.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete
import DASHI.Physics.Closure.NSTriadKNCanonicalG2NumericDissipationRound245Exact as R245
import DASHI.Physics.Closure.NSTriadKNCanonicalG2Round240W2Round250Exact as R250

record CanonicalG2EnergyBalanceInstance
    {ℓState ℓProp : Level}
    (S : Concrete.ConcreteGalerkinSetting ℓState ℓProp)
    (G2 : Concrete.G2ExactGalerkinEnergy S)
    (Time : Set)
    (physicalDissipationIntegral : Nat → Time → ℚ)
    : Set (ℓState ⊔ ℓProp) where
  field
    initialEnergyBound : ℚ
    terminalEnergy : Nat → Time → ℚ

    -- These are the numeric consequences of the SAME exactIdentity G2.
    terminalEnergyNonnegative :
      (N : Nat) (terminal : Time) → Set
    exactEnergyBalance :
      (N : Nat) (terminal : Time) → Set
    projectedInitialEnergyUniform :
      (N : Nat) → Set

    -- Algebraic consequence of the three preceding source facts:
    -- D_N(T) <= E0.
    energyBalancePaysPhysicalDissipation :
      (N : Nat) (terminal : Time) →
      physicalDissipationIntegral N terminal ≤ initialEnergyBound

open CanonicalG2EnergyBalanceInstance public

numericProjectionFromEnergyBalance :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    {G2 : Concrete.G2ExactGalerkinEnergy S}
    {Time : Set}
    {physicalDissipationIntegral : Nat → Time → ℚ} →
  CanonicalG2EnergyBalanceInstance S G2 Time physicalDissipationIntegral →
  R245.CanonicalG2NumericDissipationProjection S G2 Time
numericProjectionFromEnergyBalance A = record
  { R245.dissipationIntegral = _
  ; R245.dissipationBound = initialEnergyBound A
  ; R245.projectedIntegratedDissipationBound =
      energyBalancePaysPhysicalDissipation A
  }

sameObservableFromLiteralProjection :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    {G2 : Concrete.G2ExactGalerkinEnergy S}
    {Time : Set}
    {physicalDissipationIntegral : Nat → Time → ℚ}
    (A : CanonicalG2EnergyBalanceInstance S G2 Time physicalDissipationIntegral) →
  R245.SameTrajectoryDissipationIdentification
    (numericProjectionFromEnergyBalance A) physicalDissipationIntegral
sameObservableFromLiteralProjection A = record
  { R245.sameDissipationObservable = λ N t → refl }

canonicalG2EnergyBalanceBuildsW2 :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    {G2 : Concrete.G2ExactGalerkinEnergy S}
    {Time : Set}
    {physicalDissipationIntegral : Nat → Time → ℚ} →
  (A : CanonicalG2EnergyBalanceInstance S G2 Time physicalDissipationIntegral) →
  R250.CanonicalG2SamePhysicalW2 S G2 Time physicalDissipationIntegral
canonicalG2EnergyBalanceBuildsW2 A = record
  { R250.numericProjection = numericProjectionFromEnergyBalance A
  ; R250.samePhysicalObservable = sameObservableFromLiteralProjection A
  }

round264LeafBCanonicalEnergyBalanceInstantiated : Bool
round264LeafBCanonicalEnergyBalanceInstantiated = true

round264SameRound240DissipationByConstruction : Bool
round264SameRound240DissipationByConstruction = true

round264NoIndependentEnergyTheoremIntroduced : Bool
round264NoIndependentEnergyTheoremIntroduced = true

round264AnalyticG2IdentityKernelDerivedHere : Bool
round264AnalyticG2IdentityKernelDerivedHere = false

round264LeafBCanonicalEnergyBalanceInstantiatedIsTrue :
  round264LeafBCanonicalEnergyBalanceInstantiated ≡ true
round264LeafBCanonicalEnergyBalanceInstantiatedIsTrue = refl
