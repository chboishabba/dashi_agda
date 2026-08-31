module DASHI.Physics.Closure.NSTriadKNPhysicalSignedGramFamilyRound375Exact where

------------------------------------------------------------------------
-- ROUND375 / BIDI: MAKE R353'S COMPANION AND INTEGRAL LITERALLY PHYSICAL
--
-- R353 is generic in its cutoff/time functions.  R354 later needs explicit
-- same-object receipts identifying those generic functions with the R228/R240
-- physical companion and integration operator.
--
-- This owner removes that representation seam by constructing R353 directly
-- with
--
--   companionMass N t = R228 physical companion mass,
--   integrateTo f N T = physical integrateTo (f N) T.
--
-- Hence the R354 companion-integral identity is definitional (`refl`).  The
-- only remaining mixed->companion transport is pointwise finite ordered
-- algebra, integrated by the independently supplied physical monotonicity law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxFamilyToR293Round353Exact as R353
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalSignedGramFamily
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Base = R228.PhysicalTimeIntegral Time integrateTo
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  physicalCompanion :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  physicalCompanion T = Base.companionMass (Dyn.forgetDynamics T)

  physicalFamilyIntegral :
    (Nat → Time → ℚ) → Nat → Time → ℚ
  physicalFamilyIntegral f N terminal = integrateTo (f N) terminal

  record PhysicalSignedGramInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      energyDissipation : Nat → Time → ℚ
      gramDebt : Nat → Time → ℚ

      integrationMonotone :
        (left right : Time → ℚ) →
        ((t : Time) → left t ≤ right t) →
        (terminal : Time) →
        integrateTo left terminal ≤ integrateTo right terminal

      integrationAdditive :
        (left right : Time → ℚ) →
        (terminal : Time) →
        integrateTo (λ time → left time + right time) terminal
        ≡ integrateTo left terminal + integrateTo right terminal

      pointwiseCompanionLedger :
        (N : Nat) (t : Time) →
        physicalCompanion T N t
        ≤ R353.R293.thirtySix * energyDissipation N t + gramDebt N t

      scaledEnergyIntegralUpperBound : Time → ℚ
      integratedScaledEnergyBound :
        (N : Nat) (terminal : Time) →
        integrateTo
          (λ time → R353.R293.thirtySix * energyDissipation N time)
          terminal
        ≤ scaledEnergyIntegralUpperBound terminal

      gramFluxPayment : Nat → Time → R303.SignedGramFluxPayment

      gramFluxIsSameIntegratedDebt :
        (N : Nat) (terminal : Time) →
        R303.signedGramIntegral (gramFluxPayment N terminal)
        ≡ integrateTo (gramDebt N) terminal

      signedGramIntegralUpperBound : Time → ℚ

      gramFluxPaidUniformlyInCutoff :
        (N : Nat) (terminal : Time) →
        R303.signedGramUpperBound (gramFluxPayment N terminal)
        ≤ signedGramIntegralUpperBound terminal

      pointwiseMixedBelowCompanion :
        (N : Nat) (t : Time) →
        Dyn.mixedHelicityMass T N t ≤ physicalCompanion T N t

  open PhysicalSignedGramInputs public

  asR353Family :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    PhysicalSignedGramInputs T →
    R353.SignedGramFluxFamilyInputs Nat Time
  asR353Family T I = record
    { R353.companionMass = physicalCompanion T
    ; R353.energyDissipation = energyDissipation I
    ; R353.gramDebt = gramDebt I
    ; R353.integrateTo = physicalFamilyIntegral
    ; R353.integrationMonotone = λ left right pointwise N terminal →
        integrationMonotone I (left N) (right N)
          (λ t → pointwise N t) terminal
    ; R353.integrationAdditive = λ left right N terminal →
        integrationAdditive I (left N) (right N) terminal
    ; R353.pointwiseCompanionLedger = pointwiseCompanionLedger I
    ; R353.scaledEnergyIntegralUpperBound = scaledEnergyIntegralUpperBound I
    ; R353.integratedScaledEnergyBound = integratedScaledEnergyBound I
    ; R353.gramFluxPayment = gramFluxPayment I
    ; R353.gramFluxIsSameIntegratedDebt = gramFluxIsSameIntegratedDebt I
    ; R353.signedGramIntegralUpperBound = signedGramIntegralUpperBound I
    ; R353.gramFluxPaidUniformlyInCutoff = gramFluxPaidUniformlyInCutoff I
    }

  mixedIntegralBelowCompanion :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (I : PhysicalSignedGramInputs T) →
    (N : Nat) (terminal : Time) →
    integrateTo (Dyn.mixedHelicityMass T N) terminal
    ≤ integrateTo (physicalCompanion T N) terminal
  mixedIntegralBelowCompanion T I N terminal =
    integrationMonotone I
      (Dyn.mixedHelicityMass T N)
      (physicalCompanion T N)
      (pointwiseMixedBelowCompanion I N)
      terminal

  asR354Inputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (I : PhysicalSignedGramInputs T) →
    Weld.R293PhysicalPackageAInputs T
  asR354Inputs T I = record
    { Weld.signedPayment = R353.signedGramFluxFamilyToR293 (asR353Family T I)
    ; Weld.mixedIntegralBelowCompanionIntegral =
        mixedIntegralBelowCompanion T I
    ; Weld.physicalCompanionIsR293CompanionIntegral = λ N terminal → refl
    }

  physicalSignedGramInputsBuildPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    PhysicalSignedGramInputs T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  physicalSignedGramInputsBuildPackageA T I =
    Weld.r293BuildsPhysicalPackageA T (asR354Inputs T I)

round375R353CompanionIsDefinitionallyPhysical : Bool
round375R353CompanionIsDefinitionallyPhysical = true

round375R353IntegrationIsDefinitionallyPhysical : Bool
round375R353IntegrationIsDefinitionallyPhysical = true

round375R354CompanionIntegralEqualityIsRefl : Bool
round375R354CompanionIntegralEqualityIsRefl = true

round375IndependentIntegratedMixedDominanceInputRemoved : Bool
round375IndependentIntegratedMixedDominanceInputRemoved = true

round375PhysicalSignedGramFamilyBuildsLiteralR240PackageA : Bool
round375PhysicalSignedGramFamilyBuildsLiteralR240PackageA = true

round375R354CompanionIntegralEqualityIsReflIsTrue :
  round375R354CompanionIntegralEqualityIsRefl ≡ true
round375R354CompanionIntegralEqualityIsReflIsTrue = refl
