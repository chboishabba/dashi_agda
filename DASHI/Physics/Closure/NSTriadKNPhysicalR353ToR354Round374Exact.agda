module DASHI.Physics.Closure.NSTriadKNPhysicalR353ToR354Round374Exact where

------------------------------------------------------------------------
-- ROUND374 / BIDI: SPECIALIZE R353 TO THE PHYSICAL R354 OBSERVABLES
--
-- R354 asks for two endpoint-level transports:
--
--   integral mixed <= integral physical companion,
--   integral physical companion = R293 companion integral.
--
-- A physical R353 family already owns integration monotonicity. Therefore the
-- first endpoint inequality should not be an independent analytic theorem. It
-- follows from a pointwise mixed<=R353-companion theorem plus endpoint receipts
-- identifying R353 integration with the independently owned physical integral.
--
-- Function extensionality is deliberately NOT assumed: the integration model
-- is opaque authority, so same-integration facts are stated exactly at the
-- endpoints consumed downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxFamilyToR293Round353Exact as R353
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalR353ToR354
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Base = R228.PhysicalTimeIntegral Time integrateTo
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  record PhysicalR353Family
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      family : R353.SignedGramFluxFamilyInputs Nat Time

      -- Physical mixed mass is pointwise below the exact companion observable
      -- consumed by this R353 family.
      pointwiseMixedBelowFamilyCompanion :
        (N : Nat) (t : Time) →
        Dyn.mixedHelicityMass T N t
        ≤ R353.companionMass family N t

      -- Same integration authority, stated only at the two endpoint integrals
      -- actually needed by R354. No function extensionality is assumed.
      physicalMixedIsFamilyMixedIntegral :
        (N : Nat) (terminal : Time) →
        integrateTo (Dyn.mixedHelicityMass T N) terminal
        ≡ R353.integrateTo family
            (λ cutoff time → Dyn.mixedHelicityMass T cutoff time)
            N terminal

      physicalCompanionIsFamilyCompanionIntegral :
        (N : Nat) (terminal : Time) →
        integrateTo
          (Base.companionMass (Dyn.forgetDynamics T) N)
          terminal
        ≡ R353.integrateTo family
            (R353.companionMass family)
            N terminal

  open PhysicalR353Family public

  mixedIntegralBelowPhysicalCompanion :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (P : PhysicalR353Family T) →
    (N : Nat) (terminal : Time) →
    integrateTo (Dyn.mixedHelicityMass T N) terminal
    ≤ integrateTo
        (Base.companionMass (Dyn.forgetDynamics T) N)
        terminal
  mixedIntegralBelowPhysicalCompanion T P N terminal =
    let
      F = family P
      mixed : Nat → Time → ℚ
      mixed cutoff time = Dyn.mixedHelicityMass T cutoff time

      familyIntegrated :
        R353.integrateTo F mixed N terminal
        ≤ R353.integrateTo F (R353.companionMass F) N terminal
      familyIntegrated =
        R353.integrationMonotone F mixed (R353.companionMass F)
          (pointwiseMixedBelowFamilyCompanion P) N terminal
    in
    subst
      (λ left →
        left ≤ integrateTo
          (Base.companionMass (Dyn.forgetDynamics T) N) terminal)
      (sym (physicalMixedIsFamilyMixedIntegral P N terminal))
      (subst
        (λ right →
          R353.integrateTo F mixed N terminal ≤ right)
        (sym (physicalCompanionIsFamilyCompanionIntegral P N terminal))
        familyIntegrated)

  physicalR353BuildsR354Inputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (P : PhysicalR353Family T) →
    Weld.R293PhysicalPackageAInputs T
  physicalR353BuildsR354Inputs T P = record
    { Weld.signedPayment =
        R353.signedGramFluxFamilyToR293 (family P)
    ; Weld.mixedIntegralBelowCompanionIntegral =
        mixedIntegralBelowPhysicalCompanion T P
    ; Weld.physicalCompanionIsR293CompanionIntegral =
        physicalCompanionIsFamilyCompanionIntegral P
    }

  physicalR353BuildsPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    PhysicalR353Family T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  physicalR353BuildsPackageA T P =
    Weld.r293BuildsPhysicalPackageA T
      (physicalR353BuildsR354Inputs T P)

round374R353IntegrationMonotonicityIsCorrectTransportOwner : Bool
round374R353IntegrationMonotonicityIsCorrectTransportOwner = true

round374IntegratedMixedDominanceIndependentInputRequired : Bool
round374IntegratedMixedDominanceIndependentInputRequired = false

round374FunctionExtensionalityAssumed : Bool
round374FunctionExtensionalityAssumed = false

round374PhysicalR353FamilyDirectlyBuildsPackageA : Bool
round374PhysicalR353FamilyDirectlyBuildsPackageA = true

round374IntegratedMixedDominanceIndependentInputRequiredIsFalse :
  round374IntegratedMixedDominanceIndependentInputRequired ≡ false
round374IntegratedMixedDominanceIndependentInputRequiredIsFalse = refl

round374FunctionExtensionalityAssumedIsFalse :
  round374FunctionExtensionalityAssumed ≡ false
round374FunctionExtensionalityAssumedIsFalse = refl
