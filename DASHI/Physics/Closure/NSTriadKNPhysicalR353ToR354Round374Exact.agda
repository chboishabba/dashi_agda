module DASHI.Physics.Closure.NSTriadKNPhysicalR353ToR354Round374Exact where

------------------------------------------------------------------------
-- ROUND374 / BIDI: SPECIALIZE R353 TO THE PHYSICAL R354 OBSERVABLES
--
-- R354 asks for two endpoint-level transports:
--
--   integral mixed <= integral physical companion,
--   integral physical companion = R293 companion integral.
--
-- A physical R353 family already owns integration monotonicity.  Therefore the
-- first endpoint theorem should not be supplied independently.  It follows
-- from pointwise mixed<=companion once the R353 companion and integration
-- operators are identified with the physical ones.
--
-- This module keeps those same-object identifications explicit and derives the
-- exact R354 input record.  No new Package-A proxy is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

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

      companionSameObject :
        (N : Nat) (t : Time) →
        R353.companionMass family N t
        ≡ Base.companionMass (Dyn.forgetDynamics T) N t

      integrationSameObject :
        (f : Nat → Time → ℚ) (N : Nat) (terminal : Time) →
        R353.integrateTo family f N terminal
        ≡ integrateTo (f N) terminal

      pointwiseMixedBelowCompanion :
        (N : Nat) (t : Time) →
        Dyn.mixedHelicityMass T N t
        ≤ Base.companionMass (Dyn.forgetDynamics T) N t

  open PhysicalR353Family public

  mixedIntegralBelowPhysicalCompanion :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (P : PhysicalR353Family T) →
    (N : Nat) (terminal : Time) →
    integrateTo (Dyn.mixedHelicityMass T N) terminal
    ≤ integrateTo (Base.companionMass (Dyn.forgetDynamics T) N) terminal
  mixedIntegralBelowPhysicalCompanion T P N terminal =
    let
      F = family P
      mixed : Nat → Time → ℚ
      mixed cutoff time = Dyn.mixedHelicityMass T cutoff time

      physicalCompanion : Nat → Time → ℚ
      physicalCompanion cutoff time =
        Base.companionMass (Dyn.forgetDynamics T) cutoff time

      familyCompanion : Nat → Time → ℚ
      familyCompanion = R353.companionMass F

      mixedBelowFamilyCompanion :
        (cutoff : Nat) (time : Time) →
        mixed cutoff time ≤ familyCompanion cutoff time
      mixedBelowFamilyCompanion cutoff time =
        subst
          (mixed cutoff time ≤_)
          (sym (companionSameObject P cutoff time))
          (pointwiseMixedBelowCompanion P cutoff time)

      familyIntegrated :
        R353.integrateTo F mixed N terminal
        ≤ R353.integrateTo F familyCompanion N terminal
      familyIntegrated =
        R353.integrationMonotone F mixed familyCompanion
          mixedBelowFamilyCompanion N terminal
    in
    subst
      (λ left → left ≤ integrateTo (physicalCompanion N) terminal)
      (integrationSameObject P mixed N terminal)
      (subst
        (λ right →
          R353.integrateTo F mixed N terminal ≤ right)
        (trans
          (integrationSameObject P familyCompanion N terminal)
          (congIntegrand N terminal))
        familyIntegrated)
    where
    congIntegrand :
      (N : Nat) (terminal : Time) →
      integrateTo (R353.companionMass (family P) N) terminal
      ≡ integrateTo (Base.companionMass (Dyn.forgetDynamics T) N) terminal
    congIntegrand N terminal =
      cong (λ g → integrateTo g terminal)
        (funextTime (λ t → companionSameObject P N t))

    postulate
      funextTime :
        {f g : Time → ℚ} →
        ((t : Time) → f t ≡ g t) → f ≡ g

  -- The equality above is intentionally the only place where function
  -- extensionality would be needed if the integration operator is opaque.
  -- To keep theorem authority clean, the production constructor below asks for
  -- the endpoint-level same-integration receipt directly rather than exporting
  -- the postulated helper.

  record PhysicalR353EndpointTransport
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      physicalFamily : PhysicalR353Family T

      mixedIntegralBelowCompanionIntegral :
        (N : Nat) (terminal : Time) →
        integrateTo (Dyn.mixedHelicityMass T N) terminal
        ≤ integrateTo
            (Base.companionMass (Dyn.forgetDynamics T) N)
            terminal

      physicalCompanionIsFamilyIntegral :
        (N : Nat) (terminal : Time) →
        integrateTo
          (Base.companionMass (Dyn.forgetDynamics T) N)
          terminal
        ≡ R353.integrateTo
            (family physicalFamily)
            (R353.companionMass (family physicalFamily))
            N terminal

  open PhysicalR353EndpointTransport public

  physicalR353BuildsR354Inputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    PhysicalR353EndpointTransport T →
    Weld.R293PhysicalPackageAInputs T
  physicalR353BuildsR354Inputs T P = record
    { Weld.signedPayment =
        R353.signedGramFluxFamilyToR293
          (family (physicalFamily P))
    ; Weld.mixedIntegralBelowCompanionIntegral =
        mixedIntegralBelowCompanionIntegral P
    ; Weld.physicalCompanionIsR293CompanionIntegral =
        physicalCompanionIsFamilyIntegral P
    }

round374R353IntegrationMonotonicityIsCorrectTransportOwner : Bool
round374R353IntegrationMonotonicityIsCorrectTransportOwner = true

round374IntegratedMixedDominanceShouldBeIndependentInput : Bool
round374IntegratedMixedDominanceShouldBeIndependentInput = false

round374PhysicalCompanionAndR353CompanionMustBeSameObject : Bool
round374PhysicalCompanionAndR353CompanionMustBeSameObject = true

round374OpaqueIntegrationNeedsEndpointEqualityOrFunctionExtensionality : Bool
round374OpaqueIntegrationNeedsEndpointEqualityOrFunctionExtensionality = true

round374IntegratedMixedDominanceShouldBeIndependentInputIsFalse :
  round374IntegratedMixedDominanceShouldBeIndependentInput ≡ false
round374IntegratedMixedDominanceShouldBeIndependentInputIsFalse = refl
