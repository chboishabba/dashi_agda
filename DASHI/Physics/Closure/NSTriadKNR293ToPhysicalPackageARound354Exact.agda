module DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact where

------------------------------------------------------------------------
-- ROUND354 / BIDI: R293 SIGNED-INTEGRATED CONSUMER -> AUTHORITATIVE PACKAGE A
--
-- Repository archaeology shows that R258 is already the final compiler into
-- the corrected R240 physical Package-A object.  It asks only for a cutoff-
-- uniform bound on the literal mixed-helicity mass of one actual NS Galerkin
-- trajectory.
--
-- R293 instead closes the integrated companion mass.  R228 already owns the
-- same-object pointwise identity companion = 16 * mixed.  This adapter does
-- not reprove either fact and does not introduce a new Package-A proxy.
-- It asks only for the two physical transport receipts needed to connect the
-- already-owned objects:
--
--   (1) the physical mixed integral is below the physical companion integral;
--   (2) that physical companion integral is exactly the companion integral
--       consumed by the supplied R293 payment.
--
-- The R293 combined cutoff-independent bound is then reused unchanged as the
-- R258/R240 cutoff-independent mixed-helicity bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNPackageASequentialBoundRound258Exact as R258
import DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact as R293

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalPackageAWeld
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Base = R228.PhysicalTimeIntegral Time integrateTo
  module Seq = R258.PackageASequential Time initialTime integrateTo DerivativeOf

  record R293PhysicalPackageAInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      signedPayment : R293.SignedIntegratedGramPayment Nat Time

      -- Physical BIDI receipt: the mixed quantity controlled by Round240 is
      -- no larger after integration than the old companion quantity.
      mixedIntegralBelowCompanionIntegral :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (Dyn.mixedHelicityMass T cutoff) terminal
        ≤ integrateTo
            (Base.companionMass (Dyn.forgetDynamics T) cutoff)
            terminal

      -- Same-object receipt: the physical companion integral is literally the
      -- companion integral that R293 has paid.  This blocks proxy substitution.
      physicalCompanionIsR293CompanionIntegral :
        (cutoff : Nat) (terminal : Time) →
        integrateTo
          (Base.companionMass (Dyn.forgetDynamics T) cutoff)
          terminal
        ≡ R293.integrateTo signedPayment
            (R293.companionMass signedPayment)
            cutoff terminal

  open R293PhysicalPackageAInputs public

  r293BuildsSequentialUniformAuthority :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    R293PhysicalPackageAInputs T →
    Seq.SequentialUniformBoundAuthority T
  r293BuildsSequentialUniformAuthority T I = record
    { Seq.cutoffIndependentBound = R293.combinedIntegratedBound P
    ; Seq.integratedMixedHelicityBound = mixedBound
    }
    where
    P = signedPayment I

    companionPaid :
      (cutoff : Nat) (terminal : Time) →
      R293.integrateTo P (R293.companionMass P) cutoff terminal
      ≤ R293.combinedIntegratedBound P terminal
    companionPaid = R293.signedIntegratedGramClosesCompanionBudget P

    physicalCompanionPaid :
      (cutoff : Nat) (terminal : Time) →
      integrateTo
        (Base.companionMass (Dyn.forgetDynamics T) cutoff)
        terminal
      ≤ R293.combinedIntegratedBound P terminal
    physicalCompanionPaid cutoff terminal =
      subst
        (λ left → left ≤ R293.combinedIntegratedBound P terminal)
        (physicalCompanionIsR293CompanionIntegral I cutoff terminal)
        (companionPaid cutoff terminal)

    mixedBound :
      (cutoff : Nat) (terminal : Time) →
      integrateTo (Dyn.mixedHelicityMass T cutoff) terminal
      ≤ R293.combinedIntegratedBound P terminal
    mixedBound cutoff terminal =
      ℚP.≤-trans
        (mixedIntegralBelowCompanionIntegral I cutoff terminal)
        (physicalCompanionPaid cutoff terminal)

  r293BuildsPhysicalPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    R293PhysicalPackageAInputs T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  r293BuildsPhysicalPackageA T I =
    Seq.authorityBuildsPhysicalPackageA T
      (r293BuildsSequentialUniformAuthority T I)

round354R293CombinedBoundReusedAsPackageABound : Bool
round354R293CombinedBoundReusedAsPackageABound = true

round354R258PackageACompilerReused : Bool
round354R258PackageACompilerReused = true

round354SameObjectCompanionReceiptExplicit : Bool
round354SameObjectCompanionReceiptExplicit = true

round354NoPointwisePositiveGramMajorantReintroduced : Bool
round354NoPointwisePositiveGramMajorantReintroduced = true

round354PhysicalPackageAAdapterClosedConditionally : Bool
round354PhysicalPackageAAdapterClosedConditionally = true

-- The adapter is complete under its explicit physical inputs.  This file does
-- not globally assert those inputs for every NS trajectory and therefore does
-- not promote the repository-wide Clay flag.
round354ClayPromotion : Bool
round354ClayPromotion = false

round354PhysicalPackageAAdapterClosedConditionallyIsTrue :
  round354PhysicalPackageAAdapterClosedConditionally ≡ true
round354PhysicalPackageAAdapterClosedConditionallyIsTrue = refl

round354ClayPromotionIsFalse : round354ClayPromotion ≡ false
round354ClayPromotionIsFalse = refl
