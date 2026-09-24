{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiveThreeChannelHelicityBudgetRound638Exact where

------------------------------------------------------------------------
-- ROUND638 / R634 THREE-CHANNEL PRODUCER WITH LITERAL EXTERNAL HELICITY BUDGET
--
-- R634 already reduces the self channel to:
--
--   homochiral radial-increment signed budget
--   + heterochiral radial-sum signed budget,
--
-- while retaining a canonical-external signed budget as its third input.
--
-- R637 now proves the third live spacetime carrier is exactly the integrated
-- literal external helicity-commutator carrier.
--
-- Therefore the most resolved optional three-channel producer is:
--
--   homochiral signed budget
--   + heterochiral signed budget
--   + external helicity-commutator signed budget
--       -> R634 -> R628 -> R568.
--
-- This owner changes no inequality and introduces no estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNLiveSelfHelicityExternalSpacetimeRound634Exact as R634
import DASHI.Physics.Closure.NSTriadKNLiveExternalHelicityCommutatorSpacetimeRound637Exact as R637

F : C3.RealField _
F = Rational.rationalRealField

module LiveThreeChannelHelicity638
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Self = R634.LiveSelfHelicityExternal634
    Time initialTime integrateTo DerivativeOf integration

  module External = R637.LiveExternalHelicity637
    Time initialTime integrateTo DerivativeOf integration

  module Dyn = Self.Dyn
  module Support = Self.Support
  module Comm = Self.Comm

  record ThreeChannelHelicitySpacetimeBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      homochiralBound heterochiralBound externalHelicityBound : Time → ℚ

      homochiralSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 * Self.integratedHomochiral T R cutoff terminal
        ≤ homochiralBound terminal

      heterochiralSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 * Self.integratedHeterochiral T R cutoff terminal
        ≤ heterochiralBound terminal

      externalHelicitySignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567
          * External.integratedHelicityExternalGlobalForcingFull
              T R cutoff terminal
        ≤ externalHelicityBound terminal

  open ThreeChannelHelicitySpacetimeBudget public

  toR634 :
    ∀ {T R} →
    ThreeChannelHelicitySpacetimeBudget T R →
    Self.SelfHelicityCanonicalExternalSpacetimeBudget T R
  toR634 {T} {R} B = record
    { Self.homochiralBound = homochiralBound B
    ; Self.heterochiralBound = heterochiralBound B
    ; Self.canonicalExternalBound = externalHelicityBound B
    ; Self.homochiralSignedBudget = homochiralSignedBudget B
    ; Self.heterochiralSignedBudget = heterochiralSignedBudget B
    ; Self.canonicalExternalSignedBudget = λ cutoff terminal →
        let
          sameObject =
            External.integratedCanonicalExternalIsHelicity
              T R cutoff terminal
          paid =
            externalHelicitySignedBudget B cutoff terminal
        in
        subst
          (λ selected →
            R567.four567 * selected
              ≤ externalHelicityBound B terminal)
          (sym sameObject)
          paid
    }

  threeChannelHelicityBudgetBuildsR568 :
    ∀ {T R} →
    ThreeChannelHelicitySpacetimeBudget T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  threeChannelHelicityBudgetBuildsR568 B =
    Self.selfHelicityExternalBudgetBuildsR568 (toR634 B)

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round638ExternalChannelLiterallyHelicityCommutator : Bool
round638ExternalChannelLiterallyHelicityCommutator = true

round638ThreeResolvedChannelBudgetsCompileToR568 : Bool
round638ThreeResolvedChannelBudgetsCompileToR568 = true

round638SeparateThreeChannelBudgetsMandatoryForR568 : Bool
round638SeparateThreeChannelBudgetsMandatoryForR568 = false

round638HomochiralSignedBudgetClosed : Bool
round638HomochiralSignedBudgetClosed = false

round638HeterochiralSignedBudgetClosed : Bool
round638HeterochiralSignedBudgetClosed = false

round638ExternalHelicitySignedBudgetClosed : Bool
round638ExternalHelicitySignedBudgetClosed = false

round638IntroducesEstimate : Bool
round638IntroducesEstimate = false

round638ExternalChannelLiterallyHelicityCommutatorIsTrue :
  round638ExternalChannelLiterallyHelicityCommutator ≡ true
round638ExternalChannelLiterallyHelicityCommutatorIsTrue = refl

round638ThreeResolvedChannelBudgetsCompileToR568IsTrue :
  round638ThreeResolvedChannelBudgetsCompileToR568 ≡ true
round638ThreeResolvedChannelBudgetsCompileToR568IsTrue = refl

round638SeparateThreeChannelBudgetsMandatoryForR568IsFalse :
  round638SeparateThreeChannelBudgetsMandatoryForR568 ≡ false
round638SeparateThreeChannelBudgetsMandatoryForR568IsFalse = refl

round638HomochiralSignedBudgetClosedIsFalse :
  round638HomochiralSignedBudgetClosed ≡ false
round638HomochiralSignedBudgetClosedIsFalse = refl

round638HeterochiralSignedBudgetClosedIsFalse :
  round638HeterochiralSignedBudgetClosed ≡ false
round638HeterochiralSignedBudgetClosedIsFalse = refl

round638ExternalHelicitySignedBudgetClosedIsFalse :
  round638ExternalHelicitySignedBudgetClosed ≡ false
round638ExternalHelicitySignedBudgetClosedIsFalse = refl

round638IntroducesEstimateIsFalse :
  round638IntroducesEstimate ≡ false
round638IntroducesEstimateIsFalse = refl
