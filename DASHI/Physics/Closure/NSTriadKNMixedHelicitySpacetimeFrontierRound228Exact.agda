module DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact where

------------------------------------------------------------------------
-- ROUND228 / FINAL ANALYTIC PACKAGE-A LEAF
--
-- R223--R227 prove, on the complete physical quadratic-kernel fibre,
--
--   Q_companion(N,t)
--     = 16 * sum_k || sum_{p+q=k} u_p+(t) x u_q-(t) ||^2.
--
-- Therefore the remaining arbitrary-data theorem is exactly a cutoff-uniform
-- spacetime estimate for the mixed-helicity convolution mass.
--
-- IMPORTANT AUTHORITY CORRECTION TO ROUND222:
-- The time-integration operator is a MODULE PARAMETER here.  The budget record
-- cannot choose its own integration functional.  A future continuous-time PDE
-- receipt must instantiate this module with an independently owned physical
-- integration model.  No zero-functional loophole can by itself promote A.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNMixedHelicityGlobalCompanionRound227Exact as R227

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalTimeIntegral
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ) where

  record PhysicalMixedHelicityTrajectory : Set₁ where
    constructor physical-mixed-helicity-trajectory
    field
      E : C3.IntegerEmbedding F
      I : C3.ModeInverseSquare F E
      S : Helical.HelicalModeScalars F
      L : Helical.PeriodicHelicalProjectorLaws F E I S
      H : R142.HelicalHalfCalibration S

      velocity : Time → Z3.FourierMode → C3.Complex3 F
      velocityTransverse :
        (t : Time) (mode : Z3.FourierMode) →
        Helical.Transverse E mode (velocity t mode)

      -- Exact finite Fourier output support used at each Galerkin cutoff.
      outputs : Nat → List Z3.FourierMode

  open PhysicalMixedHelicityTrajectory public

  helicityDataAt :
    (T : PhysicalMixedHelicityTrajectory) → (t : Time) →
    R225.PhysicalFixedOutputHelicityData
      (E T) (I T) (S T) (L T) (H T) (velocity T t)
  helicityDataAt T t =
    R225.physical-fixed-output-helicity-data (velocityTransverse T t)

  mixedHelicityMass :
    (T : PhysicalMixedHelicityTrajectory) → Nat → Time → ℚ
  mixedHelicityMass T cutoff t =
    R227.globalMixedHelicityMass
      {E = E T} {I = I T}
      (S T) (velocity T t) cutoff (outputs T cutoff)

  companionMass :
    (T : PhysicalMixedHelicityTrajectory) → Nat → Time → ℚ
  companionMass T cutoff t =
    R227.globalCompanionMass
      (E T) (S T) (velocity T t) cutoff (outputs T cutoff)

  companionMassPointwiseIsSixteenMixed :
    (T : PhysicalMixedHelicityTrajectory) →
    (cutoff : Nat) (t : Time) →
    companionMass T cutoff t
    ≡ R227.R226.sixteen * mixedHelicityMass T cutoff t
  companionMassPointwiseIsSixteenMixed T cutoff t =
    R227.globalCompanionMassIsSixteenMixedHelicityMass
      (E T) (I T) (S T) (L T) (H T) (velocity T t)
      (helicityDataAt T t) cutoff (outputs T cutoff)

  record PhysicalMixedHelicitySpacetimeBudget
      (T : PhysicalMixedHelicityTrajectory) : Set where
    constructor physical-mixed-helicity-spacetime-budget
    field
      cutoffIndependentBound : Time → ℚ

      -- THE ONE REMAINING PDE THEOREM.
      integratedMixedHelicityBound :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (mixedHelicityMass T cutoff) terminal
        ≤ cutoffIndependentBound terminal

  open PhysicalMixedHelicitySpacetimeBudget public

round228PairwiseSameHelicityCancellationClosed : Bool
round228PairwiseSameHelicityCancellationClosed = true

round228FixedOutputMixedHelicityCollapseClosed : Bool
round228FixedOutputMixedHelicityCollapseClosed = true

round228GlobalCompanionMixedHelicityIdentityClosed : Bool
round228GlobalCompanionMixedHelicityIdentityClosed = true

round228Round222SelfChosenIntegrationAuthorityAccepted : Bool
round228Round222SelfChosenIntegrationAuthorityAccepted = false

round228ConcreteContinuousTimeIntegrationReceiptInstalled : Bool
round228ConcreteContinuousTimeIntegrationReceiptInstalled = false

round228MixedHelicitySpacetimeBudgetClosed : Bool
round228MixedHelicitySpacetimeBudgetClosed = false

round228NovelMathematicalLeafCount : Nat
round228NovelMathematicalLeafCount = 1

round228PackageAClosed : Bool
round228PackageAClosed = false

round228ClayPromotion : Bool
round228ClayPromotion = false

round228PairwiseSameHelicityCancellationClosedIsTrue :
  round228PairwiseSameHelicityCancellationClosed ≡ true
round228PairwiseSameHelicityCancellationClosedIsTrue = refl

round228FixedOutputMixedHelicityCollapseClosedIsTrue :
  round228FixedOutputMixedHelicityCollapseClosed ≡ true
round228FixedOutputMixedHelicityCollapseClosedIsTrue = refl

round228GlobalCompanionMixedHelicityIdentityClosedIsTrue :
  round228GlobalCompanionMixedHelicityIdentityClosed ≡ true
round228GlobalCompanionMixedHelicityIdentityClosedIsTrue = refl

round228Round222SelfChosenIntegrationAuthorityAcceptedIsFalse :
  round228Round222SelfChosenIntegrationAuthorityAccepted ≡ false
round228Round222SelfChosenIntegrationAuthorityAcceptedIsFalse = refl

round228ConcreteContinuousTimeIntegrationReceiptInstalledIsFalse :
  round228ConcreteContinuousTimeIntegrationReceiptInstalled ≡ false
round228ConcreteContinuousTimeIntegrationReceiptInstalledIsFalse = refl

round228MixedHelicitySpacetimeBudgetClosedIsFalse :
  round228MixedHelicitySpacetimeBudgetClosed ≡ false
round228MixedHelicitySpacetimeBudgetClosedIsFalse = refl

round228NovelMathematicalLeafCountIsOne :
  round228NovelMathematicalLeafCount ≡ 1
round228NovelMathematicalLeafCountIsOne = refl

round228PackageAClosedIsFalse : round228PackageAClosed ≡ false
round228PackageAClosedIsFalse = refl

round228ClayPromotionIsFalse : round228ClayPromotion ≡ false
round228ClayPromotionIsFalse = refl
