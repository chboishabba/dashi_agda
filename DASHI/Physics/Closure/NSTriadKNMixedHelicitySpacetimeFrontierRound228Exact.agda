module DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact where

------------------------------------------------------------------------
-- ROUND228 / FINAL ANALYTIC PACKAGE-A LEAF
--
-- R223--R227 prove on the physical quadratic-kernel carrier
--
--   Q_companion(N,t)
--     = 16 * sum_k || sum_{p+q=k} u_p+(t) x u_q-(t) ||^2.
--
-- The output sum below is the literal `modes` list of the finite Galerkin
-- system at cutoff N.  No arbitrary support list is allowed in the research
-- target.
--
-- AUTHORITY CORRECTION TO ROUND222:
-- The time-integration operator is a MODULE PARAMETER.  The budget record
-- cannot choose its own integration functional.  A future continuous-time PDE
-- receipt must instantiate this module with an independently owned physical
-- integration model.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCompanionMassRound226Exact as R226
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

      -- Literal finite Galerkin system at every cutoff and time.
      systemAt : Nat → Time → Audit.FiniteComplex3GalerkinSystem F E I
      systemCutoffAgreement :
        (cutoff : Nat) (t : Time) →
        Audit.cutoff (systemAt cutoff t) ≡ cutoff

      velocityTransverse :
        (cutoff : Nat) (t : Time) (mode : Z3.FourierMode) →
        Helical.Transverse E mode (Audit.velocity (systemAt cutoff t) mode)

  open PhysicalMixedHelicityTrajectory public

  helicityDataAt :
    (T : PhysicalMixedHelicityTrajectory) →
    (cutoff : Nat) (t : Time) →
    R225.PhysicalFixedOutputHelicityData
      (E T) (I T) (S T) (L T) (H T)
      (Audit.velocity (systemAt T cutoff t))
  helicityDataAt T cutoff t =
    R225.physical-fixed-output-helicity-data
      (velocityTransverse T cutoff t)

  mixedHelicityMass :
    (T : PhysicalMixedHelicityTrajectory) → Nat → Time → ℚ
  mixedHelicityMass T cutoff t =
    R227.globalMixedHelicityMass
      {E = E T} {I = I T}
      (S T)
      (Audit.velocity (systemAt T cutoff t))
      cutoff
      (Audit.modes (systemAt T cutoff t))

  companionMass :
    (T : PhysicalMixedHelicityTrajectory) → Nat → Time → ℚ
  companionMass T cutoff t =
    R227.globalCompanionMass
      (E T) (S T)
      (Audit.velocity (systemAt T cutoff t))
      cutoff
      (Audit.modes (systemAt T cutoff t))

  companionMassPointwiseIsSixteenMixed :
    (T : PhysicalMixedHelicityTrajectory) →
    (cutoff : Nat) (t : Time) →
    companionMass T cutoff t
    ≡ R226.sixteen * mixedHelicityMass T cutoff t
  companionMassPointwiseIsSixteenMixed T cutoff t =
    R227.globalCompanionMassIsSixteenMixedHelicityMass
      (E T) (I T) (S T) (L T) (H T)
      (Audit.velocity (systemAt T cutoff t))
      (helicityDataAt T cutoff t)
      cutoff
      (Audit.modes (systemAt T cutoff t))

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

round228UsesLiteralGalerkinOutputModes : Bool
round228UsesLiteralGalerkinOutputModes = true

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

round228UsesLiteralGalerkinOutputModesIsTrue :
  round228UsesLiteralGalerkinOutputModes ≡ true
round228UsesLiteralGalerkinOutputModesIsTrue = refl

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
