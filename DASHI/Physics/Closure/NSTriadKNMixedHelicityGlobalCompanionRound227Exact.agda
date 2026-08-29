module DASHI.Physics.Closure.NSTriadKNMixedHelicityGlobalCompanionRound227Exact where

------------------------------------------------------------------------
-- ROUND227 / GLOBAL FINITE COMPANION MASS = 16 * MIXED HELICITY CONVOLUTION
--
-- Round226 is outputwise.  Fourier L2 aggregation has no cross-output Gram
-- debt, so summing the exact identity over any finite output list gives
--
--   Q_companion
--     = 16 sum_k || sum_{p+q=k} u_p+ x u_q- ||^2.
--
-- Thus the final Package-A analytic leaf can be stated directly as a uniform
-- time-integrated mixed-helicity convolution estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCompanionMassRound226Exact as R226

F : C3.RealField _
F = Rational.rationalRealField

sumRational : List ℚ → ℚ
sumRational [] = 0ℚ
sumRational (x ∷ xs) = x + sumRational xs

mapSum :
  (f : Z3.FourierMode → ℚ) → List Z3.FourierMode → ℚ
mapSum f [] = 0ℚ
mapSum f (k ∷ ks) = f k + mapSum f ks

companionOutputMass :
  (E : C3.IntegerEmbedding F)
  (S : Helical.HelicalModeScalars F)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → ℚ
companionOutputMass E S velocity cutoff output =
  L2.complex3NormSquared
    (R224.foldVector (R226.quadraticKernelCell E S velocity)
      (Output.physicalOutputFiber cutoff output))

mixedOutputMass :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E}
  (S : Helical.HelicalModeScalars F)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → Z3.FourierMode → ℚ
mixedOutputMass S velocity cutoff output =
  L2.complex3NormSquared
    (R224.foldVector (R224.mixedPlusMinus S velocity)
      (Output.physicalOutputFiber cutoff output))

globalCompanionMass :
  (E : C3.IntegerEmbedding F)
  (S : Helical.HelicalModeScalars F)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → List Z3.FourierMode → ℚ
globalCompanionMass E S velocity cutoff outputs =
  mapSum (companionOutputMass E S velocity cutoff) outputs

globalMixedHelicityMass :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E}
  (S : Helical.HelicalModeScalars F)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Nat → List Z3.FourierMode → ℚ
globalMixedHelicityMass S velocity cutoff outputs =
  mapSum (mixedOutputMass S velocity cutoff) outputs

globalCompanionMassIsSixteenMixedHelicityMass :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity)
  (cutoff : Nat) (outputs : List Z3.FourierMode) →
  globalCompanionMass E S velocity cutoff outputs
  ≡ R226.sixteen * globalMixedHelicityMass S velocity cutoff outputs
globalCompanionMassIsSixteenMixedHelicityMass
    E I S L H velocity P cutoff [] = refl
globalCompanionMassIsSixteenMixedHelicityMass
    E I S L H velocity P cutoff (output ∷ outputs) =
  cong₂ _+_
    (R226.fixedOutputCompanionMassIsSixteenMixedHelicityMass
      E I S L H velocity P cutoff output)
    (globalCompanionMassIsSixteenMixedHelicityMass
      E I S L H velocity P cutoff outputs)

round227GlobalCompanionIsMixedHelicityConvolutionMass : Bool
round227GlobalCompanionIsMixedHelicityConvolutionMass = true

round227OnlyMixedHelicitySpacetimeBudgetRemains : Bool
round227OnlyMixedHelicitySpacetimeBudgetRemains = true

round227MixedHelicityIntegratedBudgetClosed : Bool
round227MixedHelicityIntegratedBudgetClosed = false

round227PackageAClosed : Bool
round227PackageAClosed = false

round227ClayPromotion : Bool
round227ClayPromotion = false

round227GlobalCompanionIsMixedHelicityConvolutionMassIsTrue :
  round227GlobalCompanionIsMixedHelicityConvolutionMass ≡ true
round227GlobalCompanionIsMixedHelicityConvolutionMassIsTrue = refl

round227OnlyMixedHelicitySpacetimeBudgetRemainsIsTrue :
  round227OnlyMixedHelicitySpacetimeBudgetRemains ≡ true
round227OnlyMixedHelicitySpacetimeBudgetRemainsIsTrue = refl

round227MixedHelicityIntegratedBudgetClosedIsFalse :
  round227MixedHelicityIntegratedBudgetClosed ≡ false
round227MixedHelicityIntegratedBudgetClosedIsFalse = refl

round227PackageAClosedIsFalse : round227PackageAClosed ≡ false
round227PackageAClosedIsFalse = refl

round227ClayPromotionIsFalse : round227ClayPromotion ≡ false
round227ClayPromotionIsFalse = refl
