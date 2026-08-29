module DASHI.Physics.Closure.NSTriadKNMixedHelicityGlobalCompanionRound227Exact where

------------------------------------------------------------------------
-- ROUND227 / GLOBAL FINITE COMPANION MASS = 16 * MIXED HELICITY CONVOLUTION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

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
mixedOutputMass {E = E} {I = I} S velocity cutoff output =
  L2.complex3NormSquared
    (R224.foldVector
      (R224.mixedPlusMinus {E = E} {I = I} S velocity)
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
globalMixedHelicityMass {E = E} {I = I} S velocity cutoff outputs =
  mapSum (mixedOutputMass {E = E} {I = I} S velocity cutoff) outputs

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
  ≡ R226.sixteen *
      globalMixedHelicityMass {E = E} {I = I} S velocity cutoff outputs
globalCompanionMassIsSixteenMixedHelicityMass
    E I S L H velocity P cutoff [] = refl
globalCompanionMassIsSixteenMixedHelicityMass
    E I S L H velocity P cutoff (output ∷ outputs) =
  let
    headEquality =
      R226.fixedOutputCompanionMassIsSixteenMixedHelicityMass
        E I S L H velocity P cutoff output
    tailEquality =
      globalCompanionMassIsSixteenMixedHelicityMass
        E I S L H velocity P cutoff outputs
    combined = cong₂ _+_ headEquality tailEquality
    headMixed = mixedOutputMass {E = E} {I = I} S velocity cutoff output
    tailMixed = globalMixedHelicityMass {E = E} {I = I} S velocity cutoff outputs
    distribute :
      R226.sixteen * headMixed + R226.sixteen * tailMixed
      ≡ R226.sixteen * (headMixed + tailMixed)
    distribute = solve (R226.sixteen ∷ headMixed ∷ tailMixed ∷ [])
  in
  trans combined distribute

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
