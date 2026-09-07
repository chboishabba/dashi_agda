module DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact where

------------------------------------------------------------------------
-- ROUND440 / PHYSICAL R299 DOUBLE SUMS FACTOR TO THE R439 COMPANION CROSS
--
-- R299's two nonlinear Gram-product-rule halves have the finite shape
--
--   sum_{a,b} 2 Re <F_a,A_b> w_a w_b,
--   sum_{a,b} 2 Re <A_a,F_b> w_a w_b.
--
-- Put the scalar weights into the literal cells.  Finite bilinearity then
-- gives, with A = sum w_a A_a and 2F = sum (w_b F_b + w_b F_b),
--
--   first half  = Re <2F,A> = Re <A,2F>,
--   second half = Re <A,2F>.
--
-- R438 identifies 2F with the exact slot-or-zero weighted quadratic companion.
-- R439 transports that vector identity through the rational Hermitian cross.
-- Therefore BOTH R299 halves are the same explicit physical companion scalar.
--
-- This closes the finite physical double-sum SAME-OBJECT identification.  It
-- still does not install the analytic Laplace representation of a resolvent
-- weight and does not bound the resulting scalar in spacetime.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNWeightedCompanionHermitianCrossRound439Exact as R439

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 2

sumScalars : List ℚ → ℚ
sumScalars [] = 0ℚ
sumScalars (x ∷ xs) = x + sumScalars xs

weightedAmplitudeCell :
  (W : R294.SwapInvariantCellWeight F) →
  (S : Helical.HelicalModeScalars F) →
  (system : Audit.FiniteComplex3GalerkinSystem F
    (Audit.integerEmbedding system) (Audit.inverseSquare system)) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedAmplitudeCell W S system tau =
  R294.weightedCell W
    (R224.mixedPlusMinus S (Audit.velocity system)) tau

-- The preceding self-indexed type is inconvenient for callers, so use this
-- fully parametric alias below as the public API.
weightedAmplitudeCell′ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedAmplitudeCell′ W S system tau =
  R294.weightedCell W
    (R224.mixedPlusMinus S (Audit.velocity system)) tau

weightedForcingCell :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedForcingCell = R438.weightedProjectedForcingCell

weightedAmplitudeAggregate :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedAmplitudeAggregate W S system items =
  R224.foldVector (weightedAmplitudeCell′ W S system) items

crossZeroLeft :
  (v : C3.Complex3 F) →
  R179.realHermitianCross (C3.complex3Zero F) v ≡ 0ℚ
crossZeroLeft
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

crossZeroRight :
  (v : C3.Complex3 F) →
  R179.realHermitianCross v (C3.complex3Zero F) ≡ 0ℚ
crossZeroRight v = trans (R287.realHermitianCrossSymmetric v (C3.complex3Zero F)) (crossZeroLeft v)

twoCrossAsDoubleLeft :
  (u v : C3.Complex3 F) →
  two * R179.realHermitianCross u v
  ≡ R179.realHermitianCross (C3.complex3Add u u) v
twoCrossAsDoubleLeft u v =
  trans
    (solve (R179.realHermitianCross u v ∷ []))
    (sym (R291.realCrossAddLeft u u v))

twoCrossAsDoubleRight :
  (u v : C3.Complex3 F) →
  two * R179.realHermitianCross u v
  ≡ R179.realHermitianCross u (C3.complex3Add v v)
twoCrossAsDoubleRight u v =
  trans
    (solve (R179.realHermitianCross u v ∷ []))
    (sym (R291.realCrossAddRight u v v))

firstHalfRow :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (alpha : Physical.PhysicalTriadIncidence)
    (betas : List Physical.PhysicalTriadIncidence) → ℚ
firstHalfRow W S system alpha [] = 0ℚ
firstHalfRow W S system alpha (beta ∷ rest) =
  two * R179.realHermitianCross
    (weightedForcingCell W S system alpha)
    (weightedAmplitudeCell′ W S system beta)
  + firstHalfRow W S system alpha rest

firstHalfRowFactors :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (alpha : Physical.PhysicalTriadIncidence)
    (betas : List Physical.PhysicalTriadIncidence) →
  firstHalfRow W S system alpha betas
  ≡ R179.realHermitianCross
      (R438.doubleWeightedProjectedForcingCell W S system alpha)
      (weightedAmplitudeAggregate W S system betas)
firstHalfRowFactors W S system alpha [] =
  sym (crossZeroRight (R438.doubleWeightedProjectedForcingCell W S system alpha))
firstHalfRowFactors W S system alpha (beta ∷ rest) =
  trans
    (cong₂ _+_
      (twoCrossAsDoubleLeft
        (weightedForcingCell W S system alpha)
        (weightedAmplitudeCell′ W S system beta))
      (firstHalfRowFactors W S system alpha rest))
    (sym
      (R291.realCrossAddRight
        (R438.doubleWeightedProjectedForcingCell W S system alpha)
        (weightedAmplitudeCell′ W S system beta)
        (weightedAmplitudeAggregate W S system rest)))

firstPairHalf :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
firstPairHalf W S system [] betas = 0ℚ
firstPairHalf W S system (alpha ∷ rest) betas =
  firstHalfRow W S system alpha betas
  + firstPairHalf W S system rest betas

firstPairHalfFactors :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (alphas betas : List Physical.PhysicalTriadIncidence) →
  firstPairHalf W S system alphas betas
  ≡ R179.realHermitianCross
      (R438.foldDoubleWeightedProjectedForcing W S system alphas)
      (weightedAmplitudeAggregate W S system betas)
firstPairHalfFactors W S system [] betas =
  sym (crossZeroLeft (weightedAmplitudeAggregate W S system betas))
firstPairHalfFactors W S system (alpha ∷ rest) betas =
  trans
    (cong₂ _+_
      (firstHalfRowFactors W S system alpha betas)
      (firstPairHalfFactors W S system rest betas))
    (sym
      (R291.realCrossAddLeft
        (R438.doubleWeightedProjectedForcingCell W S system alpha)
        (R438.foldDoubleWeightedProjectedForcing W S system rest)
        (weightedAmplitudeAggregate W S system betas)))

secondHalfRow :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (alpha : Physical.PhysicalTriadIncidence)
    (betas : List Physical.PhysicalTriadIncidence) → ℚ
secondHalfRow W S system alpha [] = 0ℚ
secondHalfRow W S system alpha (beta ∷ rest) =
  two * R179.realHermitianCross
    (weightedAmplitudeCell′ W S system alpha)
    (weightedForcingCell W S system beta)
  + secondHalfRow W S system alpha rest

secondHalfRowFactors :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (alpha : Physical.PhysicalTriadIncidence)
    (betas : List Physical.PhysicalTriadIncidence) →
  secondHalfRow W S system alpha betas
  ≡ R179.realHermitianCross
      (weightedAmplitudeCell′ W S system alpha)
      (R438.foldDoubleWeightedProjectedForcing W S system betas)
secondHalfRowFactors W S system alpha [] =
  sym (crossZeroRight (weightedAmplitudeCell′ W S system alpha))
secondHalfRowFactors W S system alpha (beta ∷ rest) =
  trans
    (cong₂ _+_
      (twoCrossAsDoubleRight
        (weightedAmplitudeCell′ W S system alpha)
        (weightedForcingCell W S system beta))
      (secondHalfRowFactors W S system alpha rest))
    (sym
      (R291.realCrossAddRight
        (weightedAmplitudeCell′ W S system alpha)
        (R438.doubleWeightedProjectedForcingCell W S system beta)
        (R438.foldDoubleWeightedProjectedForcing W S system rest)))

secondPairHalf :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
secondPairHalf W S system [] betas = 0ℚ
secondPairHalf W S system (alpha ∷ rest) betas =
  secondHalfRow W S system alpha betas
  + secondPairHalf W S system rest betas

secondPairHalfFactors :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (alphas betas : List Physical.PhysicalTriadIncidence) →
  secondPairHalf W S system alphas betas
  ≡ R179.realHermitianCross
      (weightedAmplitudeAggregate W S system alphas)
      (R438.foldDoubleWeightedProjectedForcing W S system betas)
secondPairHalfFactors W S system [] betas =
  sym (crossZeroLeft (R438.foldDoubleWeightedProjectedForcing W S system betas))
secondPairHalfFactors W S system (alpha ∷ rest) betas =
  trans
    (cong₂ _+_
      (secondHalfRowFactors W S system alpha betas)
      (secondPairHalfFactors W S system rest betas))
    (sym
      (R291.realCrossAddLeft
        (weightedAmplitudeCell′ W S system alpha)
        (weightedAmplitudeAggregate W S system rest)
        (R438.foldDoubleWeightedProjectedForcing W S system betas)))

fixedOutputPhysicalCommonCross :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
fixedOutputPhysicalCommonCross W S system output =
  let fibre = Output.physicalOutputFiber (Audit.cutoff system) output in
  R179.realHermitianCross
    (weightedAmplitudeAggregate W S system fibre)
    (R438.foldDoubleWeightedProjectedForcing W S system fibre)

fixedOutputFirstHalfIsCommonCross :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  let fibre = Output.physicalOutputFiber (Audit.cutoff system) output in
  firstPairHalf W S system fibre fibre
  ≡ fixedOutputPhysicalCommonCross W S system output
fixedOutputFirstHalfIsCommonCross W S system output =
  let fibre = Output.physicalOutputFiber (Audit.cutoff system) output in
  trans
    (firstPairHalfFactors W S system fibre fibre)
    (R287.realHermitianCrossSymmetric
      (R438.foldDoubleWeightedProjectedForcing W S system fibre)
      (weightedAmplitudeAggregate W S system fibre))

fixedOutputSecondHalfIsCommonCross :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  let fibre = Output.physicalOutputFiber (Audit.cutoff system) output in
  secondPairHalf W S system fibre fibre
  ≡ fixedOutputPhysicalCommonCross W S system output
fixedOutputSecondHalfIsCommonCross W S system output =
  secondPairHalfFactors W S system fibre fibre
  where fibre = Output.physicalOutputFiber (Audit.cutoff system) output

fixedOutputCommonCrossIsQuadraticCompanionCross :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (output : Z3.FourierMode) →
  fixedOutputPhysicalCommonCross W S system output
  ≡ R439.fixedOutputWeightedCompanionCross E I S W system output
      (weightedAmplitudeAggregate W S system
        (Output.physicalOutputFiber (Audit.cutoff system) output))
fixedOutputCommonCrossIsQuadraticCompanionCross
    S L H W system velocityTransverse output =
  R439.fixedOutputWeightedForcingCrossIsCompanionCross
    _ _ S L H W system velocityTransverse output
    (weightedAmplitudeAggregate W S system
      (Output.physicalOutputFiber (Audit.cutoff system) output))

round440PhysicalWeightedAmplitudeAggregateIdentified : Bool
round440PhysicalWeightedAmplitudeAggregateIdentified = true

round440FirstPhysicalDoubleSumHalfFactorsExactly : Bool
round440FirstPhysicalDoubleSumHalfFactorsExactly = true

round440SecondPhysicalDoubleSumHalfFactorsExactly : Bool
round440SecondPhysicalDoubleSumHalfFactorsExactly = true

round440R299PhysicalDoubleSumSameObjectIdentificationClosed : Bool
round440R299PhysicalDoubleSumSameObjectIdentificationClosed = true

round440CommonCrossIsR439QuadraticCompanionCross : Bool
round440CommonCrossIsR439QuadraticCompanionCross = true

round440AnalyticLaplaceRepresentationInstalled : Bool
round440AnalyticLaplaceRepresentationInstalled = false

round440SignedCrossSpacetimeEstimateClosed : Bool
round440SignedCrossSpacetimeEstimateClosed = false

round440R423SignedCompanionBudgetClosed : Bool
round440R423SignedCompanionBudgetClosed = false

round440PackageAClosed : Bool
round440PackageAClosed = false

round440ClayPromotion : Bool
round440ClayPromotion = false

round440R299PhysicalDoubleSumSameObjectIdentificationClosedIsTrue :
  round440R299PhysicalDoubleSumSameObjectIdentificationClosed ≡ true
round440R299PhysicalDoubleSumSameObjectIdentificationClosedIsTrue = refl

round440AnalyticLaplaceRepresentationInstalledIsFalse :
  round440AnalyticLaplaceRepresentationInstalled ≡ false
round440AnalyticLaplaceRepresentationInstalledIsFalse = refl

round440SignedCrossSpacetimeEstimateClosedIsFalse :
  round440SignedCrossSpacetimeEstimateClosed ≡ false
round440SignedCrossSpacetimeEstimateClosedIsFalse = refl
