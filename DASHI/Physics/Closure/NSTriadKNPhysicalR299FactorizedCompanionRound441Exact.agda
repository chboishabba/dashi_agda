module DASHI.Physics.Closure.NSTriadKNPhysicalR299FactorizedCompanionRound441Exact where

------------------------------------------------------------------------
-- ROUND441 / INHABIT R299 WITH THE LITERAL R440 PHYSICAL DOUBLE SUMS
--
-- R440 proves that each weighted nonlinear Gram product-rule half is the same
-- cross against the DOUBLED forcing aggregate.  R299 stores instead a scalar C
-- for which each half is 2*C.  Do not divide the doubled object by two.
--
-- Define C directly using the undoubled physical weighted forcing fold:
--
--   C_k = Re < A_k , F_k >,
--   A_k = sum_tau w_tau A_tau,
--   F_k = sum_tau w_tau F_tau.
--
-- Finite additivity gives
--
--   Re < A_k , 2 F_k > = 2 C_k,
--
-- and R440 already proves both physical double-sum halves equal the left-hand
-- side.  Thus the historical R299 record is inhabited exactly, without any
-- division, cancellation, absolute value, or estimate.
--
-- R438/R439/R440 separately identify the DOUBLED cross with the weighted
-- quadratic-companion carrier.  The remaining analytic seam is the actual
-- resolvent/Laplace realization plus the cutoff-uniform spacetime estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 2

weightedForcingAggregate :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
weightedForcingAggregate W S system output =
  R224.foldVector
    (R438.weightedProjectedForcingCell W S system)
    (Output.physicalOutputFiber (Audit.cutoff system) output)

weightedAmplitudeAggregate :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
weightedAmplitudeAggregate W S system output =
  R440.weightedAmplitudeAggregate W S system
    (Output.physicalOutputFiber (Audit.cutoff system) output)

fixedOutputR299CommonCross :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
fixedOutputR299CommonCross W S system output =
  R179.realHermitianCross
    (weightedAmplitudeAggregate W S system output)
    (weightedForcingAggregate W S system output)

foldDoubleWeightedIsDoubleUndoubled :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  R438.foldDoubleWeightedProjectedForcing W S system
    (Output.physicalOutputFiber (Audit.cutoff system) output)
  ≡ C3.complex3Add
      (weightedForcingAggregate W S system output)
      (weightedForcingAggregate W S system output)
foldDoubleWeightedIsDoubleUndoubled W S system output =
  R230.foldAdd
    (R438.weightedProjectedForcingCell W S system)
    (R438.weightedProjectedForcingCell W S system)
    (Output.physicalOutputFiber (Audit.cutoff system) output)

r440CommonCrossIsTwoR299CommonCross :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  R440.fixedOutputPhysicalCommonCross W S system output
  ≡ two * fixedOutputR299CommonCross W S system output
r440CommonCrossIsTwoR299CommonCross W S system output =
  let
    A = weightedAmplitudeAggregate W S system output
    Fsum = weightedForcingAggregate W S system output
  in
  trans
    (cong (R179.realHermitianCross A)
      (foldDoubleWeightedIsDoubleUndoubled W S system output))
    (trans
      (R291.realCrossAddRight A Fsum Fsum)
      (solve (R179.realHermitianCross A Fsum ∷ [])))

fixedOutputFirstHalfIsTwoR299Common :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  let fibre = Output.physicalOutputFiber (Audit.cutoff system) output in
  R440.firstPairHalf W S system fibre fibre
  ≡ two * fixedOutputR299CommonCross W S system output
fixedOutputFirstHalfIsTwoR299Common W S system output =
  trans
    (R440.fixedOutputFirstHalfIsCommonCross W S system output)
    (r440CommonCrossIsTwoR299CommonCross W S system output)

fixedOutputSecondHalfIsTwoR299Common :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  let fibre = Output.physicalOutputFiber (Audit.cutoff system) output in
  R440.secondPairHalf W S system fibre fibre
  ≡ two * fixedOutputR299CommonCross W S system output
fixedOutputSecondHalfIsTwoR299Common W S system output =
  trans
    (R440.fixedOutputSecondHalfIsCommonCross W S system output)
    (r440CommonCrossIsTwoR299CommonCross W S system output)

fixedOutputFactorizedPair :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  R299.HeatFactorizedPairRemainder
fixedOutputFactorizedPair W S system output =
  let
    fibre = Output.physicalOutputFiber (Audit.cutoff system) output
    first = R440.firstPairHalf W S system fibre fibre
    second = R440.secondPairHalf W S system fibre fibre
  in
  R299.heat-factorized-pair-remainder
    first
    second
    (first + second)
    (fixedOutputR299CommonCross W S system output)
    refl
    (fixedOutputFirstHalfIsTwoR299Common W S system output)
    (fixedOutputSecondHalfIsTwoR299Common W S system output)

fixedOutputPhysicalPairRemainderIsFourCommon :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  R299.pairRemainder (fixedOutputFactorizedPair W S system output)
  ≡ R299.four * fixedOutputR299CommonCross W S system output
fixedOutputPhysicalPairRemainderIsFourCommon W S system output =
  R299.pairRemainderIsFourTimesAggregateCross
    (fixedOutputFactorizedPair W S system output)

round441DirectR299RecordNormalizationMatched : Bool
round441DirectR299RecordNormalizationMatched = true

round441DivisionByTwoUsed : Bool
round441DivisionByTwoUsed = false

round441FinitePhysicalR299RecordInhabited : Bool
round441FinitePhysicalR299RecordInhabited = true

round441AnalyticLaplaceRepresentationInstalled : Bool
round441AnalyticLaplaceRepresentationInstalled = false

round441LiteralR290RemainderTransportedToHeatFactorization : Bool
round441LiteralR290RemainderTransportedToHeatFactorization = false

round441SignedCrossSpacetimeEstimateClosed : Bool
round441SignedCrossSpacetimeEstimateClosed = false

round441PackageAClosed : Bool
round441PackageAClosed = false

round441ClayPromotion : Bool
round441ClayPromotion = false

round441DirectR299RecordNormalizationMatchedIsTrue :
  round441DirectR299RecordNormalizationMatched ≡ true
round441DirectR299RecordNormalizationMatchedIsTrue = refl

round441DivisionByTwoUsedIsFalse :
  round441DivisionByTwoUsed ≡ false
round441DivisionByTwoUsedIsFalse = refl

round441FinitePhysicalR299RecordInhabitedIsTrue :
  round441FinitePhysicalR299RecordInhabited ≡ true
round441FinitePhysicalR299RecordInhabitedIsTrue = refl

round441AnalyticLaplaceRepresentationInstalledIsFalse :
  round441AnalyticLaplaceRepresentationInstalled ≡ false
round441AnalyticLaplaceRepresentationInstalledIsFalse = refl
