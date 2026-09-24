{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact where

------------------------------------------------------------------------
-- ROUND694 / LITERAL R230 COMMUTATOR -> NESTED FOUR-HELICITY INNER TRIADS
--
-- Use the UNIT swap-invariant R294 weight.  R438 says its doubled weighted
-- forcing cell is exactly two copies of the literal R230 commutator cell.
-- R573 then says two copies of that doubled cell are exactly the nested
-- componentwise carrier:
--
--   Nested_beta
--     = 4 * C_beta
--
-- where Nested_beta is a finite fold over the literal inner fibre
--
--   sigma : a+b = p_beta
--
-- and each sigma contributes the four exact R571 helical
-- multiplier-difference channels.
--
-- Therefore, for the R692 outer mixed cell A_alpha,
--
--   W(A_alpha, Nested_beta) = 4 W(A_alpha, C_beta),
--
-- and the complete same-output pair sum satisfies
--
--   NestedPairSum_k = 4 * CommutatorPairSum_k.
--
-- No division is used.  This is the requested literal nested triad incidence
-- expansion before any inequality or absolute value.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNForcingHelicityCommutatorRound306Exact as R306
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as R595
import DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyPairNormalFormRound600Exact as R600
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact as R692

F : C3.RealField _
F = Rational.rationalRealField

four : ℚ
four = 4

unitWeight : R294.SwapInvariantCellWeight F
unitWeight = record
  { R294.weight = λ _ → C3.complexOne F
  ; R294.swapInvariant = λ _ → refl
  }

module NestedExpansion
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Base = R692.Expansion physicalSystem S

  module Nested =
    R573.WeightedNested
      unitWeight S L H Base.system velocityTransverse

  nestedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  nestedCell = Nested.nestedWeightedCompanionCell

  doubledUnitWeightedIsDoubleCommutator :
    (beta : Physical.PhysicalTriadIncidence) →
    R438.doubleWeightedProjectedForcingCell
      unitWeight S Base.system beta
    ≡
    R306.doubleR230Cell S Base.velocity Base.forcing beta
  doubledUnitWeightedIsDoubleCommutator beta =
    trans
      (R438.doubleWeightedCellIsScaledDoubleR230
        unitWeight S Base.system beta)
      (R106.complex3ScaleOne
        (R306.doubleR230Cell S Base.velocity Base.forcing beta))

  nestedCellIsFourCommutatorCopies :
    (beta : Physical.PhysicalTriadIncidence) →
    nestedCell beta
    ≡
    C3.complex3Add
      (C3.complex3Add
        (Base.commutatorCell beta)
        (Base.commutatorCell beta))
      (C3.complex3Add
        (Base.commutatorCell beta)
        (Base.commutatorCell beta))
  nestedCellIsFourCommutatorCopies beta =
    let
      D =
        R438.doubleWeightedProjectedForcingCell
          unitWeight S Base.system beta
      C = Base.commutatorCell beta
      doubleMeaning :
        D ≡ C3.complex3Add C C
      doubleMeaning = doubledUnitWeightedIsDoubleCommutator beta
    in
    trans
      (sym (Nested.fourWeightedR294CellIsNested beta))
      (cong₂ C3.complex3Add doubleMeaning doubleMeaning)

  nestedPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  nestedPair alpha beta =
    Work.coherentWork (Base.mixedCell alpha) (nestedCell beta)

  nestedPairIsFourCommutatorPair :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    nestedPair alpha beta
    ≡ four * Base.commutatorPair alpha beta
  nestedPairIsFourCommutatorPair alpha beta =
    let
      A = Base.mixedCell alpha
      C = Base.commutatorCell beta
      pair = Base.commutatorPair alpha beta
    in
    trans
      (cong
        (Work.coherentWork A)
        (nestedCellIsFourCommutatorCopies beta))
      (trans
        (Work.workAddRight
          A
          (C3.complex3Add C C)
          (C3.complex3Add C C))
        (trans
          (cong₂ _+_
            (Work.workAddRight A C C)
            (Work.workAddRight A C C))
          (solve (pair ∷ []))))

  outputNestedPairSum :
    Z3.FourierMode → ℚ
  outputNestedPairSum output =
    R543.fullSquareSum nestedPair (Base.fibre output)

  outputNestedPairSumIsFourCommutator :
    (output : Z3.FourierMode) →
    outputNestedPairSum output
    ≡ four * Base.outputPairIncidenceSum output
  outputNestedPairSumIsFourCommutator output =
    trans
      (R595.fullSquareCongruent
        nestedPair
        (R600.scaledPair four Base.commutatorPair)
        nestedPairIsFourCommutatorPair
        (Base.fibre output))
      (R600.fullSquareScale
        four Base.commutatorPair (Base.fibre output))

  sumOutputNestedPairs :
    List Z3.FourierMode → ℚ
  sumOutputNestedPairs [] = 0
  sumOutputNestedPairs (output ∷ rest) =
    outputNestedPairSum output + sumOutputNestedPairs rest

  globalNestedPairsAreFourCommutatorPairs :
    (outputs : List Z3.FourierMode) →
    sumOutputNestedPairs outputs
    ≡ four * Base.sumOutputPairIncidences outputs
  globalNestedPairsAreFourCommutatorPairs [] = solve []
  globalNestedPairsAreFourCommutatorPairs (output ∷ rest) =
    trans
      (cong₂ _+_
        (outputNestedPairSumIsFourCommutator output)
        (globalNestedPairsAreFourCommutatorPairs rest))
      (solve
        ( Base.outputPairIncidenceSum output
        ∷ Base.sumOutputPairIncidences rest
        ∷ []))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round694UnitWeightedNestedCellIsFourLiteralR230Commutators : Bool
round694UnitWeightedNestedCellIsFourLiteralR230Commutators = true

round694NestedInnerCarrierIsLiteralPhysicalOutputFibre : Bool
round694NestedInnerCarrierIsLiteralPhysicalOutputFibre = true

round694InnerFourHelicityMultiplierDifferenceExpansionUsed : Bool
round694InnerFourHelicityMultiplierDifferenceExpansionUsed = true

round694GlobalNestedPairSumIsFourGlobalCommutatorPairSum : Bool
round694GlobalNestedPairSumIsFourGlobalCommutatorPairSum = true

round694DivisionUsed : Bool
round694DivisionUsed = false

round694IntroducesEstimate : Bool
round694IntroducesEstimate = false

round694OrbitContributionCancellationClosed : Bool
round694OrbitContributionCancellationClosed = false

round694ClayPromotion : Bool
round694ClayPromotion = false

round694UnitWeightedNestedCellIsFourLiteralR230CommutatorsIsTrue :
  round694UnitWeightedNestedCellIsFourLiteralR230Commutators ≡ true
round694UnitWeightedNestedCellIsFourLiteralR230CommutatorsIsTrue = refl

round694GlobalNestedPairSumIsFourGlobalCommutatorPairSumIsTrue :
  round694GlobalNestedPairSumIsFourGlobalCommutatorPairSum ≡ true
round694GlobalNestedPairSumIsFourGlobalCommutatorPairSumIsTrue = refl

round694DivisionUsedIsFalse :
  round694DivisionUsed ≡ false
round694DivisionUsedIsFalse = refl

round694IntroducesEstimateIsFalse :
  round694IntroducesEstimate ≡ false
round694IntroducesEstimateIsFalse = refl

round694OrbitContributionCancellationClosedIsFalse :
  round694OrbitContributionCancellationClosed ≡ false
round694OrbitContributionCancellationClosedIsFalse = refl

round694ClayPromotionIsFalse :
  round694ClayPromotion ≡ false
round694ClayPromotionIsFalse = refl
