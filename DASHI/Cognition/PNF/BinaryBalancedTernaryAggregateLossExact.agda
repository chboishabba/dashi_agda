module DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact where

------------------------------------------------------------------------
-- REPO-NATIVE CROSS-POLLINATION
--
-- This module composes existing boundaries rather than identifying their
-- carriers:
--
-- * EpistemicTritBalancedTernarySeparationExact:
--     unresolved is not definitionally balanced-ternary zero;
-- * DialecticCubieTetralemmaExact:
--     binary decision policy on a balanced digit is not canonical;
-- * TernaryComparisonSynthesisExact:
--     9 = diagonal 3 + directed disagreement 6 and synthesis retains the
--     comparison boundary;
-- * RepresentationChartInvariant:
--     1/2, 0.5, 50%, 3/6, and binary 0.1 are presentations of one invariant
--     rational point, not different values.
--
-- The new result is the exact many-to-one composition:
-- ternary comparison -> declared binary decisions -> accept-count aggregate.
-- The count erases disagreement direction.  No CLT is required for this loss;
-- a later probabilistic theorem may study concentration of the already-lossy
-- statistic without reopening its fine fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.DialecticCubieTetralemmaExact as Cubie
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Sheet
import DASHI.Foundations.RepresentationChartInvariant as Chart
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Governance.EpistemicTritBalancedTernarySeparationExact as Separation
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Comparison

------------------------------------------------------------------------
-- Cardinality three alone does not identify epistemic and geometric ternary.
------------------------------------------------------------------------

unresolvedEncodingRemainsPolicyIndexed :
  Separation.encodeWithPolicy Separation.neutralUnresolvedPolicy
    Separation.Epistemic.unresolved ≡ BT.zeroDigit
  × Separation.encodeWithPolicy Separation.negativeUnresolvedPolicy
    Separation.Epistemic.unresolved ≡ BT.neg
  × Separation.encodeWithPolicy Separation.positiveUnresolvedPolicy
    Separation.Epistemic.unresolved ≡ BT.pos
unresolvedEncodingRemainsPolicyIndexed = Separation.unresolvedEncodingDependsOnPolicy

------------------------------------------------------------------------
-- Two legitimate binary projections of the same balanced-ternary digit.
------------------------------------------------------------------------

positiveOnlyRejectsNegative :
  Cubie.positiveOnlyDecision BT.neg ≡ Sheet.bit0
positiveOnlyRejectsNegative = Cubie.positiveOnlyRejectsNegative

nonzeroAcceptsNegative :
  Cubie.nonzeroDecision BT.neg ≡ Sheet.bit1
nonzeroAcceptsNegative = Cubie.nonzeroAcceptsNegative

binaryPolicyChangesMeaningAtSameFineDigit :
  Cubie.positiveOnlyDecision BT.neg
  ≡ Cubie.nonzeroDecision BT.neg → ⊥
binaryPolicyChangesMeaningAtSameFineDigit = Cubie.decisionPoliciesDifferOnNegative

------------------------------------------------------------------------
-- Premature 9 -> 4 -> 3 collapse.
------------------------------------------------------------------------

BalancedComparison9 : Set
BalancedComparison9 = BT.BalancedDigit × BT.BalancedDigit

BinaryComparison4 : Set
BinaryComparison4 = Sheet.Bit2 × Sheet.Bit2

binaryProjectPositiveOnly : BalancedComparison9 → BinaryComparison4
binaryProjectPositiveOnly (left , right) =
  Cubie.positiveOnlyDecision left , Cubie.positiveOnlyDecision right

acceptCount : BinaryComparison4 → Nat
acceptCount (Sheet.bit0 , Sheet.bit0) = 0
acceptCount (Sheet.bit0 , Sheet.bit1) = 1
acceptCount (Sheet.bit1 , Sheet.bit0) = 1
acceptCount (Sheet.bit1 , Sheet.bit1) = 2

forwardDisagreement : BalancedComparison9
forwardDisagreement = BT.pos , BT.neg

reverseDisagreement : BalancedComparison9
reverseDisagreement = BT.neg , BT.pos

forwardBinary :
  binaryProjectPositiveOnly forwardDisagreement ≡ (Sheet.bit1 , Sheet.bit0)
forwardBinary = refl

reverseBinary :
  binaryProjectPositiveOnly reverseDisagreement ≡ (Sheet.bit0 , Sheet.bit1)
reverseBinary = refl

binaryDirectionStillDistinct :
  binaryProjectPositiveOnly forwardDisagreement
  ≡ binaryProjectPositiveOnly reverseDisagreement → ⊥
binaryDirectionStillDistinct ()

aggregateErasesDisagreementDirection :
  acceptCount (binaryProjectPositiveOnly forwardDisagreement)
  ≡ acceptCount (binaryProjectPositiveOnly reverseDisagreement)
aggregateErasesDisagreementDirection = refl

countAggregateIsManyToOne :
  acceptCount (Sheet.bit1 , Sheet.bit0)
  ≡ acceptCount (Sheet.bit0 , Sheet.bit1)
  × ((Sheet.bit1 , Sheet.bit0) ≡ (Sheet.bit0 , Sheet.bit1) → ⊥)
countAggregateIsManyToOne = refl , (λ ())

------------------------------------------------------------------------
-- Reuse rather than restate the 3/6/9/27 comparison geometry.
------------------------------------------------------------------------

comparisonNineDimension : Comparison.comparisonDimension ≡ 9
comparisonNineDimension = Comparison.comparisonDimensionIsNine

synthesisTwentySevenDimension : Comparison.synthesisChoiceDimension ≡ 27
synthesisTwentySevenDimension = Comparison.synthesisChoiceDimensionIsTwentySeven

comparisonBoundarySurvivesSynthesis :
  (left right synthesis : Comparison.Base.TriTruth) →
  Comparison.comparisonOfSynthesis
    (Comparison.makeSynthesisChoice left right synthesis)
  ≡ (left , right)
comparisonBoundarySurvivesSynthesis = Comparison.comparisonBoundaryRetained

------------------------------------------------------------------------
-- The half point is an invariant presentation fibre, not a truth label.
------------------------------------------------------------------------

halfAsDecimalStillOneHalf :
  Chart.RatioEquivalent Chart.fiveTenths Chart.oneHalf
halfAsDecimalStillOneHalf = Chart.fiveTenthsIsOneHalf

halfAsPercentStillOneHalf :
  Chart.RatioEquivalent Chart.fiftyHundredths Chart.oneHalf
halfAsPercentStillOneHalf = Chart.fiftyHundredthsIsOneHalf

halfAsBinaryChartStillOneHalf :
  Chart.RatioEquivalent Chart.binaryPointOne Chart.oneHalf
halfAsBinaryChartStillOneHalf = Chart.binaryPointOneIsOneHalf

------------------------------------------------------------------------
-- Three distinguished Bernoulli/complement positions after centering.
-- This is a finite affine-complement model only; it does not claim an analytic
-- logistic function or a probabilistic limit theorem has been constructed.
------------------------------------------------------------------------

data BernoulliDistinguishedPoint : Set where
  probabilityZero probabilityHalf probabilityOne : BernoulliDistinguishedPoint

complementPoint : BernoulliDistinguishedPoint → BernoulliDistinguishedPoint
complementPoint probabilityZero = probabilityOne
complementPoint probabilityHalf = probabilityHalf
complementPoint probabilityOne = probabilityZero

centredPoint : BernoulliDistinguishedPoint → SSP.SSPTrit
centredPoint probabilityZero = SSP.sspNegOne
centredPoint probabilityHalf = SSP.sspZero
centredPoint probabilityOne = SSP.sspPosOne

halfIsComplementFixed : complementPoint probabilityHalf ≡ probabilityHalf
halfIsComplementFixed = refl

centredComplementIsStrictAntipode :
  (point : BernoulliDistinguishedPoint) →
  centredPoint (complementPoint point)
  ≡ DASHI.Foundations.BalancedTernaryAntipodalOrbitExact.strictAntipode
      (centredPoint point)
centredComplementIsStrictAntipode probabilityZero = refl
centredComplementIsStrictAntipode probabilityHalf = refl
centredComplementIsStrictAntipode probabilityOne = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record BinaryBalancedTernaryAggregateBoundary : Set where
  field
    balancedZeroDefinitionallyMeansEpistemicUnresolved : Bool
    binaryZeroDefinitionallyMeansWorldFalse : Bool
    acceptCountRetainsDisagreementDirection : Bool
    halfPointDefinitionallyMeansIndecision : Bool
    aggregateConcentrationWouldReopenFineFibre : Bool
    analyticLogisticTheoremConstructedHere : Bool

canonicalBinaryBalancedTernaryAggregateBoundary :
  BinaryBalancedTernaryAggregateBoundary
canonicalBinaryBalancedTernaryAggregateBoundary = record
  { balancedZeroDefinitionallyMeansEpistemicUnresolved = false
  ; binaryZeroDefinitionallyMeansWorldFalse = false
  ; acceptCountRetainsDisagreementDirection = false
  ; halfPointDefinitionallyMeansIndecision = false
  ; aggregateConcentrationWouldReopenFineFibre = false
  ; analyticLogisticTheoremConstructedHere = false
  }
