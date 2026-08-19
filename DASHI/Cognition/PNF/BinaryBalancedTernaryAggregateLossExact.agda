module DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact where

------------------------------------------------------------------------
-- REPO-NATIVE CROSS-POLLINATION
--
-- Reuses the existing balanced-ternary decision policies and 3/6/9/27
-- comparison geometry.  The exact many-to-one composition is:
--
--   ternary comparison 9 -> declared binary decisions 4 -> accept-count 3.
--
-- The count erases disagreement direction.  A Boolean decision remains a valid
-- consumer projection when declared; it is not a reconstruction of the fine
-- signed carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.DialecticCubieTetralemmaExact as Cubie
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Sheet
import DASHI.Foundations.RepresentationChartInvariant as Chart
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Governance.EpistemicTritBalancedTernarySeparationExact as Separation
import DASHI.Ontology.EpistemicTrit as Epistemic
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Comparison

unresolvedEncodingRemainsPolicyIndexed :
  Separation.encodeWithPolicy Separation.neutralUnresolvedPolicy Epistemic.unresolved ≡ BT.zeroDigit
  × Separation.encodeWithPolicy Separation.negativeUnresolvedPolicy Epistemic.unresolved ≡ BT.neg
  × Separation.encodeWithPolicy Separation.positiveUnresolvedPolicy Epistemic.unresolved ≡ BT.pos
unresolvedEncodingRemainsPolicyIndexed = Separation.unresolvedEncodingDependsOnPolicy

positiveOnlyRejectsNegative : Cubie.positiveOnlyDecision BT.neg ≡ Sheet.bit0
positiveOnlyRejectsNegative = Cubie.positiveOnlyRejectsNegative

nonzeroAcceptsNegative : Cubie.nonzeroDecision BT.neg ≡ Sheet.bit1
nonzeroAcceptsNegative = Cubie.nonzeroAcceptsNegative

binaryPolicyChangesMeaningAtSameFineDigit :
  Cubie.positiveOnlyDecision BT.neg ≡ Cubie.nonzeroDecision BT.neg → ⊥
binaryPolicyChangesMeaningAtSameFineDigit = Cubie.decisionPoliciesDifferOnNegative

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

binaryDirectionStillDistinct :
  binaryProjectPositiveOnly forwardDisagreement
  ≡ binaryProjectPositiveOnly reverseDisagreement → ⊥
binaryDirectionStillDistinct ()

aggregateErasesDisagreementDirection :
  acceptCount (binaryProjectPositiveOnly forwardDisagreement)
  ≡ acceptCount (binaryProjectPositiveOnly reverseDisagreement)
aggregateErasesDisagreementDirection = refl

countAggregateIsManyToOne :
  acceptCount (Sheet.bit1 , Sheet.bit0) ≡ acceptCount (Sheet.bit0 , Sheet.bit1)
  × ((Sheet.bit1 , Sheet.bit0) ≡ (Sheet.bit0 , Sheet.bit1) → ⊥)
countAggregateIsManyToOne = refl , (λ ())

comparisonNineDimension : Comparison.comparisonDimension ≡ 9
comparisonNineDimension = Comparison.comparisonDimensionIsNine

synthesisTwentySevenDimension : Comparison.synthesisChoiceDimension ≡ 27
synthesisTwentySevenDimension = Comparison.synthesisChoiceDimensionIsTwentySeven

comparisonBoundarySurvivesSynthesis :
  (left right synthesis : Base.TriTruth) →
  Comparison.comparisonOfSynthesis (Comparison.makeSynthesisChoice left right synthesis)
  ≡ (left , right)
comparisonBoundarySurvivesSynthesis = Comparison.comparisonBoundaryRetained

halfAsDecimalStillOneHalf : Chart.RatioEquivalent Chart.fiveTenths Chart.oneHalf
halfAsDecimalStillOneHalf = Chart.fiveTenthsIsOneHalf

halfAsPercentStillOneHalf : Chart.RatioEquivalent Chart.fiftyHundredths Chart.oneHalf
halfAsPercentStillOneHalf = Chart.fiftyHundredthsIsOneHalf

halfAsBinaryChartStillOneHalf : Chart.RatioEquivalent Chart.binaryPointOne Chart.oneHalf
halfAsBinaryChartStillOneHalf = Chart.binaryPointOneIsOneHalf

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
  centredPoint (complementPoint point) ≡ Orbit.strictAntipode (centredPoint point)
centredComplementIsStrictAntipode probabilityZero = refl
centredComplementIsStrictAntipode probabilityHalf = refl
centredComplementIsStrictAntipode probabilityOne = refl

record BinaryBalancedTernaryAggregateBoundary : Set where
  field
    balancedZeroDefinitionallyMeansEpistemicUnresolved : Bool
    binaryZeroDefinitionallyMeansWorldFalse : Bool
    acceptCountRetainsDisagreementDirection : Bool
    halfPointDefinitionallyMeansIndecision : Bool
    aggregateConcentrationWouldReopenFineFibre : Bool

canonicalBinaryBalancedTernaryAggregateBoundary : BinaryBalancedTernaryAggregateBoundary
canonicalBinaryBalancedTernaryAggregateBoundary = record
  { balancedZeroDefinitionallyMeansEpistemicUnresolved = false
  ; binaryZeroDefinitionallyMeansWorldFalse = false
  ; acceptCountRetainsDisagreementDirection = false
  ; halfPointDefinitionallyMeansIndecision = false
  ; aggregateConcentrationWouldReopenFineFibre = false
  }
