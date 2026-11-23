module DASHI.Analysis.RHPrimeAperturePuncturedFactorChartExact where

-- RH P0 / original-source punctured-27 geometric INDEXING bridge.
-- Reuse original 27 and 26 owners; DO NOT create a second cube:
--   Punctured27NineSheetBridgeExact: 26 = lower9 + middle8 + upper9
--   IbrahimTernary27OriginTraceless26AlbertShapeBidiExact: 27=1+26
--   ExceptionalAlbertFreudenthalResidualExact: J dimension 27,
--     shape J0=26, F4 dimension 52 = 2*26.
--   HyperfabricPunctured27Projective13OrientationExact:
--     26 oriented points / 13 antipodal axes.
--
-- The ORIGINAL RH annihilator has 18 actual real quadratic factors
-- (9 at frequency r and 9 at 2r), and 4 real quartics (pole frequencies
-- t±r, t±2r = 15r,17r,14r,18r). Each quartic is bounded
-- coefficientwise by TWO virtual quadratic factors of weight 1/k².
-- These 26 MAJORANT slots are indexed by the ORIGINAL punctured cube.
-- This is an oriented bookkeeping chart, NOT a factorization of the
-- quartics into real positive quadratics, nor an Albert multiplication
-- or F4 representation, nor a kernel proof of an RH theorem.
--
-- Its rational envelope polynomial is checked by exact SymPy/Fraction
-- in scripts/check_rh_p0_punctured27_geometric_majorant_20261123.py.
-- Source-written Agda; Agda compiler/kernel has NOT been run.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as P9
import DASHI.Mathematics.Symmetry.Punctured27NineSheetBridgeExact as Original
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Analysis.RHQuartic163840DyadicTailHXIntertwinerExact as DyadicTail

-- The four punctured central-plane antipodal pairs are assigned the four
-- original pole frequency branches. This assignment is a CHOSEN chart.
data PoleFrequency : Set where
  frequency14 frequency15 frequency17 frequency18 : PoleFrequency

poleInteger : PoleFrequency → Nat
poleInteger frequency14 = 14
poleInteger frequency15 = 15
poleInteger frequency17 = 17
poleInteger frequency18 = 18

poleAxis : P9.PuncturedNineSheet → PoleFrequency
poleAxis P9.negativeFirstAxis = frequency14
poleAxis P9.positiveFirstAxis = frequency14
poleAxis P9.negativeSecondAxis = frequency15
poleAxis P9.positiveSecondAxis = frequency15
poleAxis P9.negativeEqualDiagonal = frequency17
poleAxis P9.positiveEqualDiagonal = frequency17
poleAxis P9.negativeOppositeDiagonal = frequency18
poleAxis P9.positiveOppositeDiagonal = frequency18

-- Denominator 1 means weight 1 at r; denominator 4 means 1/4 at 2r;
-- middle-plane denominators k² are from the coefficientwise pole
-- quartic majorant (1+z/k²)². Sign remains as the original site.
factorDenominator : Original.Punctured27Chart → Nat
factorDenominator (Original.lowerSheet x y) = 1
factorDenominator (Original.upperSheet x y) = 4
factorDenominator (Original.middleNonzero p) =
  poleInteger (poleAxis p) * poleInteger (poleAxis p)

-- The source's 27 ambient coefficients consist of one distinguished
-- normalised constant coefficient q0=1 and 26 others. This is ONLY
-- a dimension/index statement, not a canonical grade→site isomorphism.
originalScalarAndTwentySix : 27 ≡ 1 + 26
originalScalarAndTwentySix = Exceptional.albertSplitsScalarPlusTraceless

originalPuncturedThreeSlices : 26 ≡ 9 + 8 + 9
originalPuncturedThreeSlices = refl

sourceOrderTwiceTwentySix : 52 ≡ 2 * 26
sourceOrderTwiceTwentySix = Exceptional.fFourIsTwoTracelessAlbertDimensions

unitLowerSheet : (x y : SSP.SSPTrit) →
  factorDenominator (Original.lowerSheet x y) ≡ 1
unitLowerSheet x y = refl

quarterUpperSheet : (x y : SSP.SSPTrit) →
  factorDenominator (Original.upperSheet x y) ≡ 4
quarterUpperSheet x y = refl

-- Opposite signs within the central eight retain one common frequency
-- DENOMINATOR while still remaining TWO DISTINCT ORIENTED POINTS.
centralFirstAntipodes :
  factorDenominator (Original.middleNonzero P9.negativeFirstAxis) ≡
  factorDenominator (Original.middleNonzero P9.positiveFirstAxis)
centralFirstAntipodes = refl

centralSecondAntipodes :
  factorDenominator (Original.middleNonzero P9.negativeSecondAxis) ≡
  factorDenominator (Original.middleNonzero P9.positiveSecondAxis)
centralSecondAntipodes = refl

centralEqualDiagonalAntipodes :
  factorDenominator (Original.middleNonzero P9.negativeEqualDiagonal) ≡
  factorDenominator (Original.middleNonzero P9.positiveEqualDiagonal)
centralEqualDiagonalAntipodes = refl

centralOppositeDiagonalAntipodes :
  factorDenominator (Original.middleNonzero P9.negativeOppositeDiagonal) ≡
  factorDenominator (Original.middleNonzero P9.positiveOppositeDiagonal)
centralOppositeDiagonalAntipodes = refl

central14 : factorDenominator (Original.middleNonzero P9.positiveFirstAxis) ≡ 196
central14 = refl

central15 : factorDenominator (Original.middleNonzero P9.positiveSecondAxis) ≡ 225
central15 = refl

central17 : factorDenominator (Original.middleNonzero P9.positiveEqualDiagonal) ≡ 289
central17 = refl

central18 : factorDenominator (Original.middleNonzero P9.positiveOppositeDiagonal) ≡ 324
central18 = refl


------------------------------------------------------------------------
-- P0 constants audit: different SAME-NUMBER geometries, NO false action.
--
-- 32768 = 8^5 = 2^15 is already the original SOURCE dyadic tail
-- chart capacity, with a retained continuous residual theta.
-- The separate low-tech t>=32768 analytic sufficient threshold was
-- OPTIONAL and is superseded by an exact source-target floor from
-- t>=19440 (r>=1215). No t↔dyadic-action identification follows.
--
-- 208 = 26*8 coincides with the punctured cube's 26 source sites
-- and the middle plane's eight oriented points, but its prior
-- analytical 1/208 was an EQUAL SPLIT of a chosen 1/8 error
-- budget across 26 polynomial terms: change the bump width and
-- this allocation changes. No invariant 208-dimensional action.
--
-- The full nonuniform punctured-shell E2 coefficients E_j and the
-- positive *weighted polynomial* H(r) replace equal term splitting.
-- Proved with source exact fractions by local regression; neither
-- H(r) nor a zeta sign theorem is kernel-welded here.
------------------------------------------------------------------------

puncturedMiddleCount : Nat
puncturedMiddleCount = 8

originalTwentySixSlotCount : Nat
originalTwentySixSlotCount = 26

formerEqualSplitCount : Nat
formerEqualSplitCount = originalTwentySixSlotCount * puncturedMiddleCount

old208Is26TimesEight : formerEqualSplitCount ≡ 208
old208Is26TimesEight = refl

-- The original dyadic chart has its own independent analytic owner,
-- not the new coefficient-bound chart.
sourceDyadicFlag32768 : Nat
sourceDyadicFlag32768 = DyadicTail.sourceDyadicCapacity

sourceDyadicFlagIs32768 : sourceDyadicFlag32768 ≡ 32768
sourceDyadicFlagIs32768 = DyadicTail.sourceDyadicCapacityIs32768

sourceTailCutoffMatchesPuncturedEight :
  DyadicTail.tailCutoff ≡ puncturedMiddleCount
sourceTailCutoffMatchesPuncturedEight = refl

sourceDyadicPowerMatchesTail :
  DyadicTail.tailCutoffFifthPower ≡ sourceDyadicFlag32768
sourceDyadicPowerMatchesTail =
  DyadicTail.tailCutoffFifthPowerIsSourceDyadicCapacity

-- The two actual same-integer owners agree on 32768, but
-- the source explicitly BLOCKS identifying dyadic x3 with Monster 3B.
-- Equally no RH proof is licensed from the integer equality.


------------------------------------------------------------------------
-- P0 E2: user-identified 4*256 = ORIGINAL q=16 dyadic-cell index 1024.
--
-- The derivatives and q-tail have DIFFERENT SOURCE OWNERS:
--  * source C∞ prime flat-top b_p has two ±log p centres and two
--    interval-indicator jumps each => FOUR signed boundary jumps.
--    Previous first box has halfwidth 1/256, so its TV derivative
--    cost 4*256=1024.
--  * ORIGINAL RHQuartic163840DyadicTailHXIntertwinerExact already has
--    q=16 at dyadic cell index 1024 among 32768 continuous-residual
--    tail cells; 32768=32*1024.
-- This is a positive same-number BIDI/attribution bridge only.
-- Changing smoothing widths changes the derivative bound but NOT
-- the original tail-cell index: no false RH group/action or Monster 3B.
--
-- NEW chosen E2 source: reserve ONE original dyadic-index unit 1/1024
-- for an infinite residual sequence of box halfwidths 2^-n/1024,
-- n>=1; give the other SEVEN units to 52 equal primary boxes,
-- each halfwidth 7/(52*1024).
-- Total support smoothing halfwidth (7+1)/1024=1/128.
-- The flat-top centred at ±log p starts from the SAME a=3/128
-- indicator, giving support1/32, plateau1/64, mass3/32.
-- New inverse primary width lambda=52*1024/7 is a chosen geometric
-- scale, not equal to the old 256.
--
-- The true old 4E_j factor in the 26-degree source E(x) is the
-- four BOUNDARY-JUMP total-variation factor; there are ALSO four
-- different source prime ports (two primes x two endpoints).
-- Neither identification turns the 26 weighted elementary-symmetric
-- source coefficients into an F4/Albert representation.
--
-- Analytic infinite convolution, all L1 and source positivity bounds
-- are in the mathematical proof ledger, not kernel-checked here.
------------------------------------------------------------------------

originalQSixteenDyadicCellIndex : Nat
originalQSixteenDyadicCellIndex =
  DyadicTail.crossingAtSixteenCellIndex

oldFlatTopSymmetricPrimeCentres : Nat
oldFlatTopSymmetricPrimeCentres = 2

oldFlatTopIndicatorJumpsPerCentre : Nat
oldFlatTopIndicatorJumpsPerCentre = 2

oldFlatTopBoundaryJumps : Nat
oldFlatTopBoundaryJumps =
  oldFlatTopSymmetricPrimeCentres
    * oldFlatTopIndicatorJumpsPerCentre

oldFlatTopFirstBoxReciprocalHalfwidth : Nat
oldFlatTopFirstBoxReciprocalHalfwidth = 256

oldFlatTopSecondDerivativeTVBoundInteger : Nat
oldFlatTopSecondDerivativeTVBoundInteger =
  oldFlatTopBoundaryJumps * oldFlatTopFirstBoxReciprocalHalfwidth

originalFourTimes256IsQSixteenCellIndex :
  oldFlatTopSecondDerivativeTVBoundInteger
    ≡ originalQSixteenDyadicCellIndex
originalFourTimes256IsQSixteenCellIndex = refl

sourceFullDyadicCapacityAsThirtyTwoCrossings :
  32 * originalQSixteenDyadicCellIndex
    ≡ DyadicTail.sourceDyadicCapacity
sourceFullDyadicCapacityAsThirtyTwoCrossings =
  DyadicTail.crossingScaledBackToDyadicCapacity

sourceAnnihilatorEvenOrder : Nat
sourceAnnihilatorEvenOrder =
  2 * originalTwentySixSlotCount

sourceAnnihilatorEvenOrderIs52 :
  sourceAnnihilatorEvenOrder ≡ 52
sourceAnnihilatorEvenOrderIs52 = refl

rebalancedPrimaryBoxCount : Nat
rebalancedPrimaryBoxCount = sourceAnnihilatorEvenOrder

rebalancedPrimarySmoothingUnits : Nat
rebalancedPrimarySmoothingUnits = 7

rebalancedInfiniteTailSmoothingUnits : Nat
rebalancedInfiniteTailSmoothingUnits = 1

rebalancedTotalSmoothingUnits : Nat
rebalancedTotalSmoothingUnits =
  rebalancedPrimarySmoothingUnits
    + rebalancedInfiniteTailSmoothingUnits

rebalancedEightUnitsAreTheSourcePuncturedMiddleCount :
  rebalancedTotalSmoothingUnits ≡ puncturedMiddleCount
rebalancedEightUnitsAreTheSourcePuncturedMiddleCount = refl

-- Rational lambda = this numerator / 7.
rebalancedInversePrimaryBoxNumerator : Nat
rebalancedInversePrimaryBoxNumerator =
  rebalancedPrimaryBoxCount * originalQSixteenDyadicCellIndex

rebalancedLambdaNumeratorIs53248 :
  rebalancedInversePrimaryBoxNumerator ≡ 53248
rebalancedLambdaNumeratorIs53248 = refl

sourceTwoPrimeLabels : Nat
sourceTwoPrimeLabels = 2

sourceTwoOriginalEndpoints : Nat
sourceTwoOriginalEndpoints = 2

sourceIndependentPrimePortCount : Nat
sourceIndependentPrimePortCount =
  sourceTwoPrimeLabels * sourceTwoOriginalEndpoints

sourceIndependentPortCountIsFour :
  sourceIndependentPrimePortCount ≡ 4
sourceIndependentPortCountIsFour = refl

-- Equal cardinality DOES NOT identify two factors of four:
-- the b_p indicator's 4 distributional jumps are NOT the four
-- independent (prime,endpoint) source port labels.
sourceBoundaryGradeBookkeeping : Nat
sourceBoundaryGradeBookkeeping =
  oldFlatTopBoundaryJumps * originalTwentySixSlotCount

sourcePortGradeBookkeeping : Nat
sourcePortGradeBookkeeping =
  sourceIndependentPrimePortCount * originalTwentySixSlotCount

sourceBoundaryBookkeepingIs104 :
  sourceBoundaryGradeBookkeeping ≡ 104
sourceBoundaryBookkeepingIs104 = refl

sourcePortBookkeepingIs104 :
  sourcePortGradeBookkeeping ≡ 104
sourcePortBookkeepingIs104 = refl
