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
