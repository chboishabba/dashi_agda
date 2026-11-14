module DASHI.Information.PNFMPStaticGramTemporalNonIdentificationExact where

-- Exact multivariate extension of PNFMPTemporalOrderingNonIdentificationExact.
-- Two 4×2 observation matrices contain the SAME four rows in different
-- temporal order. They have equal full column totals and all 2×2 raw
-- Gram entries, hence equal sample-centred covariance (with fixed n).
-- Their lag-one time statistic differs. No probabilistic iid hypothesis,
-- empirical MP null or promotion is produced by this finite countermodel.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Information.PNFMPTemporalOrderingNonIdentificationExact as Time
import DASHI.Information.PNFMPObserverNonPromotionWeldExact as MPObserver
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Information.PNFSpectralGeometry as PNF

data Column : Set where
  firstColumn secondColumn : Column

-- The second column is the complement of the first; the row multiset
-- is [(0,1),(1,0),(0,1),(1,0)] in either selected time order.
complement : Nat → Nat
complement 0 = 1
complement (suc _) = 0

entry : Time.TimeOrder → Time.FourSample → Column → Nat
entry history row firstColumn = Time.sample history row
entry history row secondColumn = complement (Time.sample history row)

columnTotal : Time.TimeOrder → Column → Nat
columnTotal history col =
  entry history Time.first col + entry history Time.second col +
  entry history Time.third col + entry history Time.fourth col

rawGram : Time.TimeOrder → Column → Column → Nat
rawGram history a b =
  entry history Time.first a * entry history Time.first b +
  entry history Time.second a * entry history Time.second b +
  entry history Time.third a * entry history Time.third b +
  entry history Time.fourth a * entry history Time.fourth b

sameColumnTotals :
  (col : Column) →
  columnTotal Time.alternating col ≡ columnTotal Time.clustered col
sameColumnTotals firstColumn = refl
sameColumnTotals secondColumn = refl

sameEntireRawGram :
  (a b : Column) →
  rawGram Time.alternating a b ≡ rawGram Time.clustered a b
sameEntireRawGram firstColumn firstColumn = refl
sameEntireRawGram firstColumn secondColumn = refl
sameEntireRawGram secondColumn firstColumn = refl
sameEntireRawGram secondColumn secondColumn = refl

-- Four exact moments uniquely determine the symmetric 2×2 sample
-- covariance once n and centering convention are fixed. Rather than
-- assume real division, retain the full integer statistics sufficient
-- to reconstruct that covariance in any ordinary characteristic-0 field.
record TwoColumnSufficientStatistics : Set where
  constructor two-column-statistics
  field
    sumFirst sumSecond : Nat
    gram11 gram12 gram21 gram22 : Nat

open TwoColumnSufficientStatistics public

staticTwoColumnStatistics : Time.TimeOrder → TwoColumnSufficientStatistics
staticTwoColumnStatistics history = two-column-statistics
  (columnTotal history firstColumn)
  (columnTotal history secondColumn)
  (rawGram history firstColumn firstColumn)
  (rawGram history firstColumn secondColumn)
  (rawGram history secondColumn firstColumn)
  (rawGram history secondColumn secondColumn)

equalFullTwoColumnStatistics :
  staticTwoColumnStatistics Time.alternating ≡
  staticTwoColumnStatistics Time.clustered
equalFullTwoColumnStatistics = refl

equalFullGramButDifferentTemporalLag :
  NF.NonFactorabilityWitness
    staticTwoColumnStatistics Time.lagOneProducts
equalFullGramButDifferentTemporalLag =
  NF.nonFactorabilityWitness
    Time.alternating Time.clustered
    equalFullTwoColumnStatistics Time.differentLagOne

-- For any pair of columns, equality of original totals and Gram
-- entries yields exact cross-multiplied equality of the unnormalised
-- centred-covariance expression:
-- n·G_ab - S_a·S_b, with n=4.
-- The equation is expressed over Nat by moving the subtraction terms
-- across the equality, avoiding any assumed field division or negatives.
-- A real/rational sample covariance has the common denominator n(n-1).
sameCentredCovarianceCrossProduct :
  (a b : Column) →
  (4 * rawGram Time.alternating a b +
    columnTotal Time.clustered a * columnTotal Time.clustered b)
  ≡
  (4 * rawGram Time.clustered a b +
    columnTotal Time.alternating a * columnTotal Time.alternating b)
sameCentredCovarianceCrossProduct firstColumn firstColumn = refl
sameCentredCovarianceCrossProduct firstColumn secondColumn = refl
sameCentredCovarianceCrossProduct secondColumn firstColumn = refl
sameCentredCovarianceCrossProduct secondColumn secondColumn = refl

-- In particular no eigenvalue classifier/MP edge applied to those
-- sufficient covariance statistics can recover the erased time order.
noStaticTwoColumnSpectralDecoder :
  NF.FactorsThrough staticTwoColumnStatistics Time.lagOneProducts → ⊥
noStaticTwoColumnSpectralDecoder =
  NF.witnessRulesOutEveryFlatFactorisation
    equalFullGramButDifferentTemporalLag

noRechartedTwoColumnSpectralDecoder :
  ∀ {Spectral : Set}
  (classify : TwoColumnSufficientStatistics → Spectral) →
  NF.FactorsThrough
    (λ h → classify (staticTwoColumnStatistics h))
    Time.lagOneProducts → ⊥
noRechartedTwoColumnSpectralDecoder classify =
  NF.rechartingCannotRecoverErasedPhenomenon
    classify equalFullGramButDifferentTemporalLag

-- Specific sample values: both matrices have column totals (2,2)
-- and Gram [[2,0],[0,2]], yet differ in chronological structure.
totalsExactlyTwo :
  (columnTotal Time.alternating firstColumn ≡ 2)
  × (columnTotal Time.alternating secondColumn ≡ 2)
totalsExactlyTwo = refl , refl

offDiagonalGramZero :
  rawGram Time.alternating firstColumn secondColumn ≡ 0
offDiagonalGramZero = refl

-- This is the actual source-specific MP interface instantiated to the
-- 2-column sufficient statistics above. It imports the generic
-- MPObserver theorem rather than an unmerged PR #1479 source.
twoColumnMPClassificationCannotRecoverTemporalLag :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (estimate : TwoColumnSufficientStatistics →
    PNF.ScalarStructure.Scalar K) →
  NF.FactorsThrough
    (MPObserver.mpClassOfObserver K C classifier
      staticTwoColumnStatistics estimate)
    Time.lagOneProducts → ⊥
twoColumnMPClassificationCannotRecoverTemporalLag
  K C classifier estimate =
  MPObserver.mpRechartCannotRecoverErasedOutcome
    K C classifier
    staticTwoColumnStatistics
    Time.lagOneProducts
    equalFullGramButDifferentTemporalLag
    estimate
