module DASHI.Information.PNFMPFullRankTemporalNonIdentificationExact where

-- Original DASHI exact finite FULL-RANK covariance negative control.
-- The four distinct 2-dimensional observations are ordered differently
-- without changing their row multiset. Their sample covariance is the
-- POSITIVE-DEFINITE diagonal (1/3,1/3), unlike an earlier singular toy.
-- They still have different first-coordinate lag-one product sums.
-- No empirical IID/MP null, clinical inference or probability theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Information.PNFMPTemporalOrderingNonIdentificationExact as Time
import DASHI.Information.PNFMPStaticGramTemporalNonIdentificationExact as Prior
import DASHI.Information.PNFMPObserverNonPromotionWeldExact as Observer
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Information.PNFSpectralGeometry as Spectrum

-- The columns swap their time ordering in the second scenario:
-- alternating rows: (0,0),(1,0),(0,1),(1,1)
-- clustered rows:   (0,0),(0,1),(1,0),(1,1)
-- Every row occurs once, so all static moments are identical.
opposite : Time.TimeOrder → Time.TimeOrder
opposite Time.alternating = Time.clustered
opposite Time.clustered = Time.alternating

entry : Time.TimeOrder → Time.FourSample → Prior.Column → Nat
entry h row Prior.firstColumn = Time.sample h row
entry h row Prior.secondColumn = Time.sample (opposite h) row

total : Time.TimeOrder → Prior.Column → Nat
total h c = entry h Time.first c + entry h Time.second c +
            entry h Time.third c + entry h Time.fourth c

rawGram : Time.TimeOrder → Prior.Column → Prior.Column → Nat
rawGram h a b =
  entry h Time.first a * entry h Time.first b +
  entry h Time.second a * entry h Time.second b +
  entry h Time.third a * entry h Time.third b +
  entry h Time.fourth a * entry h Time.fourth b

-- All columns have total 2; Gram entries are 2 on diagonal, 1 off.
sameTotal : (c : Prior.Column) →
  total Time.alternating c ≡ total Time.clustered c
sameTotal Prior.firstColumn = refl
sameTotal Prior.secondColumn = refl

sameGram : (a b : Prior.Column) →
  rawGram Time.alternating a b ≡ rawGram Time.clustered a b
sameGram Prior.firstColumn Prior.firstColumn = refl
sameGram Prior.firstColumn Prior.secondColumn = refl
sameGram Prior.secondColumn Prior.firstColumn = refl
sameGram Prior.secondColumn Prior.secondColumn = refl

bothDiagonalRawGramTwo :
  rawGram Time.alternating Prior.firstColumn Prior.firstColumn ≡ 2
bothDiagonalRawGramTwo = refl

offDiagonalRawGramOne :
  rawGram Time.alternating Prior.firstColumn Prior.secondColumn ≡ 1
offDiagonalRawGramOne = refl

-- The integer numerator of unbiased covariance for n=4 is
-- 4*G_ab - S_a*S_b. It is 4 for each diagonal and 0 off diagonal,
-- so dividing by n(n-1)=12 gives C=diag(1/3,1/3).
diagonalCentredNumerator :
  4 * rawGram Time.alternating Prior.firstColumn Prior.firstColumn ≡
  4 + total Time.alternating Prior.firstColumn *
      total Time.alternating Prior.firstColumn
diagonalCentredNumerator = refl

offDiagonalCentredNumerator :
  4 * rawGram Time.alternating Prior.firstColumn Prior.secondColumn ≡
  total Time.alternating Prior.firstColumn *
    total Time.alternating Prior.secondColumn
offDiagonalCentredNumerator = refl

equalCentredCovarianceCrossProduct :
  (a b : Prior.Column) →
  4 * rawGram Time.alternating a b +
    total Time.clustered a * total Time.clustered b
  ≡
  4 * rawGram Time.clustered a b +
    total Time.alternating a * total Time.alternating b
equalCentredCovarianceCrossProduct Prior.firstColumn Prior.firstColumn = refl
equalCentredCovarianceCrossProduct Prior.firstColumn Prior.secondColumn = refl
equalCentredCovarianceCrossProduct Prior.secondColumn Prior.firstColumn = refl
equalCentredCovarianceCrossProduct Prior.secondColumn Prior.secondColumn = refl

stats : Time.TimeOrder → Prior.TwoColumnSufficientStatistics
stats h = Prior.two-column-statistics
  (total h Prior.firstColumn)
  (total h Prior.secondColumn)
  (rawGram h Prior.firstColumn Prior.firstColumn)
  (rawGram h Prior.firstColumn Prior.secondColumn)
  (rawGram h Prior.secondColumn Prior.firstColumn)
  (rawGram h Prior.secondColumn Prior.secondColumn)

equalFullRankStaticStatistics :
  stats Time.alternating ≡ stats Time.clustered
equalFullRankStaticStatistics = refl

fullRankStaticMomentsCannotDetermineLag :
  NF.NonFactorabilityWitness stats Time.lagOneProducts
fullRankStaticMomentsCannotDetermineLag =
  NF.nonFactorabilityWitness Time.alternating Time.clustered
    equalFullRankStaticStatistics Time.differentLagOne

anyFullRankCovarianceRechartStillLosesLag :
  ∀ {Chart : Set}
  (map : Prior.TwoColumnSufficientStatistics → Chart) →
  NF.FactorsThrough (λ h → map (stats h)) Time.lagOneProducts → ⊥
anyFullRankCovarianceRechartStillLosesLag map =
  NF.rechartingCannotRecoverErasedPhenomenon
    map fullRankStaticMomentsCannotDetermineLag

actualMPClassifierStillLosesLag :
  (K : Spectrum.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : Spectrum.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (estimate : Prior.TwoColumnSufficientStatistics →
    Spectrum.ScalarStructure.Scalar K) →
  NF.FactorsThrough
    (Observer.mpClassOfObserver K C classifier stats estimate)
    Time.lagOneProducts → ⊥
actualMPClassifierStillLosesLag K C classifier estimate =
  Observer.mpRechartCannotRecoverErasedOutcome
    K C classifier stats Time.lagOneProducts
    fullRankStaticMomentsCannotDetermineLag estimate
