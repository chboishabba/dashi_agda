module DASHI.Information.PNFMPTemporalOrderingNonIdentificationExact where

-- Original DASHI finite null-model negative control, synthetic only.
-- Two distinct time orders have exactly the same mean and uncentred
-- second moment (thus same scalar covariance), but different lag-one
-- product statistics. Consequently a *static covariance* cannot by
-- itself identify the temporal-dependence assumptions of iid MP.
-- No probability distribution, actual clinical or financial panel,
-- p-value, or empirical trend is supplied.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.IntersectionalNonFactorability as NF

-- Two time series, each a permutation of the same multiset (0,0,1,1).
data TimeOrder : Set where
  alternating clustered : TimeOrder

data FourSample : Set where
  first second third fourth : FourSample

sample : TimeOrder → FourSample → Nat
sample alternating first = 0
sample alternating second = 1
sample alternating third = 0
sample alternating fourth = 1
sample clustered first = 0
sample clustered second = 0
sample clustered third = 1
sample clustered fourth = 1

sampleTotal : TimeOrder → Nat
sampleTotal a =
  sample a first + sample a second +
  sample a third + sample a fourth

sampleSquareTotal : TimeOrder → Nat
sampleSquareTotal a =
  (sample a first * sample a first) +
  (sample a second * sample a second) +
  (sample a third * sample a third) +
  (sample a fourth * sample a fourth)

lagOneProducts : TimeOrder → Nat
lagOneProducts a =
  (sample a first * sample a second) +
  (sample a second * sample a third) +
  (sample a third * sample a fourth)

staticMoments : TimeOrder → Nat × Nat
staticMoments a = sampleTotal a , sampleSquareTotal a

sameStaticMoments :
  staticMoments alternating ≡ staticMoments clustered
sameStaticMoments = refl

differentLagOne :
  lagOneProducts alternating ≡ lagOneProducts clustered → ⊥
differentLagOne ()

staticMomentsCannotIdentifyTemporalStructure :
  NF.NonFactorabilityWitness staticMoments lagOneProducts
staticMomentsCannotIdentifyTemporalStructure =
  NF.nonFactorabilityWitness
    alternating clustered sameStaticMoments differentLagOne

noStaticCovarianceMomentOnlyAutocorrelationDecoder :
  NF.FactorsThrough staticMoments lagOneProducts → ⊥
noStaticCovarianceMomentOnlyAutocorrelationDecoder =
  NF.witnessRulesOutEveryFlatFactorisation
    staticMomentsCannotIdentifyTemporalStructure

-- Thresholding, spectral cleaning and every other static recharting
-- inherit this information-theoretic limitation: information omitted
-- by the static moments cannot be reconstructed by post-processing.
arbitraryStaticRechartCannotRecoverLag :
  ∀ {Chart : Set} (rechart : (Nat × Nat) → Chart) →
  NF.FactorsThrough
    (λ history → rechart (staticMoments history))
    lagOneProducts → ⊥
arbitraryStaticRechartCannotRecoverLag rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart staticMomentsCannotIdentifyTemporalStructure

-- Static moments are 2 and 2 for both histories, while the lag-one
-- sums are 0 vs 1. The latter is a discrete diagnostic of ordering, not
-- evidence for or against a stochastic iid data generating process.
alternatingLagZero : lagOneProducts alternating ≡ 0
alternatingLagZero = refl

clusteredLagOne : lagOneProducts clustered ≡ 1
clusteredLagOne = refl
