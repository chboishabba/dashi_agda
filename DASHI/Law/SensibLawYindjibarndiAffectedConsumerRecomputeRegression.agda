module DASHI.Law.SensibLawYindjibarndiAffectedConsumerRecomputeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawYindjibarndiAffectedConsumerRecomputeExact as A

yunupinguStillReopensYindjibarndi :
  A.yunupinguDeltaReopensYindjibarndi
    A.canonicalYindjibarndiAffectedConsumerBoundary
  ≡ true
yunupinguStillReopensYindjibarndi = refl

yunupinguStillReopensSharedAuthorityConsumer :
  A.yunupinguDeltaReopensSharedAuthorityConsumer
    A.canonicalYindjibarndiAffectedConsumerBoundary
  ≡ true
yunupinguStillReopensSharedAuthorityConsumer = refl

maboStillReopensYindjibarndi :
  A.maboDeltaReopensYindjibarndi
    A.canonicalYindjibarndiAffectedConsumerBoundary
  ≡ true
maboStillReopensYindjibarndi = refl

maboStillReopensSpecificConsumer :
  A.maboDeltaReopensMaboSpecificConsumer
    A.canonicalYindjibarndiAffectedConsumerBoundary
  ≡ true
maboStillReopensSpecificConsumer = refl

pabaiStillDoesNotReopenByAdjacency :
  A.pabaiReopensByAdjacency
    A.canonicalYindjibarndiAffectedConsumerBoundary
  ≡ false
pabaiStillDoesNotReopenByAdjacency = refl

munkaraStillDoesNotReopenByAdjacency :
  A.munkaraReopensByAdjacency
    A.canonicalYindjibarndiAffectedConsumerBoundary
  ≡ false
munkaraStillDoesNotReopenByAdjacency = refl

recomputeStillDoesNotCreateTruth :
  A.recomputeCreatesClaimTruth
    A.canonicalYindjibarndiAffectedConsumerBoundary
  ≡ false
recomputeStillDoesNotCreateTruth = refl

pabaiCannotAcquireYunupinguFanoutWithoutDependency :
  A.Recompute A.pabaiControl A.yunupinguAcquisition → ⊥
pabaiCannotAcquireYunupinguFanoutWithoutDependency =
  A.pabaiDoesNotRecomputeForYunupingu
