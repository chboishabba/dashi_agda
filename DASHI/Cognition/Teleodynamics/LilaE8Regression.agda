module DASHI.Cognition.Teleodynamics.LilaE8Regression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Algebra.Trit.E8RootEnumeration as E8
import DASHI.Cognition.Teleodynamics.LilaE8QuantizerExact as Q
import DASHI.Cognition.Teleodynamics.LilaE8AttentionBiasExact as B

internalE8GeneratorHas240Entries : E8.combinedIndexedRootsLength ≡ 240
internalE8GeneratorHas240Entries = E8.combinedIndexedRootsLengthIs240

externalShapeAdapterRecords112Plus128 :
  Q.integerFamilyCount Q.canonicalE8RootShapeAdapter ≡ 112
externalShapeAdapterRecords112Plus128 = refl

externalShapeAdapterRecordsHalf128 :
  Q.halfFamilyCount Q.canonicalE8RootShapeAdapter ≡ 128
externalShapeAdapterRecordsHalf128 = refl

zeroScaleBiasReducesToBaseline :
  B.biasedScore B.demoZeroScaleBias ≡ B.baselineScore B.demoZeroScaleBias
zeroScaleBiasReducesToBaseline = B.zeroScaleReducesToBaseline B.demoZeroScaleBias

rootUseDoesNotEstablishEquivariance :
  B.e8EquivarianceEstablished B.canonicalE8AttentionBoundary ≡ false
rootUseDoesNotEstablishEquivariance = refl

forwardQuantizerDoesNotIdentifyStraightThroughEstimator :
  Q.forwardMapEqualsOptimizerEstimator Q.canonicalQuantizerBoundary ≡ false
forwardQuantizerDoesNotIdentifyStraightThroughEstimator = refl
