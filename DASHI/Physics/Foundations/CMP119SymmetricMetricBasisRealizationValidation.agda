{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as R

tenSlotsGenerateOrderedBasis :
  R.orderedPairBasisIsGeneratedFromTenSlots ≡ true
tenSlotsGenerateOrderedBasis = refl

sixteenBasisVectorsNotIndependent :
  R.sixteenIndependentMetricBasisVectorsRequired ≡ false
sixteenBasisVectorsNotIndependent = refl

slotEmbeddingStillPhysical :
  R.symmetricSlotToCMP119PerturbationStillRequired ≡ true
slotEmbeddingStillPhysical = refl
