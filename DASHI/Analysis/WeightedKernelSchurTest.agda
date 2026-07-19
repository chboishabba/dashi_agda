module DASHI.Analysis.WeightedKernelSchurTest where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Weighted Schur-test surface for a concrete finite kernel.
--
-- A certificate is indexed by the actual kernel and weight functions.  This is
-- intentional: constants measured on a coarse projection cannot be silently
-- reused for a different pair-incidence operator.
------------------------------------------------------------------------

record WeightedKernelData
    {r c s : Level}
    (Row : Set r)
    (Col : Set c)
    (Scalar : Set s) : Set (lsuc (r ⊔ c ⊔ s)) where
  field
    kernel : Row → Col → Scalar
    rowWeight : Row → Scalar
    colWeight : Col → Scalar

open WeightedKernelData public

record WeightedSchurLaws
    {r c s : Level}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : WeightedKernelData Row Col Scalar) : Set (lsuc (r ⊔ c ⊔ s)) where
  field
    VectorIn : Set c
    VectorOut : Set r

    applyKernel : VectorIn → VectorOut
    inputEnergy : VectorIn → Scalar
    outputEnergy : VectorOut → Scalar

    _≤_ : Scalar → Scalar → Set s
    _⊗_ : Scalar → Scalar → Scalar

    rowConstant : Scalar
    columnConstant : Scalar

    rowWeightedBound : Set (r ⊔ c ⊔ s)
    columnWeightedBound : Set (r ⊔ c ⊔ s)

    weightedSchurEstimate :
      rowWeightedBound →
      columnWeightedBound →
      ∀ input →
      _≤_
        (outputEnergy (applyKernel input))
        (_⊗_ rowConstant (_⊗_ columnConstant (inputEnergy input)))

open WeightedSchurLaws public

record WeightedKernelSchurCertificate
    {r c s : Level}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : WeightedKernelData Row Col Scalar)
    (L : WeightedSchurLaws K) : Set (lsuc (r ⊔ c ⊔ s)) where
  field
    rowBound : rowWeightedBound L
    columnBound : columnWeightedBound L

open WeightedKernelSchurCertificate public

weightedOperatorProduct :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    {K : WeightedKernelData Row Col Scalar} →
  WeightedSchurLaws K →
  Scalar
weightedOperatorProduct L =
  _⊗_ L (rowConstant L) (columnConstant L)

weightedKernelBound :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : WeightedKernelData Row Col Scalar)
    (L : WeightedSchurLaws K)
    (C : WeightedKernelSchurCertificate K L)
    (input : VectorIn L) →
  _≤_ L
    (outputEnergy L (applyKernel L input))
    (_⊗_ L (weightedOperatorProduct L) (inputEnergy L input))
weightedKernelBound K L C =
  weightedSchurEstimate L (rowBound C) (columnBound C)

record KernelIdentityMatch
    {r c s : Level}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (concrete candidate : WeightedKernelData Row Col Scalar) :
    Set (r ⊔ c ⊔ s) where
  field
    kernelMatches : kernel concrete ≡ kernel candidate
    rowWeightsMatch : rowWeight concrete ≡ rowWeight candidate
    colWeightsMatch : colWeight concrete ≡ colWeight candidate

open KernelIdentityMatch public