module DASHI.Analysis.WeightedKernelSchurTest where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

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

------------------------------------------------------------------------
-- Keep the exact bracketing supplied by `weightedSchurEstimate`.
--
-- No associativity law is part of `WeightedSchurLaws`, so the expression
--
--   rowConstant ⊗ (columnConstant ⊗ inputEnergy)
--
-- cannot definitionally be replaced by
--
--   (rowConstant ⊗ columnConstant) ⊗ inputEnergy.
--
-- Concrete semiring instances may prove that reassociation separately.
------------------------------------------------------------------------

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
    (_⊗_ L
      (rowConstant L)
      (_⊗_ L (columnConstant L) (inputEnergy L input)))
weightedKernelBound K L C =
  weightedSchurEstimate L (rowBound C) (columnBound C)

record WeightedProductAssociativity
    {r c s : Level}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    {K : WeightedKernelData Row Col Scalar}
    (L : WeightedSchurLaws K) : Set s where
  field
    multiplyAssociative :
      ∀ a b c →
      _⊗_ L (_⊗_ L a b) c ≡ _⊗_ L a (_⊗_ L b c)

open WeightedProductAssociativity public

weightedKernelProductBound :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : WeightedKernelData Row Col Scalar)
    (L : WeightedSchurLaws K)
    (A : WeightedProductAssociativity L)
    (C : WeightedKernelSchurCertificate K L)
    (input : VectorIn L) →
  _≤_ L
    (outputEnergy L (applyKernel L input))
    (_⊗_ L (weightedOperatorProduct L) (inputEnergy L input))
weightedKernelProductBound K L A C input =
  subst
    (λ bound → _≤_ L (outputEnergy L (applyKernel L input)) bound)
    (sym (multiplyAssociative A
      (rowConstant L)
      (columnConstant L)
      (inputEnergy L input)))
    (weightedKernelBound K L C input)

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

------------------------------------------------------------------------
-- Exact action semantics.
--
-- `WeightedSchurLaws` deliberately leaves vectors abstract.  Consequently the
-- bare existence of `applyKernel` does not by itself prove that the action is
-- assembled from `kernel K`.  This companion record closes that authority seam
-- without breaking existing Schur instances: a concrete vector model supplies
-- one evaluator for matrix entries and proves that `applyKernel` is exactly that
-- evaluator applied to the declared kernel.
------------------------------------------------------------------------

record ExactKernelAction
    {r c s : Level}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : WeightedKernelData Row Col Scalar)
    (L : WeightedSchurLaws K) : Set (lsuc (r ⊔ c ⊔ s)) where
  field
    evaluateEntries :
      (Row → Col → Scalar) →
      VectorIn L →
      VectorOut L

    applyKernelMatchesEntries :
      ∀ input →
      applyKernel L input ≡
      evaluateEntries (kernel K) input

open ExactKernelAction public

exactKernelActionTransport :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    {K : WeightedKernelData Row Col Scalar}
    {L : WeightedSchurLaws K}
    (A : ExactKernelAction K L)
    (candidateEntries : Row → Col → Scalar) →
  kernel K ≡ candidateEntries →
  ∀ input →
  applyKernel L input ≡
  evaluateEntries A candidateEntries input
exactKernelActionTransport A candidateEntries entriesMatch input =
  subst
    (λ entries →
      applyKernel L input ≡
      evaluateEntries A entries input)
    entriesMatch
    (applyKernelMatchesEntries A input)

exactKernelActionTransportByIdentity :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    {K candidate : WeightedKernelData Row Col Scalar}
    {L : WeightedSchurLaws K} →
  (A : ExactKernelAction K L) →
  KernelIdentityMatch K candidate →
  ∀ input →
  applyKernel L input ≡
  evaluateEntries A (kernel candidate) input
exactKernelActionTransportByIdentity {candidate = candidate} A M =
  exactKernelActionTransport A (kernel candidate) (kernelMatches M)
