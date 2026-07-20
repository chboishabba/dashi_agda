{-# OPTIONS --safe #-}
module DASHI.Core.KernelRenormalization where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

------------------------------------------------------------------------
-- Three deliberately distinct renormalisation contracts.

record StrictRenormalizationSquare
  {Fine Coarse : Set}
  (fineKernel : Fine → Fine)
  (coarseKernel : Coarse → Coarse)
  (renormalize : Fine → Coarse) : Set where
  field
    commutes :
      ∀ s →
      renormalize (fineKernel s)
        ≡ coarseKernel (renormalize s)
open StrictRenormalizationSquare public

record QuotientRenormalizationSquare
  {Fine Coarse Quotient : Set}
  (fineKernel : Fine → Fine)
  (coarseKernel : Coarse → Coarse)
  (renormalize : Fine → Coarse)
  (quotient : Coarse → Quotient) : Set where
  field
    commutes-after-quotient :
      ∀ s →
      quotient (renormalize (fineKernel s))
        ≡ quotient (coarseKernel (renormalize s))
open QuotientRenormalizationSquare public

record BoundedDefectRenormalizationSquare
  {Fine Coarse : Set}
  (fineKernel : Fine → Fine)
  (coarseKernel : Coarse → Coarse)
  (renormalize : Fine → Coarse)
  (distance : Coarse → Coarse → Nat)
  (epsilon : Nat) : Set where
  field
    bounded-defect :
      ∀ s →
      distance
        (renormalize (fineKernel s))
        (coarseKernel (renormalize s))
        ≤ epsilon
open BoundedDefectRenormalizationSquare public

strict⇒quotient :
  ∀ {Fine Coarse Quotient : Set}
    {fineKernel : Fine → Fine}
    {coarseKernel : Coarse → Coarse}
    {renormalize : Fine → Coarse}
    (quotient : Coarse → Quotient) →
  StrictRenormalizationSquare fineKernel coarseKernel renormalize →
  QuotientRenormalizationSquare
    fineKernel coarseKernel renormalize quotient
strict⇒quotient quotient strict = record
  { commutes-after-quotient = λ s →
      Agda.Builtin.Equality.cong quotient
        (StrictRenormalizationSquare.commutes strict s)
  }
