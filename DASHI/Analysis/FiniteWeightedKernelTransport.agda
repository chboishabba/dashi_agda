module DASHI.Analysis.FiniteWeightedKernelTransport where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)

open import DASHI.Analysis.FiniteWeightedKernelSums

------------------------------------------------------------------------
-- Exact transport of a finite weighted Schur certificate when only the kernel
-- evaluator changes and the new evaluator is pointwise equal to the old one.
--
-- This is the representation bridge needed by finite Fourier restrictions:
-- a hand-computed canonical matrix may certify an actual restricted kernel only
-- after pointwise equality has been proved.  No equality of coarse empirical
-- matrices is accepted in place of that theorem.
------------------------------------------------------------------------

replaceKernel :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s} →
  FiniteWeightedKernel Row Col Scalar →
  (Row → Col → Scalar) →
  FiniteWeightedKernel Row Col Scalar
replaceKernel K candidate = record
  { rows = rows K
  ; columns = columns K
  ; zero = zero K
  ; add = add K
  ; multiply = multiply K
  ; _≤_ = _≤_ K
  ; kernel = candidate
  ; rowWeight = rowWeight K
  ; colWeight = colWeight K
  }

mapCong :
  ∀ {a b}
    {A : Set a}
    {B : Set b}
    (left right : A → B) →
  ((x : A) → left x ≡ right x) →
  (xs : List A) →
  map left xs ≡ map right xs
mapCong left right pointwise [] = refl
mapCong left right pointwise (x ∷ xs) =
  cong₂ _∷_
    (pointwise x)
    (mapCong left right pointwise xs)

rowWeightedSumReplaceKernel :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : FiniteWeightedKernel Row Col Scalar)
    (candidate : Row → Col → Scalar) →
  ((row : Row) → (col : Col) →
    candidate row col ≡ kernel K row col) →
  (row : Row) →
  rowWeightedSum (replaceKernel K candidate) row ≡
  rowWeightedSum K row
rowWeightedSumReplaceKernel K candidate kernelMatch row =
  cong (sumScalars K)
    (mapCong
      (λ col → multiply K (candidate row col) (colWeight K col))
      (λ col → multiply K (kernel K row col) (colWeight K col))
      (λ col →
        cong
          (λ value → multiply K value (colWeight K col))
          (kernelMatch row col))
      (columns K))

columnWeightedSumReplaceKernel :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : FiniteWeightedKernel Row Col Scalar)
    (candidate : Row → Col → Scalar) →
  ((row : Row) → (col : Col) →
    candidate row col ≡ kernel K row col) →
  (col : Col) →
  columnWeightedSum (replaceKernel K candidate) col ≡
  columnWeightedSum K col
columnWeightedSumReplaceKernel K candidate kernelMatch col =
  cong (sumScalars K)
    (mapCong
      (λ row → multiply K (candidate row col) (rowWeight K row))
      (λ row → multiply K (kernel K row col) (rowWeight K row))
      (λ row →
        cong
          (λ value → multiply K value (rowWeight K row))
          (kernelMatch row col))
      (rows K))

transportFiniteWeightedSchurCertificate :
  ∀ {r c s}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : FiniteWeightedKernel Row Col Scalar)
    (candidate : Row → Col → Scalar) →
  ((row : Row) → (col : Col) →
    candidate row col ≡ kernel K row col) →
  FiniteWeightedSchurCertificate K →
  FiniteWeightedSchurCertificate (replaceKernel K candidate)
transportFiniteWeightedSchurCertificate K candidate kernelMatch C = record
  { rowConstant = rowConstant C
  ; columnConstant = columnConstant C
  ; rowBound = λ row →
      subst
        (λ lhs →
          _≤_ (replaceKernel K candidate)
            lhs
            (multiply K (rowConstant C) (rowWeight K row)))
        (sym (rowWeightedSumReplaceKernel K candidate kernelMatch row))
        (rowBound C row)
  ; columnBound = λ col →
      subst
        (λ lhs →
          _≤_ (replaceKernel K candidate)
            lhs
            (multiply K (columnConstant C) (colWeight K col)))
        (sym (columnWeightedSumReplaceKernel K candidate kernelMatch col))
        (columnBound C col)
  }
