module DASHI.Analysis.FiniteWeightedKernelSums where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Exact finite row/column sums for a weighted rectangular kernel.
------------------------------------------------------------------------

fold : ∀ {a} {A : Set a} → (A → A → A) → A → List A → A
fold combine unit [] = unit
fold combine unit (x ∷ xs) = combine x (fold combine unit xs)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

record FiniteWeightedKernel
    {r c s : Level}
    (Row : Set r)
    (Col : Set c)
    (Scalar : Set s) : Set (lsuc (r ⊔ c ⊔ s)) where
  field
    rows : List Row
    columns : List Col

    zero : Scalar
    add : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    kernel : Row → Col → Scalar
    rowWeight : Row → Scalar
    colWeight : Col → Scalar

open FiniteWeightedKernel public

sumScalars :
  ∀ {r c s} {Row : Set r} {Col : Set c} {Scalar : Set s} →
  FiniteWeightedKernel Row Col Scalar →
  List Scalar → Scalar
sumScalars K = fold (add K) (zero K)

rowWeightedSum :
  ∀ {r c s} {Row : Set r} {Col : Set c} {Scalar : Set s} →
  (K : FiniteWeightedKernel Row Col Scalar) →
  Row → Scalar
rowWeightedSum K row =
  sumScalars K
    (map (λ col → multiply K (kernel K row col) (colWeight K col))
      (columns K))

columnWeightedSum :
  ∀ {r c s} {Row : Set r} {Col : Set c} {Scalar : Set s} →
  (K : FiniteWeightedKernel Row Col Scalar) →
  Col → Scalar
columnWeightedSum K col =
  sumScalars K
    (map (λ row → multiply K (kernel K row col) (rowWeight K row))
      (rows K))

record FiniteWeightedSchurCertificate
    {r c s : Level}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (K : FiniteWeightedKernel Row Col Scalar) : Set (lsuc (r ⊔ c ⊔ s)) where
  field
    rowConstant : Scalar
    columnConstant : Scalar

    rowBound :
      ∀ row →
      _≤_ K
        (rowWeightedSum K row)
        (multiply K rowConstant (rowWeight K row))

    columnBound :
      ∀ col →
      _≤_ K
        (columnWeightedSum K col)
        (multiply K columnConstant (colWeight K col))

open FiniteWeightedSchurCertificate public

record FiniteKernelIdentityMatch
    {r c s : Level}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (concrete candidate : FiniteWeightedKernel Row Col Scalar) :
    Set (r ⊔ c ⊔ s) where
  field
    rowsMatch : rows concrete ≡ rows candidate
    columnsMatch : columns concrete ≡ columns candidate
    kernelMatches : kernel concrete ≡ kernel candidate
    rowWeightsMatch : rowWeight concrete ≡ rowWeight candidate
    colWeightsMatch : colWeight concrete ≡ colWeight candidate

open import Relation.Binary.PropositionalEquality using (_≡_)
open FiniteKernelIdentityMatch public
