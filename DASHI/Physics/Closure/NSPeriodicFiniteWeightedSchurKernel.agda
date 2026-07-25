module DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal weighted row and column sums for a finite far-low kernel.
--
-- This gives the Schur lane one exact owner for the kernel and both sums.  It
-- also proves that extending a Galerkin cutoff by rows or columns on which the
-- kernel vanishes does not change either sum.  Thus cutoff independence cannot
-- be asserted using a different enumeration or a hidden extra multiplicity.
------------------------------------------------------------------------

record WeightedKernel
    {r c : Level}
    (A : AbsorptionArithmetic)
    (Row : Set r)
    (Column : Set c) : Set (r Level.⊔ c) where
  field
    entryMajorant : Row → Column → Scalar A

open WeightedKernel public

sumBy :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  (Item → Scalar A) → List Item → Scalar A
sumBy {A = A} f [] = zero A
sumBy {A = A} f (x ∷ xs) = _+_ A (f x) (sumBy f xs)

weightedRowSum :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  WeightedKernel A Row Column → Row → List Column → Scalar A
weightedRowSum K row columns = sumBy (entryMajorant K row) columns

weightedColumnSum :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  WeightedKernel A Row Column → Column → List Row → Scalar A
weightedColumnSum K column rows = sumBy (λ row → entryMajorant K row column) rows

sumByAppend :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i}
    (f : Item → Scalar A) →
  ∀ left right →
  sumBy f (left ++ right) ≡ _+_ A (sumBy f left) (sumBy f right)
sumByAppend {A = A} f [] right = sym (addZeroLeft A (sumBy f right))
sumByAppend {A = A} f (x ∷ xs) right =
  trans
    (cong (λ tail → _+_ A (f x) tail) (sumByAppend f xs right))
    (sym (addAssociative A (f x) (sumBy f xs) (sumBy f right)))

sumByAllZero :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i}
    (f : Item → Scalar A) →
  (∀ item → f item ≡ zero A) →
  ∀ items → sumBy f items ≡ zero A
sumByAllZero {A = A} f zeroAt [] = refl
sumByAllZero {A = A} f zeroAt (x ∷ xs) =
  trans
    (cong₂ (_+_ A) (zeroAt x) (sumByAllZero f zeroAt xs))
    (addZeroLeft A (zero A))
  where
  cong₂ : ∀ {X Y Z : Set} (g : X → Y → Z) {x x′ y y′} →
    x ≡ x′ → y ≡ y′ → g x y ≡ g x′ y′
  cong₂ g refl refl = refl

rowSumZeroExtensionInvariant :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  (K : WeightedKernel A Row Column) →
  ∀ row oldColumns newColumns →
  (∀ column → entryMajorant K row column ≡ zero A) →
  weightedRowSum K row (oldColumns ++ newColumns)
  ≡ weightedRowSum K row oldColumns
rowSumZeroExtensionInvariant {A = A} K row oldColumns newColumns newZero =
  trans
    (sumByAppend (entryMajorant K row) oldColumns newColumns)
    (trans
      (cong (λ tail → _+_ A (weightedRowSum K row oldColumns) tail)
        (sumByAllZero (entryMajorant K row) newZero newColumns))
      (addZeroRight A (weightedRowSum K row oldColumns)))
  where
  addZeroRight : ∀ x → _+_ A x (zero A) ≡ x
  addZeroRight x =
    trans (addCommutative A x (zero A)) (addZeroLeft A x)

columnSumZeroExtensionInvariant :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  (K : WeightedKernel A Row Column) →
  ∀ column oldRows newRows →
  (∀ row → entryMajorant K row column ≡ zero A) →
  weightedColumnSum K column (oldRows ++ newRows)
  ≡ weightedColumnSum K column oldRows
columnSumZeroExtensionInvariant {A = A} K column oldRows newRows newZero =
  rowSumZeroExtensionInvariant
    (record { entryMajorant = λ column row → entryMajorant K row column })
    column oldRows newRows newZero

finiteWeightedSchurKernelLevel : ProofLevel
finiteWeightedSchurKernelLevel = machineChecked
