module DASHI.Physics.Closure.NSPeriodicFinitePythagoreanSum where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicLerayBiotSavartNormReduction as Pythagorean
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite-sum transport of modewise Pythagorean identities.
--
-- Galerkin cutoffs are finite.  If every mode splits into projected and
-- complementary squared norms, then the full cutoff sum has the same split.
-- Nonnegative modewise complements sum to a nonnegative global complement,
-- yielding cutoff-level Leray/Biot-Savart contractivity.
------------------------------------------------------------------------

sumBy :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  (Item → Scalar A) → List Item → Scalar A
sumBy {A = A} f [] = zero A
sumBy {A = A} f (x ∷ xs) = _+_ A (f x) (sumBy f xs)

interchangeFiniteFour :
  (A : AbsorptionArithmetic) →
  ∀ a b c d →
  _+_ A (_+_ A a b) (_+_ A c d)
  ≡
  _+_ A (_+_ A a c) (_+_ A b d)
interchangeFiniteFour A a b c d =
  trans
    (addAssociative A a b (_+_ A c d))
    (trans
      (cong
        (λ middle → _+_ A a middle)
        (trans
          (sym (addAssociative A b c d))
          (trans
            (cong (λ left → _+_ A left d)
              (addCommutative A b c))
            (addAssociative A c b d))))
      (sym (addAssociative A a c (_+_ A b d))))

record ModewisePythagoreanFamily
    {i : Level}
    (A : AbsorptionArithmetic)
    (Item : Set i) : Set (lsuc i) where
  field
    input output complement : Item → Scalar A

    complementNonnegative : ∀ item →
      _≤_ A (zero A) (complement item)

    modewiseSplit : ∀ item →
      input item ≡ _+_ A (output item) (complement item)

open ModewisePythagoreanFamily public

sumByNonnegative :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i}
    (f : Item → Scalar A) →
  (∀ item → _≤_ A (zero A) (f item)) →
  ∀ items → _≤_ A (zero A) (sumBy f items)
sumByNonnegative {A = A} f nonnegative [] = ≤-refl A
sumByNonnegative {A = A} f nonnegative (x ∷ xs) =
  subst
    (λ lower → _≤_ A lower (_+_ A (f x) (sumBy f xs)))
    (addZeroLeft A (zero A))
    (additionMonotone A
      (nonnegative x)
      (sumByNonnegative f nonnegative xs))

sumByPythagoreanSplit :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  (F : ModewisePythagoreanFamily A Item) →
  ∀ items →
  sumBy (input F) items
  ≡
  _+_ A
    (sumBy (output F) items)
    (sumBy (complement F) items)
sumByPythagoreanSplit {A = A} F [] =
  sym (addZeroLeft A (zero A))
sumByPythagoreanSplit {A = A} F (x ∷ xs) =
  trans
    (cong
      (λ tail → _+_ A (input F x) tail)
      (sumByPythagoreanSplit F xs))
    (trans
      (cong
        (λ head →
          _+_ A head
            (_+_ A
              (sumBy (output F) xs)
              (sumBy (complement F) xs)))
        (modewiseSplit F x))
      (interchangeFiniteFour A
        (output F x)
        (complement F x)
        (sumBy (output F) xs)
        (sumBy (complement F) xs)))

finitePythagoreanInputs :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  (F : ModewisePythagoreanFamily A Item) →
  (items : List Item) →
  Pythagorean.PythagoreanOperatorBoundInputs A
finitePythagoreanInputs F items = record
  { inputNormSquared = sumBy (input F) items
  ; outputNormSquared = sumBy (output F) items
  ; complementNormSquared = sumBy (complement F) items
  ; complementNonnegative =
      sumByNonnegative
        (complement F)
        (complementNonnegative F)
        items
  ; pythagoreanSplit = sumByPythagoreanSplit F items
  }

finitePythagoreanOperatorContractive :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  (F : ModewisePythagoreanFamily A Item) →
  ∀ items →
  _≤_ A
    (sumBy (output F) items)
    (sumBy (input F) items)
finitePythagoreanOperatorContractive F items =
  Pythagorean.pythagoreanOperatorIsContractive
    (finitePythagoreanInputs F items)

------------------------------------------------------------------------
-- Status: finite Fourier-sum transport is checked for arbitrary Galerkin mode
-- lists.  The remaining real-carrier work is modewise complement
-- nonnegativity and identification of the literal sums with official norms.
------------------------------------------------------------------------

finitePythagoreanSumLevel : ProofLevel
finitePythagoreanSumLevel = machineChecked
