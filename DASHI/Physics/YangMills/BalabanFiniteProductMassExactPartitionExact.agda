module DASHI.Physics.YangMills.BalabanFiniteProductMassExactPartitionExact where

------------------------------------------------------------------------
-- FINITE PRODUCT OF A MASS-EXACT ONE-SITE PARTITION
--
-- Given one finite probability partition
--
--   cells : List Cell
--   mass  : Cell -> R
--   sum mass = 1,
--
-- the canonical vectorPower enumeration of N cells carries product mass
--
--   mass(c_1,...,c_N) = prod_i mass(c_i)
--
-- and the total product mass is again exactly one.
--
-- This removes the SU(2)^N product-measure bookkeeping from the Eq.(1.71)
-- quadrature frontier: only the one-site SU(2) partition remains geometric.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (map; _++_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_;
   +-identityʳ; *-distribˡ-+; mulZeroʳ; mulOneʳ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums

realSumAppend :
  ∀ {A : Set}
    (left right : List A)
    (value : A → ℝ) →
  Sums.realSum (left ++ right) value
  ≡
  Sums.realSum left value +ℝ Sums.realSum right value
realSumAppend [] right value =
  sym (+-identityʳ (Sums.realSum right value))
realSumAppend (x ∷ xs) right value =
  cong
    (value x +ℝ_)
    (realSumAppend xs right value)

realSumMap :
  ∀ {A B : Set}
    (f : A → B)
    (values : List A)
    (value : B → ℝ) →
  Sums.realSum (map f values) value
  ≡
  Sums.realSum values (λ x → value (f x))
realSumMap f [] value = refl
realSumMap f (x ∷ xs) value =
  cong
    (value (f x) +ℝ_)
    (realSumMap f xs value)

realSumConcatMap :
  ∀ {A B : Set}
    (f : A → List B)
    (values : List A)
    (value : B → ℝ) →
  Sums.realSum (Product.concatMap f values) value
  ≡
  Sums.realSum values
    (λ x → Sums.realSum (f x) value)
realSumConcatMap f [] value = refl
realSumConcatMap f (x ∷ xs) value =
  trans
    (realSumAppend
      (f x)
      (Product.concatMap f xs)
      value)
    (cong
      (Sums.realSum (f x) value +ℝ_)
      (realSumConcatMap f xs value))

realSumLeftScaleExact :
  ∀ {A : Set}
    (scale : ℝ)
    (values : List A)
    (value : A → ℝ) →
  Sums.realSum values (λ x → scale *ℝ value x)
  ≡
  scale *ℝ Sums.realSum values value
realSumLeftScaleExact scale [] value =
  sym (mulZeroʳ scale)
realSumLeftScaleExact scale (x ∷ xs) value =
  trans
    (cong
      (scale *ℝ value x +ℝ_)
      (realSumLeftScaleExact scale xs value))
    (sym
      (*-distribˡ-+
        scale
        (value x)
        (Sums.realSum xs value)))

record OneSiteMassExactPartition (Cell : Set) : Set₁ where
  field
    cells : List Cell
    mass : Cell → ℝ
    massesSumOne :
      Sums.realSum cells mass ≡ 1ℝ

open OneSiteMassExactPartition public

productCells :
  ∀ {Cell : Set} →
  OneSiteMassExactPartition Cell →
  Nat →
  List (Vec.Vec Cell _)
productCells partition dimension =
  Product.vectorPower (cells partition) dimension

productMass :
  ∀ {Cell : Set}
    (partition : OneSiteMassExactPartition Cell)
    {dimension : Nat} →
  Vec.Vec Cell dimension → ℝ
productMass partition Vec.[] = 1ℝ
productMass partition (cell Vec.∷ rest) =
  mass partition cell *ℝ productMass partition rest

productMassesSumOne :
  ∀ {Cell : Set}
    (partition : OneSiteMassExactPartition Cell)
    (dimension : Nat) →
  Sums.realSum
    (Product.vectorPower (cells partition) dimension)
    (productMass partition)
  ≡
  1ℝ
productMassesSumOne partition zero =
  +-identityʳ 1ℝ
productMassesSumOne partition (suc dimension) =
  trans
    (realSumConcatMap
      (λ cell →
        map (Vec._∷_ cell)
          (Product.vectorPower (cells partition) dimension))
      (cells partition)
      (productMass partition))
    (trans
      (Sums.realSumCong
        (cells partition)
        (λ cell →
          trans
            (realSumMap
              (Vec._∷_ cell)
              (Product.vectorPower (cells partition) dimension)
              (productMass partition))
            (trans
              (realSumLeftScaleExact
                (mass partition cell)
                (Product.vectorPower (cells partition) dimension)
                (productMass partition))
              (trans
                (cong
                  (mass partition cell *ℝ_)
                  (productMassesSumOne partition dimension))
                (mulOneʳ (mass partition cell))))))
      )
      (massesSumOne partition))

productMassExactPartitionCompilerLevel : ProofLevel
productMassExactPartitionCompilerLevel = machineChecked

productMassNormalizationCompilerLevel : ProofLevel
productMassNormalizationCompilerLevel = machineChecked

-- Only the one-site compact-group geometry remains:
-- build a literal finite SU(2) partition and identify its exact Haar masses.
literalOneSiteSU2MassPartitionLevel : ProofLevel
literalOneSiteSU2MassPartitionLevel = conditional
