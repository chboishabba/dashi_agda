module DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorBonySumRound121Exact where

------------------------------------------------------------------------
-- ROUND121 / SIGN-PRESERVING BONY DECOMPOSITION OF THE PURE COMMUTATOR SUM
--
-- Round120 closes the physical shared-output partner identity before absolute
-- values: the paired external cell is a pure multiplier-difference object.
-- The next analytic step must preserve that sign information while routing the
-- complete residual carrier into the mature four-way Bony geometry.
--
-- This module proves the exact finite algebra needed for that route. For ANY
-- complex-valued cell functional V and ANY incidence list xs,
--
--   sum_xs V
--     = sum_LH V + sum_HL V + sum_HH->low V + sum_comparable V,
--
-- where each right-hand list is the existing literal Round63 filter.  This is
-- an identity of signed sums, not a triangle-inequality estimate, so no
-- cardinality/Wiener factor is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony

foldComplex :
  ∀ {r} {F : C3.RealField r} →
  (Physical.PhysicalTriadIncidence → C3.Complex F) →
  List Physical.PhysicalTriadIncidence → C3.Complex F
foldComplex {F = F} value [] = C3.complexZero F
foldComplex value (tau ∷ rest) =
  C3.complexAdd (value tau) (foldComplex value rest)

fourWayBonyFold :
  ∀ {r} {F : C3.RealField r} →
  (Physical.PhysicalTriadIncidence → C3.Complex F) →
  List Physical.PhysicalTriadIncidence → C3.Complex F
fourWayBonyFold value items =
  C3.complexAdd
    (C3.complexAdd
      (foldComplex value (Bony.filterBonyTag Bony.lhTag items))
      (foldComplex value (Bony.filterBonyTag Bony.hlTag items)))
    (C3.complexAdd
      (foldComplex value (Bony.filterBonyTag Bony.hhToLowTag items))
      (foldComplex value (Bony.filterBonyTag Bony.comparableTag items)))

foldComplexEqualsFourWayBonyFold :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex F)
    (items : List Physical.PhysicalTriadIncidence) →
  foldComplex value items ≡ fourWayBonyFold value items
foldComplexEqualsFourWayBonyFold {F = F} value [] =
  R.solve 0
    (((R.Κ (C3.complexZero F) R.⊕ R.Κ (C3.complexZero F))
      R.⊕
      (R.Κ (C3.complexZero F) R.⊕ R.Κ (C3.complexZero F)))
      R.⊜ R.Κ (C3.complexZero F))
    refl
  where module R = Ring.Solver F
foldComplexEqualsFourWayBonyFold {F = F} value (tau ∷ rest)
  with Bony.bonyTag tau
... | Bony.lhTag =
  trans
    (cong (C3.complexAdd (value tau))
      (foldComplexEqualsFourWayBonyFold value rest))
    (R.solve 5
      (λ x a b c d →
        (x R.⊕ ((a R.⊕ b) R.⊕ (c R.⊕ d)))
        R.⊜ (((x R.⊕ a) R.⊕ b) R.⊕ (c R.⊕ d)))
      refl
      (value tau)
      (foldComplex value (Bony.filterBonyTag Bony.lhTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hlTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hhToLowTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.comparableTag rest)))
  where module R = Ring.Solver F
... | Bony.hlTag =
  trans
    (cong (C3.complexAdd (value tau))
      (foldComplexEqualsFourWayBonyFold value rest))
    (R.solve 5
      (λ x a b c d →
        (x R.⊕ ((a R.⊕ b) R.⊕ (c R.⊕ d)))
        R.⊜ ((a R.⊕ (x R.⊕ b)) R.⊕ (c R.⊕ d)))
      refl
      (value tau)
      (foldComplex value (Bony.filterBonyTag Bony.lhTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hlTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hhToLowTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.comparableTag rest)))
  where module R = Ring.Solver F
... | Bony.hhToLowTag =
  trans
    (cong (C3.complexAdd (value tau))
      (foldComplexEqualsFourWayBonyFold value rest))
    (R.solve 5
      (λ x a b c d →
        (x R.⊕ ((a R.⊕ b) R.⊕ (c R.⊕ d)))
        R.⊜ ((a R.⊕ b) R.⊕ ((x R.⊕ c) R.⊕ d)))
      refl
      (value tau)
      (foldComplex value (Bony.filterBonyTag Bony.lhTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hlTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hhToLowTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.comparableTag rest)))
  where module R = Ring.Solver F
... | Bony.comparableTag =
  trans
    (cong (C3.complexAdd (value tau))
      (foldComplexEqualsFourWayBonyFold value rest))
    (R.solve 5
      (λ x a b c d →
        (x R.⊕ ((a R.⊕ b) R.⊕ (c R.⊕ d)))
        R.⊜ ((a R.⊕ b) R.⊕ (c R.⊕ (x R.⊕ d))))
      refl
      (value tau)
      (foldComplex value (Bony.filterBonyTag Bony.lhTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hlTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.hhToLowTag rest))
      (foldComplex value (Bony.filterBonyTag Bony.comparableTag rest)))
  where module R = Ring.Solver F

round121SignedFourWayBonySumDecompositionClosed : Bool
round121SignedFourWayBonySumDecompositionClosed = true

round121CellwiseAbsoluteValueRequiredBeforeBonySum : Bool
round121CellwiseAbsoluteValueRequiredBeforeBonySum = false

round121ClasswiseCriticalCommutatorPaymentClosed : Bool
round121ClasswiseCriticalCommutatorPaymentClosed = false

round121SignedFourWayBonySumDecompositionClosedIsTrue :
  round121SignedFourWayBonySumDecompositionClosed ≡ true
round121SignedFourWayBonySumDecompositionClosedIsTrue = refl

round121CellwiseAbsoluteValueRequiredBeforeBonySumIsFalse :
  round121CellwiseAbsoluteValueRequiredBeforeBonySum ≡ false
round121CellwiseAbsoluteValueRequiredBeforeBonySumIsFalse = refl

round121ClasswiseCriticalCommutatorPaymentClosedIsFalse :
  round121ClasswiseCriticalCommutatorPaymentClosed ≡ false
round121ClasswiseCriticalCommutatorPaymentClosedIsFalse = refl
