module DASHI.Physics.Closure.NSTriadKNUniversalFiniteChargeAllocationRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Agda standard-library contributors; DASHI repository contributors.
-- Title: "Exact rational finite geometric envelope for output relocation".
-- Repository formal development, 2026; DOI not applicable.
--
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- DOI: 10.1007/978-3-642-61667-9.
--
-- ROUND77 / UNIVERSAL FINITE CHARGE SUBPARTITION
--
-- The charge-allocation theorem does not need descendant orthogonality.  Every
-- finite reuse family has a canonical rational allocation:
--
--      s_0 = 1/2, s_1 = 1/4, s_2 = 1/8, ...
--      r_j = 1/s_j = 2,4,8,...
--
-- and therefore
--
--      sum_j s_j^2 <= 1.
--
-- This module constructs those AllocationScale witnesses recursively and proves
-- the finite squared-subpartition bound without square roots.  Combining it
-- with `primitiveSubpartitionFundsAllAllocatedCopies` means finite charge reuse
-- can always be made budget-admissible.  The genuine PDE difficulty is no
-- longer existence of an additive/disjoint charge family; it is whether the
-- resulting reciprocal-complexity cost still permits positive FRAME-WEIGHTED
-- propagation excess.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNChargeAllocatedFactorizationRound77Exact as Allocation

half two quarter : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1
quarter = Int.+ 1 / 4

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

quarterNonnegative : 0ℚ ≤ quarter
quarterNonnegative = toWitness {a? = 0ℚ ≤? quarter} _

halfTwoExact : half * two ≡ 1ℚ
halfTwoExact = refl

halfSquareExact : L2.square half ≡ quarter
halfSquareExact = refl

baseAllocation : Allocation.AllocationScale
baseAllocation = Allocation.allocation-scale
  half two halfNonnegative twoNonnegative halfTwoExact

shiftAllocation : Allocation.AllocationScale → Allocation.AllocationScale
shiftAllocation allocation =
  let
    s = Allocation.scale allocation
    r = Allocation.reciprocal allocation
    shiftedScaleNN = ℚP.0≤*0≤ halfNonnegative (Allocation.scaleNonnegative allocation)
    shiftedReciprocalNN = ℚP.0≤*0≤ twoNonnegative (Allocation.reciprocalNonnegative allocation)
    exact : (half * s) * (two * r) ≡ 1ℚ
    exact =
      trans
        (solve (s ∷ r ∷ []))
        (trans
          (cong (_* (s * r)) halfTwoExact)
          (trans
            (cong (1ℚ *_) (Allocation.reciprocalExact allocation))
            (ℚP.*-identityˡ 1ℚ)))
  in
  Allocation.allocation-scale
    (half * s) (two * r)
    shiftedScaleNN shiftedReciprocalNN exact

shiftAllocations : List Allocation.AllocationScale → List Allocation.AllocationScale
shiftAllocations [] = []
shiftAllocations (allocation ∷ rest) =
  shiftAllocation allocation ∷ shiftAllocations rest

shiftScaleSquaresExact : ∀ allocations →
  Allocation.sumScaleSquares (shiftAllocations allocations)
  ≡ quarter * Allocation.sumScaleSquares allocations
shiftScaleSquaresExact [] = refl
shiftScaleSquaresExact (allocation ∷ rest) =
  let
    s = Allocation.scale allocation
    tail = Allocation.sumScaleSquares rest
  in
  trans
    (cong
      (L2.square (half * s) +_)
      (shiftScaleSquaresExact rest))
    (solve (s ∷ tail ∷ []))

geometricAllocations : Nat → List Allocation.AllocationScale
geometricAllocations zero = []
geometricAllocations (suc count) =
  baseAllocation ∷ shiftAllocations (geometricAllocations count)

geometricScaleSquaresRecurrence : ∀ count →
  Allocation.sumScaleSquares (geometricAllocations (suc count))
  ≡ quarter + quarter * Allocation.sumScaleSquares (geometricAllocations count)
geometricScaleSquaresRecurrence count =
  trans
    (cong
      (L2.square half +_)
      (shiftScaleSquaresExact (geometricAllocations count)))
    (cong (_+ (quarter * Allocation.sumScaleSquares (geometricAllocations count)))
      halfSquareExact)

quarterPlusQuarterBelowOne : quarter + quarter ≤ 1ℚ
quarterPlusQuarterBelowOne = toWitness {a? = quarter + quarter ≤? 1ℚ} _

geometricScaleSquaresBelowOne : ∀ count →
  Allocation.sumScaleSquares (geometricAllocations count) ≤ 1ℚ
geometricScaleSquaresBelowOne zero = ℚP.0≤1
geometricScaleSquaresBelowOne (suc count) =
  let
    previousNN =
      Allocation.sumScaleSquaresNonnegative (geometricAllocations count)
    previousBelow = geometricScaleSquaresBelowOne count
    scaledPrevious :
      quarter * Allocation.sumScaleSquares (geometricAllocations count)
      ≤ quarter * 1ℚ
    scaledPrevious =
      L2.nonnegativeProductMonotone
        quarterNonnegative previousNN quarterNonnegative ℚP.0≤1
        ℚP.≤-refl previousBelow
    addQuarter :
      quarter + quarter * Allocation.sumScaleSquares (geometricAllocations count)
      ≤ quarter + quarter * 1ℚ
    addQuarter = ℚP.+-monoʳ-≤ quarter scaledPrevious
    collapseRight : quarter + quarter * 1ℚ ≡ quarter + quarter
    collapseRight = cong (quarter +_) (ℚP.*-identityʳ quarter)
    recurrenceBound :
      quarter + quarter * Allocation.sumScaleSquares (geometricAllocations count)
      ≤ 1ℚ
    recurrenceBound =
      ℚP.≤-trans
        addQuarter
        (subst (_≤ 1ℚ) (sym collapseRight) quarterPlusQuarterBelowOne)
  in
  subst
    (_≤ 1ℚ)
    (sym (geometricScaleSquaresRecurrence count))
    recurrenceBound

universalFiniteChargeSubpartition : ∀ count →
  Allocation.PrimitiveChargeSubpartition (geometricAllocations count)
universalFiniteChargeSubpartition count = record
  { scaleSquaresBelowOne = geometricScaleSquaresBelowOne count }

universalFiniteReuseFitsPrimitiveCharge : ∀ primitive count →
  Allocation.allocatedPrimitiveCharge primitive (geometricAllocations count)
  ≤ L2.square primitive
universalFiniteReuseFitsPrimitiveCharge primitive count =
  Allocation.primitiveSubpartitionFundsAllAllocatedCopies
    primitive
    (geometricAllocations count)
    (universalFiniteChargeSubpartition count)

round77EveryFiniteReuseFamilyHasCanonicalChargeSubpartition : Bool
round77EveryFiniteReuseFamilyHasCanonicalChargeSubpartition = true

round77DescendantChargeOrthogonalityRequired : Bool
round77DescendantChargeOrthogonalityRequired = false

round77AllocationComplexityCostDisappears : Bool
round77AllocationComplexityCostDisappears = false

round77WeightedPropagationMustPayAllocationCost : Bool
round77WeightedPropagationMustPayAllocationCost = true

round77EveryFiniteReuseFamilyHasCanonicalChargeSubpartitionIsTrue :
  round77EveryFiniteReuseFamilyHasCanonicalChargeSubpartition ≡ true
round77EveryFiniteReuseFamilyHasCanonicalChargeSubpartitionIsTrue = refl
