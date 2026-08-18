module DASHI.Physics.Closure.NSTriadKNMoranHutchinsonPropagationBoundaryRound75Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: P. A. P. Moran.
-- Title: "Additive functions of intervals and Hausdorff measure".
-- Mathematical Proceedings of the Cambridge Philosophical Society 42 (1946),
-- 15--23.
-- DOI: 10.1017/S0305004100022684.
--
-- Author: John E. Hutchinson.
-- Title: "Fractals and self-similarity".
-- Indiana University Mathematics Journal 30 (1981), 713--747.
-- DOI: 10.1512/iumj.1981.30.30055.
--
-- ROUND75 / MORAN--HUTCHINSON PROPAGATION BOUNDARY
--
-- Round74 discovered the exact deterministic squared-loss invariant
--
--     sum_i (r_i mu)^2 = mu^2 sum_i r_i^2.
--
-- The Moran similarity equation sum_i r_i^s = 1 therefore has an exact
-- arithmetic analogue at s=2.  This module imports NO fractal-dimension theorem;
-- Moran/Hutchinson are provenance for the non-overlap warning only.
--
-- The important correction is stronger than the usual open-set analogy:
-- sibling non-overlap does NOT imply that a parent and its children are
-- mutually disjoint.  Self-similar children are normally nested inside the
-- parent.  Therefore an NS Carleson argument which sums charge over MULTIPLE
-- generations needs either
--
--   (A) genuine cross-generation charge orthogonality/disjointness, or
--   (B) an antichain/generation-only argument whose mass itself grows.
--
-- At the critical surface sum_i r_i^2 = 1, one antichain preserves squared
-- floor mass exactly.  It does not grow.  Supercritical antichains can grow;
-- alternatively critical generations can yield cumulative growth only when
-- cross-generation charges are independently additive.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNDeterministicIrregularSquaredCascadeRound74Exact as Cascade
import DASHI.Physics.Closure.NSTriadKNPhysicalCarlesonFundingRound73Exact as Carleson

------------------------------------------------------------------------
-- Exact finite countermodel: siblings are disjoint but each child is nested
-- in / overlaps the parent.  This prevents importing the open-set condition as
-- a cross-generation charge theorem.
------------------------------------------------------------------------

data ToyPoint : Set where
  leftPoint rightPoint : ToyPoint

ParentSupport : ToyPoint → Bool
ParentSupport leftPoint = true
ParentSupport rightPoint = true

LeftChildSupport : ToyPoint → Bool
LeftChildSupport leftPoint = true
LeftChildSupport rightPoint = false

RightChildSupport : ToyPoint → Bool
RightChildSupport leftPoint = false
RightChildSupport rightPoint = true

supportsOverlapAt : (ToyPoint → Bool) → (ToyPoint → Bool) → ToyPoint → Set
supportsOverlapAt A B p =
  (A p ≡ true) × (B p ≡ true)
  where
  open import Data.Product.Base using (_×_)

childrenHaveNoCommonPoint :
  (p : ToyPoint) → ¬ supportsOverlapAt LeftChildSupport RightChildSupport p
childrenHaveNoCommonPoint leftPoint ()
childrenHaveNoCommonPoint rightPoint ()

leftChildOverlapsParent : supportsOverlapAt ParentSupport LeftChildSupport leftPoint
leftChildOverlapsParent = refl , refl
  where open import Data.Product.Base using (_,_)

rightChildOverlapsParent : supportsOverlapAt ParentSupport RightChildSupport rightPoint
rightChildOverlapsParent = refl , refl
  where open import Data.Product.Base using (_,_)

siblingNonOverlapDoesNotImplyCrossGenerationDisjointness : Bool
siblingNonOverlapDoesNotImplyCrossGenerationDisjointness = true

------------------------------------------------------------------------
-- Antichain route: Round74's critical generation theorem already says exactly
-- that the squared floor on ONE generation is preserved.  We expose that as
-- the safe Moran-s=2 analogue.
------------------------------------------------------------------------

criticalAntichainSquaredMassPreserved :
  (rows : List Cascade.CriticalSquaredPropagationRow) →
  Cascade.criticalChildMass rows ≡ Cascade.criticalParentMass rows
criticalAntichainSquaredMassPreserved =
  Cascade.criticalIrregularGenerationPreservesSquaredFloor

------------------------------------------------------------------------
-- Cross-generation route: if independent physical analysis supplies one
-- funded-node list per generation and certifies that concatenating those lists
-- is a legitimate additive physical charge family, then ordinary list
-- recursion makes the total floor exactly additive.  The theorem below does
-- NOT infer that physical premise from sibling separation.
------------------------------------------------------------------------

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

sumFloorsAppend : ∀ left right →
  Carleson.sumFloors (append left right)
  ≡ Carleson.sumFloors left + Carleson.sumFloors right
sumFloorsAppend [] right =
  let
    open import Data.Rational.Tactic.RingSolver using (solve)
  in solve (Carleson.sumFloors right ∷ [])
sumFloorsAppend (node ∷ rest) right =
  let
    open import Relation.Binary.PropositionalEquality using (cong; trans)
    open import Data.Rational.Tactic.RingSolver using (solve)
  in
  trans
    (cong (Carleson.floor node +_) (sumFloorsAppend rest right))
    (solve
      ( Carleson.floor node
      ∷ Carleson.sumFloors rest
      ∷ Carleson.sumFloors right
      ∷ []))

sumChargesAppend : ∀ left right →
  Carleson.sumCharges (append left right)
  ≡ Carleson.sumCharges left + Carleson.sumCharges right
sumChargesAppend [] right =
  let
    open import Data.Rational.Tactic.RingSolver using (solve)
  in solve (Carleson.sumCharges right ∷ [])
sumChargesAppend (node ∷ rest) right =
  let
    open import Relation.Binary.PropositionalEquality using (cong; trans)
    open import Data.Rational.Tactic.RingSolver using (solve)
  in
  trans
    (cong (Carleson.charge node +_) (sumChargesAppend rest right))
    (solve
      ( Carleson.charge node
      ∷ Carleson.sumCharges rest
      ∷ Carleson.sumCharges right
      ∷ []))

record CrossGenerationAdditiveCharge
    (earlier later : List Carleson.FundedNode) (budget : ℚ) : Set where
  field
    budgetNonnegative : 0ℚ ≤ budget
    concatenatedChargeWithinBudget :
      Carleson.sumCharges (append earlier later) ≤ budget

open CrossGenerationAdditiveCharge public

crossGenerationAdditivityFundsBothFloorFamilies :
  ∀ {earlier later budget} →
  CrossGenerationAdditiveCharge earlier later budget →
  Carleson.sumFloors earlier + Carleson.sumFloors later ≤ budget
crossGenerationAdditivityFundsBothFloorFamilies
    {earlier} {later} witness =
  let
    floorBelow = Carleson.sumFloorsBelowCharges (append earlier later)
    combined = ℚP.≤-trans floorBelow (concatenatedChargeWithinBudget witness)
  in
  Relation.Binary.PropositionalEquality.subst
    (_≤ budget)
    (sumFloorsAppend earlier later)
    combined
  where
  open import Relation.Binary.PropositionalEquality

crossGenerationFloorAboveBudgetRefutesAdditivity :
  ∀ {earlier later budget} →
  budget < Carleson.sumFloors earlier + Carleson.sumFloors later →
  ¬ CrossGenerationAdditiveCharge earlier later budget
crossGenerationFloorAboveBudgetRefutesAdditivity excess witness =
  ℚP.<-irrefl _
    (ℚP.<-≤-trans excess
      (crossGenerationAdditivityFundsBothFloorFamilies witness))

round75MoranS2ArithmeticIdentified : Bool
round75MoranS2ArithmeticIdentified = true

round75SiblingOpenSetStyleSeparationInsufficientForCrossGenerationCharge : Bool
round75SiblingOpenSetStyleSeparationInsufficientForCrossGenerationCharge = true

round75CriticalAntichainMassPreserved : Bool
round75CriticalAntichainMassPreserved = true

round75PhysicalCrossGenerationChargeOrthogonalityConstructed : Bool
round75PhysicalCrossGenerationChargeOrthogonalityConstructed = false

round75SupercriticalPhysicalAntichainGrowthConstructed : Bool
round75SupercriticalPhysicalAntichainGrowthConstructed = false

round75SiblingOpenSetStyleSeparationInsufficientForCrossGenerationChargeIsTrue :
  round75SiblingOpenSetStyleSeparationInsufficientForCrossGenerationCharge ≡ true
round75SiblingOpenSetStyleSeparationInsufficientForCrossGenerationChargeIsTrue = refl
