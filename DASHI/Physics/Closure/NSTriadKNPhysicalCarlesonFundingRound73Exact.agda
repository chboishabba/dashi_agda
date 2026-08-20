module DASHI.Physics.Closure.NSTriadKNPhysicalCarlesonFundingRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / FINITE CARLESON FUNDING FORM
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Lennart Carleson.
-- Classical Carleson-measure framework; the exact finite ledger theorem below
-- is elementary ordered finite algebra and does not import a deep theorem.
--
-- Round70--72 used a global finite budget plus descendant multiplicity.  The
-- safer invariant is additive physical charge on genuinely disjoint/orthogonal
-- descendants.  Once a physical subtree is certified additive, every node has
--
--     floor_nu <= charge_nu,
--
-- and a Carleson-style budget says the subtree charge sum is <= E.  Then the
-- sum of all node floors is <= E.  Any finite propagated prefix whose certified
-- floor total already exceeds E therefore contradicts that budget exactly.
--
-- This file proves the exact finite ledger and contradiction.  It deliberately
-- leaves the PDE theorem saying that selected descendants are charge-disjoint /
-- orthogonal as a separate physical source obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation.Core using (¬_)

record FundedNode : Set where
  constructor funded-node
  field
    floor : ℚ
    charge : ℚ
    floorNonnegative : 0ℚ ≤ floor
    floorBelowCharge : floor ≤ charge

open FundedNode public

sumFloors : List FundedNode → ℚ
sumFloors [] = 0ℚ
sumFloors (node ∷ rest) = floor node + sumFloors rest

sumCharges : List FundedNode → ℚ
sumCharges [] = 0ℚ
sumCharges (node ∷ rest) = charge node + sumCharges rest

sumFloorsBelowCharges : ∀ nodes → sumFloors nodes ≤ sumCharges nodes
sumFloorsBelowCharges [] = ℚP.≤-refl
sumFloorsBelowCharges (node ∷ rest) =
  ℚP.+-mono-≤
    (floorBelowCharge node)
    (sumFloorsBelowCharges rest)

record PhysicalCarlesonBudget (nodes : List FundedNode) (budget : ℚ) : Set where
  field
    budgetNonnegative : 0ℚ ≤ budget
    subtreeChargeWithinBudget : sumCharges nodes ≤ budget

open PhysicalCarlesonBudget public

carlesonBudgetFundsAllCertifiedFloors :
  ∀ {nodes budget} →
  PhysicalCarlesonBudget nodes budget →
  sumFloors nodes ≤ budget
carlesonBudgetFundsAllCertifiedFloors {nodes} witness =
  ℚP.≤-trans
    (sumFloorsBelowCharges nodes)
    (subtreeChargeWithinBudget witness)

floorPrefixAboveBudgetRefutesCarlesonFunding :
  ∀ {nodes budget} →
  budget < sumFloors nodes →
  ¬ PhysicalCarlesonBudget nodes budget
floorPrefixAboveBudgetRefutesCarlesonFunding {budget = budget} excess witness =
  ℚP.<-irrefl budget
    (ℚP.<-≤-trans excess (carlesonBudgetFundsAllCertifiedFloors witness))

record FrameGeneratedNode : Set where
  constructor frame-generated-node
  field
    amplificationSquare : ℚ
    effectiveComplexityBudget : ℚ
    generatedFloor : ℚ
    floorNonnegativeFG : 0ℚ ≤ generatedFloor
    amplificationPaidByFloor :
      amplificationSquare ≤ generatedFloor * effectiveComplexityBudget

open FrameGeneratedNode public

record PhysicalFrameFundedNode : Set where
  constructor physical-frame-funded-node
  field
    generated : FrameGeneratedNode
    actualCharge : ℚ
    generatedFloorBelowActualCharge : generatedFloor generated ≤ actualCharge

open PhysicalFrameFundedNode public

forgetFrameNode : PhysicalFrameFundedNode → FundedNode
forgetFrameNode node =
  funded-node
    (generatedFloor (generated node))
    (actualCharge node)
    (floorNonnegativeFG (generated node))
    (generatedFloorBelowActualCharge node)

forgetFrameNodes : List PhysicalFrameFundedNode → List FundedNode
forgetFrameNodes [] = []
forgetFrameNodes (node ∷ rest) = forgetFrameNode node ∷ forgetFrameNodes rest

round73FiniteCarlesonFundingTheoremConstructed : Bool
round73FiniteCarlesonFundingTheoremConstructed = true

round73PhysicalDescendantChargeOrthogonalityConstructed : Bool
round73PhysicalDescendantChargeOrthogonalityConstructed = false

round73CriticalAmplificationViolatesPhysicalCarlesonBudgetConstructed : Bool
round73CriticalAmplificationViolatesPhysicalCarlesonBudgetConstructed = false

round73FiniteCarlesonFundingTheoremConstructedIsTrue :
  round73FiniteCarlesonFundingTheoremConstructed ≡ true
round73FiniteCarlesonFundingTheoremConstructedIsTrue = refl

round73PhysicalDescendantChargeOrthogonalityConstructedIsFalse :
  round73PhysicalDescendantChargeOrthogonalityConstructed ≡ false
round73PhysicalDescendantChargeOrthogonalityConstructedIsFalse = refl
