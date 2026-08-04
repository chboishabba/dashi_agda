module DASHI.Physics.YangMills.BalabanP33CMP109MinimalPathStageBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - I. Small Fields",
-- arXiv:1108.1335v2 [math-ph]. No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Convert the literal length-24 theorem for the minimal admissible CMP109
-- contours into the allocated transport and path-derivative budgets.  Exact
-- rational arithmetic gives
--
--   24 * (rho / 96) = rho / 4,
--   24 * (rho / 48) = rho / 2.
--
-- Hence the two large four-stage leaves are reduced to local directed-step
-- estimates.  No global transport or path budget is supplied independently:
-- finite-list induction sums the local bounds along every enumerated contour.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanP33CMP109MinimalContourLength24Exact as Length24
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

natAsRationalNonnegative : ∀ n → 0ℚ ≤ Sums.natAsRational n
natAsRationalNonnegative zero = ℚP.≤-refl
natAsRationalNonnegative (suc n) =
  ℚP.+-mono-≤
    (ℚP.nonNegative⁻¹ 1ℚ)
    (natAsRationalNonnegative n)

productNonnegative : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNonnegative left right leftNonnegative rightNonnegative =
  let
    instance
      leftNN : NonNegative left
      leftNN = ℚ.nonNegative leftNonnegative
      rightNN : NonNegative right
      rightNN = ℚ.nonNegative rightNonnegative
  in
  ℚP.nonNegative⁻¹ (left * right)

successorBudgetExact : ∀ n budget →
  budget + Sums.natAsRational n * budget
  ≡ Sums.natAsRational (suc n) * budget
successorBudgetExact = ℚRing.solve-∀

finiteUniformSumBoundByLength :
  ∀ {A : Set}
    (values : List A) (bound : Nat)
    (term : A → ℚ) (budget : ℚ) →
  0ℚ ≤ budget →
  Periodic.listLength values ≤ bound →
  (∀ value → term value ≤ budget) →
  Sums.sumRational values term
  ≤ Sums.natAsRational bound * budget
finiteUniformSumBoundByLength [] bound term budget budgetNonnegative
    lengthBound pointwise =
  productNonnegative
    (Sums.natAsRational bound) budget
    (natAsRationalNonnegative bound) budgetNonnegative
finiteUniformSumBoundByLength (value ∷ values) zero
    term budget budgetNonnegative () pointwise
finiteUniformSumBoundByLength (value ∷ values) (suc bound)
    term budget budgetNonnegative (s≤s lengthBound) pointwise =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (pointwise value)
      (finiteUniformSumBoundByLength
        values bound term budget budgetNonnegative lengthBound pointwise))
    (subst
      (λ upper →
        budget + Sums.natAsRational bound * budget ≤ upper)
      (successorBudgetExact bound budget)
      ℚP.≤-refl)

oneNinetySixth oneFortyEighth oneQuarter oneHalf : ℚ
oneNinetySixth = + 1 / 96
oneFortyEighth = + 1 / 48
oneQuarter = + 1 / 4
oneHalf = + 1 / 2

transportStepBudget pathStepBudget : ℚ
transportStepBudget = oneNinetySixth * P33.p33SmallFieldRadius
pathStepBudget = oneFortyEighth * P33.p33SmallFieldRadius

transportAllocatedBudget pathAllocatedBudget : ℚ
transportAllocatedBudget = oneQuarter * P33.p33SmallFieldRadius
pathAllocatedBudget = oneHalf * P33.p33SmallFieldRadius

transportStepBudgetNonnegative : 0ℚ ≤ transportStepBudget
transportStepBudgetNonnegative = ℚP.nonNegative⁻¹ transportStepBudget

pathStepBudgetNonnegative : 0ℚ ≤ pathStepBudget
pathStepBudgetNonnegative = ℚP.nonNegative⁻¹ pathStepBudget

transportTwentyFourStepsExact :
  Sums.natAsRational 24 * transportStepBudget
  ≡ transportAllocatedBudget
transportTwentyFourStepsExact = ℚRing.solve []

pathTwentyFourStepsExact :
  Sums.natAsRational 24 * pathStepBudget
  ≡ pathAllocatedBudget
pathTwentyFourStepsExact = ℚRing.solve []

minimalContourTransportBudget :
  (point : Centered.CenteredBlockPoint4 Minimal.radius) →
  ∀ order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Length24.centeredPointDisplacement point)) →
  (transportContribution : Word.SignedAxis4 → ℚ) →
  (∀ direction →
    transportContribution direction ≤ transportStepBudget) →
  Sums.sumRational (Periodic.contourWord order) transportContribution
  ≤ transportAllocatedBudget
minimalContourTransportBudget point order membership
    transportContribution pointwise =
  subst
    (λ upper →
      Sums.sumRational (Periodic.contourWord order) transportContribution
      ≤ upper)
    transportTwentyFourStepsExact
    (finiteUniformSumBoundByLength
      (Periodic.contourWord order) 24
      transportContribution transportStepBudget
      transportStepBudgetNonnegative
      (Length24.minimalCenteredContourLengthAtMost24
        point order membership)
      pointwise)

minimalContourPathDerivativeBudget :
  (point : Centered.CenteredBlockPoint4 Minimal.radius) →
  ∀ order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Length24.centeredPointDisplacement point)) →
  (pathContribution : Word.SignedAxis4 → ℚ) →
  (∀ direction → pathContribution direction ≤ pathStepBudget) →
  Sums.sumRational (Periodic.contourWord order) pathContribution
  ≤ pathAllocatedBudget
minimalContourPathDerivativeBudget point order membership
    pathContribution pointwise =
  subst
    (λ upper →
      Sums.sumRational (Periodic.contourWord order) pathContribution
      ≤ upper)
    pathTwentyFourStepsExact
    (finiteUniformSumBoundByLength
      (Periodic.contourWord order) 24
      pathContribution pathStepBudget
      pathStepBudgetNonnegative
      (Length24.minimalCenteredContourLengthAtMost24
        point order membership)
      pointwise)

cmp109FiniteLengthBudgetInductionLevel : ProofLevel
cmp109FiniteLengthBudgetInductionLevel = machineChecked

cmp109MinimalTransportQuarterAllocationLevel : ProofLevel
cmp109MinimalTransportQuarterAllocationLevel = machineChecked

cmp109MinimalPathHalfAllocationLevel : ProofLevel
cmp109MinimalPathHalfAllocationLevel = machineChecked
