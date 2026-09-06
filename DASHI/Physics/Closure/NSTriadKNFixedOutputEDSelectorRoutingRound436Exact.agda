module DASHI.Physics.Closure.NSTriadKNFixedOutputEDSelectorRoutingRound436Exact where

------------------------------------------------------------------------
-- ROUND436 / FIXED-OUTPUT ED CHARGES -> ONE PHYSICAL R109 SELECTOR
--
-- R435 isolates the only remaining summation carrier seam:
--
--   sum_k ED_k
--
-- must be recognized as a partition/subselection of the physical ordered-pair
-- energy-dissipation kernel.  R219 already instantiates R109 on the literal
-- Galerkin velocity with
--
--   E_m = ||u_m||^2,
--   D_m = |m|^2 ||u_m||^2,
--
-- and proves the selected-pair bound for ANY Boolean selector.  Therefore no
-- further analytic inequality is required here.
--
-- This owner makes the same-object routing explicit.  A physical family gives
-- one Boolean selector and proves that the sum of its fixed-output ED charges
-- is exactly the corresponding R109 selected ordered-pair sum.  The existing
-- R219 theorem then constructs R435.GlobalSelectedPairEDPayment automatically.
--
-- The equality/partition receipt is still a real carrier obligation; it is not
-- fabricated from R284's unindexed scalar `energyDissipation` field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeFamilyRound435Exact as R435

F : C3.RealField _
F = Rational.rationalRealField

record PhysicalFixedOutputEDRouting
    {theta coefficient : ℚ}
    (cells : List (R435.UniformFixedOutputCriticalConeCell theta coefficient))
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (modes : List Z3.FourierMode) : Set where
  constructor physical-fixed-output-ed-routing
  field
    select : Z3.FourierMode → Z3.FourierMode → Bool

    fibreEDSumMeaning :
      R435.sumED cells
      ≡ R109.selectedOrderedPairSum
          (R219.physicalModalED E I velocity)
          select modes modes

open PhysicalFixedOutputEDRouting public

selectedPhysicalED :
  ∀ {theta coefficient}
    {cells : List (R435.UniformFixedOutputCriticalConeCell theta coefficient)}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {velocity : Z3.FourierMode → C3.Complex3 F}
    {modes : List Z3.FourierMode} →
  PhysicalFixedOutputEDRouting cells E I velocity modes → ℚ
selectedPhysicalED {E = E} {I = I} {velocity = velocity} {modes = modes} R =
  R109.selectedOrderedPairSum
    (R219.physicalModalED E I velocity)
    (select R) modes modes

globalPhysicalEnergyDissipationProduct :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (modes : List Z3.FourierMode) → ℚ
globalPhysicalEnergyDissipationProduct E I velocity modes =
  R109.sumEnergy (R219.physicalModalED E I velocity) modes
  * R109.sumDissipation (R219.physicalModalED E I velocity) modes

physicalRoutingToGlobalSelectedPairEDPayment :
  ∀ {theta coefficient}
    (cells : List (R435.UniformFixedOutputCriticalConeCell theta coefficient))
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (modes : List Z3.FourierMode) →
  (R : PhysicalFixedOutputEDRouting cells E I velocity modes) →
  R435.GlobalSelectedPairEDPayment cells
physicalRoutingToGlobalSelectedPairEDPayment cells E I velocity modes R = record
  { R435.globalEnergyDissipationProduct =
      globalPhysicalEnergyDissipationProduct E I velocity modes
  ; R435.selectedPairEDUpper = selectedPhysicalED R
  ; R435.fibreEDSumPaid =
      subst
        (λ upper → R435.sumED cells ≤ upper)
        (fibreEDSumMeaning R)
        ℚP.≤-refl
  ; R435.selectedPairUpperPaid =
      R219.physicalSelectedPairEDBound
        E I velocity (select R) modes
  }

physicalRoutingClosesGlobalFixedOutputEDBudget :
  ∀ {theta coefficient}
    (cells : List (R435.UniformFixedOutputCriticalConeCell theta coefficient))
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (modes : List Z3.FourierMode) →
  0ℚ ≤ coefficient →
  (R : PhysicalFixedOutputEDRouting cells E I velocity modes) →
  R435.sumCross cells
  ≤ theta * R435.sumCompanion cells
    + coefficient
      * (globalPhysicalEnergyDissipationProduct E I velocity modes
        + globalPhysicalEnergyDissipationProduct E I velocity modes)
physicalRoutingClosesGlobalFixedOutputEDBudget
    cells E I velocity modes coefficientNN R =
  R435.globalFixedOutputCriticalConeBound
    cells coefficientNN
    (physicalRoutingToGlobalSelectedPairEDPayment cells E I velocity modes R)

round436PhysicalR109SelectorUpperBoundAlreadyOwned : Bool
round436PhysicalR109SelectorUpperBoundAlreadyOwned =
  R219.round219PhysicalSelectorEDAdapterClosed

round436EDBudgetSummationNeedsNewAnalyticInequality : Bool
round436EDBudgetSummationNeedsNewAnalyticInequality = false

round436FixedOutputEDPartitionEqualityInstalled : Bool
round436FixedOutputEDPartitionEqualityInstalled = false

round436FixedOutputEDRoutingCompilerClosed : Bool
round436FixedOutputEDRoutingCompilerClosed = true

round436AddsOutputCardinalityFactor : Bool
round436AddsOutputCardinalityFactor = false

round436PhysicalCriticalConeCovarianceClosed : Bool
round436PhysicalCriticalConeCovarianceClosed = false

round436R423SignedCommonCrossPaid : Bool
round436R423SignedCommonCrossPaid = false

round436PackageAClosed : Bool
round436PackageAClosed = false

round436ClayPromotion : Bool
round436ClayPromotion = false

round436EDBudgetSummationNeedsNewAnalyticInequalityIsFalse :
  round436EDBudgetSummationNeedsNewAnalyticInequality ≡ false
round436EDBudgetSummationNeedsNewAnalyticInequalityIsFalse = refl

round436FixedOutputEDRoutingCompilerClosedIsTrue :
  round436FixedOutputEDRoutingCompilerClosed ≡ true
round436FixedOutputEDRoutingCompilerClosedIsTrue = refl

round436FixedOutputEDPartitionEqualityInstalledIsFalse :
  round436FixedOutputEDPartitionEqualityInstalled ≡ false
round436FixedOutputEDPartitionEqualityInstalledIsFalse = refl
