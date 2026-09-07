module DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeFamilyRound435Exact where

------------------------------------------------------------------------
-- ROUND435 / UNIFORM FIXED-OUTPUT CRITICAL-CONE FAMILY -> GLOBAL BUDGET
--
-- R434 proves the pointwise/fixed-output compiler
--
--   X_k <= theta_k Q_k + C_k ED_k.
--
-- The remaining finite summation is not a new Navier--Stokes estimate.  If the
-- physical family supplies ONE uniform theta < 1 and ONE uniform coefficient C
-- so that theta_k = theta and C_k = C for every retained output, then literal
-- list induction gives
--
--   sum_k X_k <= theta sum_k Q_k + C sum_k ED_k.
--
-- R109 already proves, for ANY Boolean-selected ordered modal pair family,
--
--   sum selected (D_i E_j + E_i D_j) <= 2 E D
--
-- with no cardinality factor.  Hence a same-object adapter identifying the
-- fixed-output charges ED_k with a partition/subselection of that R109 kernel
-- immediately gives
--
--   sum_k X_k <= theta sum_k Q_k + 2 C E D.
--
-- This owner deliberately keeps that adapter explicit.  R284's scalar record
-- does not currently remember which modal pairs produced its `energyDissipation`
-- field, so pretending the R109 theorem applies definitionally would erase a
-- real carrier seam.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact as R434
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109

record UniformFixedOutputCriticalConeCell (theta coefficient : ℚ) : Set where
  constructor uniform-fixed-output-critical-cone-cell
  field
    decomposition : R434.FixedOutputCriticalConeDecomposition

    thetaMeaning :
      R284.theta (R434.payment decomposition) ≡ theta

    coefficientMeaning :
      R284.paidDeepCoefficient (R434.payment decomposition)
        + R284.coreEDCoefficient (R434.payment decomposition)
      ≡ coefficient

open UniformFixedOutputCriticalConeCell public

cellCross :
  ∀ {theta coefficient} →
  UniformFixedOutputCriticalConeCell theta coefficient → ℚ
cellCross C = R434.fixedOutputCross (decomposition C)

cellCompanion :
  ∀ {theta coefficient} →
  UniformFixedOutputCriticalConeCell theta coefficient → ℚ
cellCompanion C = R284.coreCompanionMass (R434.payment (decomposition C))

cellED :
  ∀ {theta coefficient} →
  UniformFixedOutputCriticalConeCell theta coefficient → ℚ
cellED C = R284.energyDissipation (R434.payment (decomposition C))

uniformCellBound :
  ∀ {theta coefficient}
    (C : UniformFixedOutputCriticalConeCell theta coefficient) →
  cellCross C ≤ theta * cellCompanion C + coefficient * cellED C
uniformCellBound {theta} {coefficient} C =
  let
    D = decomposition C
    P = R434.payment D
    base = R434.fixedOutputCrossBelowCriticalConeBudget D
    endpoint :
      R284.theta P * R284.coreCompanionMass P
        + (R284.paidDeepCoefficient P + R284.coreEDCoefficient P)
          * R284.energyDissipation P
      ≡ theta * cellCompanion C + coefficient * cellED C
    endpoint rewrite thetaMeaning C | coefficientMeaning C = refl
  in
  subst (cellCross C ≤_) endpoint base

sumCross :
  ∀ {theta coefficient} →
  List (UniformFixedOutputCriticalConeCell theta coefficient) → ℚ
sumCross [] = 0ℚ
sumCross (C ∷ rest) = cellCross C + sumCross rest

sumCompanion :
  ∀ {theta coefficient} →
  List (UniformFixedOutputCriticalConeCell theta coefficient) → ℚ
sumCompanion [] = 0ℚ
sumCompanion (C ∷ rest) = cellCompanion C + sumCompanion rest

sumED :
  ∀ {theta coefficient} →
  List (UniformFixedOutputCriticalConeCell theta coefficient) → ℚ
sumED [] = 0ℚ
sumED (C ∷ rest) = cellED C + sumED rest

uniformFamilyFiniteSumBound :
  ∀ {theta coefficient}
    (cells : List (UniformFixedOutputCriticalConeCell theta coefficient)) →
  sumCross cells ≤ theta * sumCompanion cells + coefficient * sumED cells
uniformFamilyFiniteSumBound {theta} {coefficient} [] =
  subst (0ℚ ≤_) (sym (solve (theta ∷ coefficient ∷ []))) ℚP.≤-refl
uniformFamilyFiniteSumBound {theta} {coefficient} (C ∷ rest) =
  let
    summed = ℚP.+-mono-≤
      (uniformCellBound C)
      (uniformFamilyFiniteSumBound rest)
    endpoint :
      (theta * cellCompanion C + coefficient * cellED C)
        + (theta * sumCompanion rest + coefficient * sumED rest)
      ≡ theta * sumCompanion (C ∷ rest)
        + coefficient * sumED (C ∷ rest)
    endpoint = solve
      ( theta ∷ coefficient
      ∷ cellCompanion C ∷ cellED C
      ∷ sumCompanion rest ∷ sumED rest ∷ [])
  in
  subst
    (λ upper → sumCross (C ∷ rest) ≤ upper)
    endpoint summed

record GlobalSelectedPairEDPayment
    {theta coefficient : ℚ}
    (cells : List (UniformFixedOutputCriticalConeCell theta coefficient)) : Set where
  constructor global-selected-pair-ed-payment
  field
    globalEnergyDissipationProduct : ℚ
    selectedPairEDUpper : ℚ

    -- This is the SAME-OBJECT routing seam.  A physical producer must show
    -- that the sum of per-output ED charges is a partition/subselection of the
    -- R109 selected-pair kernel, and then transport R109's theorem to this
    -- scalar upper bound.
    fibreEDSumPaid : sumED cells ≤ selectedPairEDUpper

    selectedPairUpperPaid :
      selectedPairEDUpper
      ≤ globalEnergyDissipationProduct + globalEnergyDissipationProduct

open GlobalSelectedPairEDPayment public

globalFixedOutputCriticalConeBound :
  ∀ {theta coefficient}
    (cells : List (UniformFixedOutputCriticalConeCell theta coefficient)) →
  0ℚ ≤ coefficient →
  (G : GlobalSelectedPairEDPayment cells) →
  sumCross cells
  ≤ theta * sumCompanion cells
    + coefficient
      * (globalEnergyDissipationProduct G + globalEnergyDissipationProduct G)
globalFixedOutputCriticalConeBound {theta} {coefficient} cells coefficientNN G =
  let
    finite = uniformFamilyFiniteSumBound cells

    edToSelected :
      coefficient * sumED cells ≤ coefficient * selectedPairEDUpper G
    edToSelected =
      let instance coefficientNNI = ℚ.nonNegative coefficientNN
      in ℚP.*-monoˡ-≤-nonNeg coefficient (fibreEDSumPaid G)

    selectedToGlobal :
      coefficient * selectedPairEDUpper G
      ≤ coefficient
        * (globalEnergyDissipationProduct G + globalEnergyDissipationProduct G)
    selectedToGlobal =
      let instance coefficientNNI = ℚ.nonNegative coefficientNN
      in ℚP.*-monoˡ-≤-nonNeg coefficient (selectedPairUpperPaid G)

    forcingBound = ℚP.≤-trans edToSelected selectedToGlobal
    added = ℚP.+-monoʳ-≤ (theta * sumCompanion cells) forcingBound
  in
  ℚP.≤-trans finite added

round435UniformFiniteFamilySummationClosed : Bool
round435UniformFiniteFamilySummationClosed = true

round435FamilySummationAddsOutputCardinalityFactor : Bool
round435FamilySummationAddsOutputCardinalityFactor = false

round435R109SelectedPairEDCompilerAlreadyOwned : Bool
round435R109SelectedPairEDCompilerAlreadyOwned =
  R109.round109SelectedPairEnergyDissipationProductBoundClosed

round435R109SelectedPairEDHasNoCardinalityFactor : Bool
round435R109SelectedPairEDHasNoCardinalityFactor =
  R109.round109SelectedPairBoundHasNoCardinalityFactor

round435PhysicalUniformThetaAndCoefficientFamilyInstalled : Bool
round435PhysicalUniformThetaAndCoefficientFamilyInstalled = false

round435FixedOutputEDChargesWeldedToR109SelectedPairs : Bool
round435FixedOutputEDChargesWeldedToR109SelectedPairs = false

round435PhysicalCriticalConeCovarianceClosed : Bool
round435PhysicalCriticalConeCovarianceClosed = false

round435R423SignedCommonCrossPaid : Bool
round435R423SignedCommonCrossPaid = false

round435PackageAClosed : Bool
round435PackageAClosed = false

round435ClayPromotion : Bool
round435ClayPromotion = false

round435UniformFiniteFamilySummationClosedIsTrue :
  round435UniformFiniteFamilySummationClosed ≡ true
round435UniformFiniteFamilySummationClosedIsTrue = refl

round435FamilySummationAddsOutputCardinalityFactorIsFalse :
  round435FamilySummationAddsOutputCardinalityFactor ≡ false
round435FamilySummationAddsOutputCardinalityFactorIsFalse = refl

round435R109SelectedPairEDCompilerAlreadyOwnedIsTrue :
  round435R109SelectedPairEDCompilerAlreadyOwned ≡ true
round435R109SelectedPairEDCompilerAlreadyOwnedIsTrue =
  R109.round109SelectedPairEnergyDissipationProductBoundClosedIsTrue

round435FixedOutputEDChargesWeldedToR109SelectedPairsIsFalse :
  round435FixedOutputEDChargesWeldedToR109SelectedPairs ≡ false
round435FixedOutputEDChargesWeldedToR109SelectedPairsIsFalse = refl
