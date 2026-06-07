module DASHI.Physics.Closure.YMStrictSelectedBoundaryCancellationCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as Strict

------------------------------------------------------------------------
-- Strict selected boundary-cancellation criterion.
--
-- This module consumes the finite selected-Hodge variation pairing surface
-- and packages the next exact calculation: if the selected boundary term is
-- the canonical zero/closed term, the selected finite action variation
-- reduces to the selected Euler-Lagrange pairing over the user-supplied
-- variation/action carriers.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedBoundaryCancellationStatus : Set where
  strictSelectedZeroBoundaryCancellationClosedNoPhysicalPromotion :
    StrictSelectedBoundaryCancellationStatus

data StrictSelectedBoundaryCancellationRow : Set where
  consumesStrictSelectedPairingRow :
    StrictSelectedBoundaryCancellationRow

  selectedBoundaryClosedHypothesisRow :
    StrictSelectedBoundaryCancellationRow

  canonicalBoundaryClosedEvidenceRow :
    StrictSelectedBoundaryCancellationRow

  combineWithCanonicalBoundaryRow :
    StrictSelectedBoundaryCancellationRow

  actionVariationReducesToEulerLagrangeRow :
    StrictSelectedBoundaryCancellationRow

  finiteCriterionClosedRow :
    StrictSelectedBoundaryCancellationRow

  physicalPromotionBlockedRow :
    StrictSelectedBoundaryCancellationRow

canonicalStrictSelectedBoundaryCancellationRows :
  List StrictSelectedBoundaryCancellationRow
canonicalStrictSelectedBoundaryCancellationRows =
  consumesStrictSelectedPairingRow
  ∷ selectedBoundaryClosedHypothesisRow
  ∷ canonicalBoundaryClosedEvidenceRow
  ∷ combineWithCanonicalBoundaryRow
  ∷ actionVariationReducesToEulerLagrangeRow
  ∷ finiteCriterionClosedRow
  ∷ physicalPromotionBlockedRow
  ∷ []

SelectedBoundaryClosedAt :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  Set
SelectedBoundaryClosedAt connection δA =
  Strict.strictSelectedBoundaryTerm connection δA
  ≡
  YMObs.ymSFGCUserSuppliedZeroActionScalar

selectedBoundaryClosedCanonical :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  SelectedBoundaryClosedAt connection δA
selectedBoundaryClosedCanonical connection δA =
  refl

selectedCombineWithCanonicalBoundaryIsEulerLagrange :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  SelectedBoundaryClosedAt connection δA →
  Strict.strictActionScalarCombine
    (Strict.strictSelectedHodgeVariationPairing connection δA)
    (Strict.strictSelectedBoundaryTerm connection δA)
  ≡
  Strict.strictSelectedHodgeVariationPairing connection δA
selectedCombineWithCanonicalBoundaryIsEulerLagrange connection δA refl =
  refl

selectedActionVariationReducesToEulerLagrange :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  SelectedBoundaryClosedAt connection δA →
  Strict.strictSelectedActionVariation connection δA
  ≡
  Strict.strictSelectedHodgeVariationPairing connection δA
selectedActionVariationReducesToEulerLagrange connection δA refl =
  refl

selectedIBPWithCanonicalBoundaryIsEulerLagrange :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  Strict.strictSelectedActionVariation connection δA
  ≡
  Strict.strictSelectedHodgeVariationPairing connection δA
selectedIBPWithCanonicalBoundaryIsEulerLagrange connection δA =
  selectedActionVariationReducesToEulerLagrange
    connection
    δA
    (selectedBoundaryClosedCanonical connection δA)

record StrictSelectedBoundaryCancellationCriterion : Set₁ where
  field
    status :
      StrictSelectedBoundaryCancellationStatus

    consumedStrictSelectedPairing :
      Strict.StrictSelectedHodgeVariationPairingCalculation

    consumedStrictSelectedPairingIsCanonical :
      consumedStrictSelectedPairing
      ≡
      Strict.canonicalStrictSelectedHodgeVariationPairingCalculation

    selectedFiniteClosure :
      YMObs.YMSFGCStrictSelectedHodgeVariationPairingFiniteClosure

    selectedFiniteClosureIsCanonical :
      selectedFiniteClosure
      ≡
      YMObs.canonicalYMSFGCStrictSelectedHodgeVariationPairingFiniteClosure

    boundaryClosedAt :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      Set

    boundaryClosedAtIsSelected :
      boundaryClosedAt
      ≡
      SelectedBoundaryClosedAt

    canonicalBoundaryClosed :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      boundaryClosedAt connection δA

    combineWithCanonicalBoundary :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      boundaryClosedAt connection δA →
      Strict.strictActionScalarCombine
        (Strict.strictSelectedHodgeVariationPairing connection δA)
        (Strict.strictSelectedBoundaryTerm connection δA)
      ≡
      Strict.strictSelectedHodgeVariationPairing connection δA

    actionVariationReducesToEulerLagrange :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      boundaryClosedAt connection δA →
      Strict.strictSelectedActionVariation connection δA
      ≡
      Strict.strictSelectedHodgeVariationPairing connection δA

    canonicalIBPReduction :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      Strict.strictSelectedActionVariation connection δA
      ≡
      Strict.strictSelectedHodgeVariationPairing connection δA

    finiteBoundaryCancellationCriterionClosed :
      Bool

    finiteBoundaryCancellationCriterionClosedIsTrue :
      finiteBoundaryCancellationCriterionClosed ≡ true

    selectedIBPReductionClosed :
      Bool

    selectedIBPReductionClosedIsTrue :
      selectedIBPReductionClosed ≡ true

    physicalYangMillsPromoted :
      Bool

    physicalYangMillsPromotedIsFalse :
      physicalYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    rowIndex :
      List StrictSelectedBoundaryCancellationRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalStrictSelectedBoundaryCancellationRows

    rowCount :
      Nat

    rowCountIs7 :
      rowCount ≡ 7

    criterionBoundary :
      List String

open StrictSelectedBoundaryCancellationCriterion public

canonicalStrictSelectedBoundaryCancellationCriterion :
  StrictSelectedBoundaryCancellationCriterion
canonicalStrictSelectedBoundaryCancellationCriterion =
  record
    { status =
        strictSelectedZeroBoundaryCancellationClosedNoPhysicalPromotion
    ; consumedStrictSelectedPairing =
        Strict.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; consumedStrictSelectedPairingIsCanonical =
        refl
    ; selectedFiniteClosure =
        YMObs.canonicalYMSFGCStrictSelectedHodgeVariationPairingFiniteClosure
    ; selectedFiniteClosureIsCanonical =
        refl
    ; boundaryClosedAt =
        SelectedBoundaryClosedAt
    ; boundaryClosedAtIsSelected =
        refl
    ; canonicalBoundaryClosed =
        selectedBoundaryClosedCanonical
    ; combineWithCanonicalBoundary =
        selectedCombineWithCanonicalBoundaryIsEulerLagrange
    ; actionVariationReducesToEulerLagrange =
        selectedActionVariationReducesToEulerLagrange
    ; canonicalIBPReduction =
        selectedIBPWithCanonicalBoundaryIsEulerLagrange
    ; finiteBoundaryCancellationCriterionClosed =
        true
    ; finiteBoundaryCancellationCriterionClosedIsTrue =
        refl
    ; selectedIBPReductionClosed =
        true
    ; selectedIBPReductionClosedIsTrue =
        refl
    ; physicalYangMillsPromoted =
        false
    ; physicalYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; rowIndex =
        canonicalStrictSelectedBoundaryCancellationRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        7
    ; rowCountIs7 =
        refl
    ; criterionBoundary =
        "Consumes DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as the strict selected finite variation/IBP calculation"
        ∷ "Defines SelectedBoundaryClosedAt as equality between the selected boundary term and the canonical zero action scalar"
        ∷ "The canonical selected boundary term is closed by refl over every user-supplied connection and variation"
        ∷ "Combining the selected Euler-Lagrange pairing with the canonical zero boundary term reduces to the selected Euler-Lagrange pairing"
        ∷ "The selected action variation therefore reduces to the selected Euler-Lagrange pairing on the finite user-supplied carriers"
        ∷ "This closes only the selected zero-boundary cancellation criterion, not a nontrivial physical boundary theorem"
        ∷ "Physical Yang-Mills, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalStrictSelectedBoundaryCancellationRowCountIs7 :
  listCount canonicalStrictSelectedBoundaryCancellationRows ≡ 7
canonicalStrictSelectedBoundaryCancellationRowCountIs7 =
  refl

canonicalStrictSelectedBoundaryCancellationClosed :
  StrictSelectedBoundaryCancellationCriterion.finiteBoundaryCancellationCriterionClosed
    canonicalStrictSelectedBoundaryCancellationCriterion
  ≡
  true
canonicalStrictSelectedBoundaryCancellationClosed =
  refl

canonicalStrictSelectedBoundaryCancellationIBPReductionClosed :
  StrictSelectedBoundaryCancellationCriterion.selectedIBPReductionClosed
    canonicalStrictSelectedBoundaryCancellationCriterion
  ≡
  true
canonicalStrictSelectedBoundaryCancellationIBPReductionClosed =
  refl

canonicalStrictSelectedBoundaryCancellationPhysicalPromotionFalse :
  StrictSelectedBoundaryCancellationCriterion.physicalYangMillsPromoted
    canonicalStrictSelectedBoundaryCancellationCriterion
  ≡
  false
canonicalStrictSelectedBoundaryCancellationPhysicalPromotionFalse =
  refl

canonicalStrictSelectedBoundaryCancellationClayPromotionFalse :
  StrictSelectedBoundaryCancellationCriterion.clayYangMillsPromoted
    canonicalStrictSelectedBoundaryCancellationCriterion
  ≡
  false
canonicalStrictSelectedBoundaryCancellationClayPromotionFalse =
  refl

canonicalStrictSelectedBoundaryCancellationTerminalPromotionFalse :
  StrictSelectedBoundaryCancellationCriterion.terminalPromotion
    canonicalStrictSelectedBoundaryCancellationCriterion
  ≡
  false
canonicalStrictSelectedBoundaryCancellationTerminalPromotionFalse =
  refl
