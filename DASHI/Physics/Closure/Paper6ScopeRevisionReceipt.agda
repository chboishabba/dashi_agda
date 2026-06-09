module DASHI.Physics.Closure.Paper6ScopeRevisionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Paper 6 scope revision receipt.
--
-- This receipt narrows Paper 6 to exactly two recorded items:
--
-- 1. lambda = sqrt(m_d/m_s), recorded as a known structural connection in
--    the Georgi-Jarlskog literature, not as a new DASHI result.
-- 2. |Vub| approximately alpha1 alpha2, recorded as a structural hypothesis
--    from an adjacent-only carrier chain in U_d approximately I.  The 4.2
--    percent leading-order match and the 1073 percent next-order failure are
--    both part of the receipt.
--
-- Every other CKM quantity remains open frontier, and no Paper 6 quantity is
-- allowed to support Paper 8.  Paper 8 rests on NS and YM only.

data Paper6PresentedThing : Set where
  lambdaSqrtMdMsKnownStructuralConnection :
    Paper6PresentedThing

  vubAlpha1Alpha2AdjacentOnlyHypothesis :
    Paper6PresentedThing

paper6PresentedThings :
  List Paper6PresentedThing
paper6PresentedThings =
  lambdaSqrtMdMsKnownStructuralConnection
  ∷ vubAlpha1Alpha2AdjacentOnlyHypothesis
  ∷ []

data Paper6ClaimStatus : Set where
  knownStructuralConnectionExternalLiterature :
    Paper6ClaimStatus

  structuralHypothesisLeadingOrderOnly :
    Paper6ClaimStatus

data Paper6CKMFrontierQuantity : Set where
  vcbMagnitudeOpen :
    Paper6CKMFrontierQuantity

  gammaAngleOpen :
    Paper6CKMFrontierQuantity

  betaAngleOpen :
    Paper6CKMFrontierQuantity

  alphaAngleOpen :
    Paper6CKMFrontierQuantity

  ckmPhaseOpen :
    Paper6CKMFrontierQuantity

  jarlskogOpen :
    Paper6CKMFrontierQuantity

  fullCKMMatrixOpen :
    Paper6CKMFrontierQuantity

  physicalCKMDiagonalisationOpen :
    Paper6CKMFrontierQuantity

canonicalPaper6OpenCKMFrontier :
  List Paper6CKMFrontierQuantity
canonicalPaper6OpenCKMFrontier =
  vcbMagnitudeOpen
  ∷ gammaAngleOpen
  ∷ betaAngleOpen
  ∷ alphaAngleOpen
  ∷ ckmPhaseOpen
  ∷ jarlskogOpen
  ∷ fullCKMMatrixOpen
  ∷ physicalCKMDiagonalisationOpen
  ∷ []

data Paper6ScopeBlocker : Set where
  lambdaIsNotNewDASHIResult :
    Paper6ScopeBlocker

  vubIsStructuralHypothesisOnly :
    Paper6ScopeBlocker

  nextOrderVubCorrectionFails :
    Paper6ScopeBlocker

  allOtherCKMQuantitiesOpen :
    Paper6ScopeBlocker

  noPaper6QuantitySupportsPaper8 :
    Paper6ScopeBlocker

canonicalPaper6ScopeBlockers :
  List Paper6ScopeBlocker
canonicalPaper6ScopeBlockers =
  lambdaIsNotNewDASHIResult
  ∷ vubIsStructuralHypothesisOnly
  ∷ nextOrderVubCorrectionFails
  ∷ allOtherCKMQuantitiesOpen
  ∷ noPaper6QuantitySupportsPaper8
  ∷ []

data Paper6Paper8Support : Set where

paper6Paper8SupportImpossibleHere :
  Paper6Paper8Support →
  ⊥
paper6Paper8SupportImpossibleHere ()

lambdaFormulaLabel : String
lambdaFormulaLabel =
  "lambda = sqrt(m_d/m_s)"

lambdaLiteratureLabel : String
lambdaLiteratureLabel =
  "known structural connection in the Georgi-Jarlskog literature"

vubFormulaLabel : String
vubFormulaLabel =
  "|Vub| approximately alpha1 alpha2"

vubChainLabel : String
vubChainLabel =
  "adjacent-only carrier chain in U_d approximately I"

paper8BasisLabel : String
paper8BasisLabel =
  "Paper 8 rests on NS and YM only"

record Paper6ScopedItem : Set where
  field
    item :
      Paper6PresentedThing

    formula :
      String

    status :
      Paper6ClaimStatus

    statusLabel :
      String

    newDASHIResult :
      Bool

    newDASHIResultIsFalseForLambdaWhenExternal :
      item ≡ lambdaSqrtMdMsKnownStructuralConnection →
      newDASHIResult ≡ false

    structuralHypothesis :
      Bool

    supportsPaper8 :
      Bool

    supportsPaper8IsFalse :
      supportsPaper8 ≡ false

open Paper6ScopedItem public

lambdaScopeItem :
  Paper6ScopedItem
lambdaScopeItem =
  record
    { item =
        lambdaSqrtMdMsKnownStructuralConnection
    ; formula =
        lambdaFormulaLabel
    ; status =
        knownStructuralConnectionExternalLiterature
    ; statusLabel =
        lambdaLiteratureLabel
    ; newDASHIResult =
        false
    ; newDASHIResultIsFalseForLambdaWhenExternal =
        λ _ → refl
    ; structuralHypothesis =
        false
    ; supportsPaper8 =
        false
    ; supportsPaper8IsFalse =
        refl
    }

vubScopeItem :
  Paper6ScopedItem
vubScopeItem =
  record
    { item =
        vubAlpha1Alpha2AdjacentOnlyHypothesis
    ; formula =
        vubFormulaLabel
    ; status =
        structuralHypothesisLeadingOrderOnly
    ; statusLabel =
        vubChainLabel
    ; newDASHIResult =
        false
    ; newDASHIResultIsFalseForLambdaWhenExternal =
        λ ()
    ; structuralHypothesis =
        true
    ; supportsPaper8 =
        false
    ; supportsPaper8IsFalse =
        refl
    }

canonicalPaper6ScopedItems :
  List Paper6ScopedItem
canonicalPaper6ScopedItems =
  lambdaScopeItem
  ∷ vubScopeItem
  ∷ []

canonicalPaper6ScopeBoundary :
  List String
canonicalPaper6ScopeBoundary =
  "Paper 6 presents exactly two things"
  ∷ "lambda = sqrt(m_d/m_s) is recorded as a known Georgi-Jarlskog structural connection, not a new DASHI result"
  ∷ "|Vub| approximately alpha1 alpha2 is recorded as a structural hypothesis from an adjacent-only carrier chain in U_d approximately I"
  ∷ "|Vub| leading-order match is 4.2 percent"
  ∷ "|Vub| next-order correction failure is 1073 percent"
  ∷ "All other CKM quantities are open frontier"
  ∷ "No quantity in Paper 6 supports Paper 8"
  ∷ "paper6SupportsPaper8 = false"
  ∷ "paper8RestsOnNSandYMOnly = true"
  ∷ []

record Paper6ScopeRevisionReceipt : Setω where
  field
    presentedThings :
      List Paper6PresentedThing

    presentedThingsAreExactlyCanonical :
      presentedThings ≡ paper6PresentedThings

    presentedThingCount :
      Nat

    presentedThingCountIsTwo :
      presentedThingCount ≡ 2

    scopedItems :
      List Paper6ScopedItem

    scopedItemsAreCanonical :
      scopedItems ≡ canonicalPaper6ScopedItems

    lambdaFormula :
      String

    lambdaFormulaIsCanonical :
      lambdaFormula ≡ lambdaFormulaLabel

    lambdaKnownStructuralConnection :
      Bool

    lambdaKnownStructuralConnectionIsTrue :
      lambdaKnownStructuralConnection ≡ true

    lambdaGeorgiJarlskogLiterature :
      Bool

    lambdaGeorgiJarlskogLiteratureIsTrue :
      lambdaGeorgiJarlskogLiterature ≡ true

    lambdaNewDASHIResult :
      Bool

    lambdaNewDASHIResultIsFalse :
      lambdaNewDASHIResult ≡ false

    vubFormula :
      String

    vubFormulaIsCanonical :
      vubFormula ≡ vubFormulaLabel

    vubStructuralHypothesis :
      Bool

    vubStructuralHypothesisIsTrue :
      vubStructuralHypothesis ≡ true

    adjacentOnlyCarrierChain :
      Bool

    adjacentOnlyCarrierChainIsTrue :
      adjacentOnlyCarrierChain ≡ true

    downDiagonalizerApproximatelyIdentity :
      Bool

    downDiagonalizerApproximatelyIdentityIsTrue :
      downDiagonalizerApproximatelyIdentity ≡ true

    vubLeadingOrderMatchPercent :
      Float

    vubLeadingOrderMatchPercentIsCanonical :
      vubLeadingOrderMatchPercent ≡ 4.2

    vubNextOrderFailurePercent :
      Float

    vubNextOrderFailurePercentIsCanonical :
      vubNextOrderFailurePercent ≡ 1073.0

    vubNextOrderFailureDocumented :
      Bool

    vubNextOrderFailureDocumentedIsTrue :
      vubNextOrderFailureDocumented ≡ true

    openCKMFrontier :
      List Paper6CKMFrontierQuantity

    openCKMFrontierIsCanonical :
      openCKMFrontier ≡ canonicalPaper6OpenCKMFrontier

    allOtherCKMQuantitiesOpenFrontier :
      Bool

    allOtherCKMQuantitiesOpenFrontierIsTrue :
      allOtherCKMQuantitiesOpenFrontier ≡ true

    paper6SupportsPaper8 :
      Bool

    paper6SupportsPaper8IsFalse :
      paper6SupportsPaper8 ≡ false

    paper8RestsOnNSandYMOnly :
      Bool

    paper8RestsOnNSandYMOnlyIsTrue :
      paper8RestsOnNSandYMOnly ≡ true

    paper8Basis :
      String

    paper8BasisIsCanonical :
      paper8Basis ≡ paper8BasisLabel

    blockers :
      List Paper6ScopeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalPaper6ScopeBlockers

    supportFlags :
      List Paper6Paper8Support

    supportFlagsAreEmpty :
      supportFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalPaper6ScopeBoundary

open Paper6ScopeRevisionReceipt public

canonicalPaper6ScopeRevisionReceipt :
  Paper6ScopeRevisionReceipt
canonicalPaper6ScopeRevisionReceipt =
  record
    { presentedThings =
        paper6PresentedThings
    ; presentedThingsAreExactlyCanonical =
        refl
    ; presentedThingCount =
        2
    ; presentedThingCountIsTwo =
        refl
    ; scopedItems =
        canonicalPaper6ScopedItems
    ; scopedItemsAreCanonical =
        refl
    ; lambdaFormula =
        lambdaFormulaLabel
    ; lambdaFormulaIsCanonical =
        refl
    ; lambdaKnownStructuralConnection =
        true
    ; lambdaKnownStructuralConnectionIsTrue =
        refl
    ; lambdaGeorgiJarlskogLiterature =
        true
    ; lambdaGeorgiJarlskogLiteratureIsTrue =
        refl
    ; lambdaNewDASHIResult =
        false
    ; lambdaNewDASHIResultIsFalse =
        refl
    ; vubFormula =
        vubFormulaLabel
    ; vubFormulaIsCanonical =
        refl
    ; vubStructuralHypothesis =
        true
    ; vubStructuralHypothesisIsTrue =
        refl
    ; adjacentOnlyCarrierChain =
        true
    ; adjacentOnlyCarrierChainIsTrue =
        refl
    ; downDiagonalizerApproximatelyIdentity =
        true
    ; downDiagonalizerApproximatelyIdentityIsTrue =
        refl
    ; vubLeadingOrderMatchPercent =
        4.2
    ; vubLeadingOrderMatchPercentIsCanonical =
        refl
    ; vubNextOrderFailurePercent =
        1073.0
    ; vubNextOrderFailurePercentIsCanonical =
        refl
    ; vubNextOrderFailureDocumented =
        true
    ; vubNextOrderFailureDocumentedIsTrue =
        refl
    ; openCKMFrontier =
        canonicalPaper6OpenCKMFrontier
    ; openCKMFrontierIsCanonical =
        refl
    ; allOtherCKMQuantitiesOpenFrontier =
        true
    ; allOtherCKMQuantitiesOpenFrontierIsTrue =
        refl
    ; paper6SupportsPaper8 =
        false
    ; paper6SupportsPaper8IsFalse =
        refl
    ; paper8RestsOnNSandYMOnly =
        true
    ; paper8RestsOnNSandYMOnlyIsTrue =
        refl
    ; paper8Basis =
        paper8BasisLabel
    ; paper8BasisIsCanonical =
        refl
    ; blockers =
        canonicalPaper6ScopeBlockers
    ; blockersAreCanonical =
        refl
    ; supportFlags =
        []
    ; supportFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalPaper6ScopeBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

paper6PresentsExactlyTwoThings :
  presentedThings canonicalPaper6ScopeRevisionReceipt
  ≡
  paper6PresentedThings
paper6PresentsExactlyTwoThings =
  refl

paper6PresentedThingCountIsTwo :
  presentedThingCount canonicalPaper6ScopeRevisionReceipt ≡ 2
paper6PresentedThingCountIsTwo =
  refl

paper6LambdaIsKnownGJConnectionNotNewDASHI :
  lambdaKnownStructuralConnection canonicalPaper6ScopeRevisionReceipt
  ≡
  true
paper6LambdaIsKnownGJConnectionNotNewDASHI =
  refl

paper6LambdaNewDASHIResultFalse :
  lambdaNewDASHIResult canonicalPaper6ScopeRevisionReceipt
  ≡
  false
paper6LambdaNewDASHIResultFalse =
  refl

paper6VubLeadingOrderMatchRecorded :
  vubLeadingOrderMatchPercent canonicalPaper6ScopeRevisionReceipt
  ≡
  4.2
paper6VubLeadingOrderMatchRecorded =
  refl

paper6VubNextOrderFailureRecorded :
  vubNextOrderFailurePercent canonicalPaper6ScopeRevisionReceipt
  ≡
  1073.0
paper6VubNextOrderFailureRecorded =
  refl

paper6AllOtherCKMQuantitiesOpen :
  allOtherCKMQuantitiesOpenFrontier canonicalPaper6ScopeRevisionReceipt
  ≡
  true
paper6AllOtherCKMQuantitiesOpen =
  refl

paper6SupportsPaper8FlagFalse :
  paper6SupportsPaper8 canonicalPaper6ScopeRevisionReceipt
  ≡
  false
paper6SupportsPaper8FlagFalse =
  refl

paper8RestsOnNSandYMOnlyFlagTrue :
  paper8RestsOnNSandYMOnly canonicalPaper6ScopeRevisionReceipt
  ≡
  true
paper8RestsOnNSandYMOnlyFlagTrue =
  refl

paper6NoPaper8SupportFlags :
  supportFlags canonicalPaper6ScopeRevisionReceipt ≡ []
paper6NoPaper8SupportFlags =
  refl
