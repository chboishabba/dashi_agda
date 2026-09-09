module DASHI.Cognition.PNF.SensibLawBrightonS185ViolationElementFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal

------------------------------------------------------------------------
-- BRIGHTON s 185: FIRST SURVIVING VIOLATION-ELEMENT RESIDUAL
--
-- Paid upstream:
--   * exact private Form 11 span -> bounded assertion -> +1 source support;
--   * public historical s 185 source/version envelope;
--   * existing applicability/violation compiler interfaces.
--
-- Not paid by those receipts:
--   whether the premises-condition / maintenance-failure merits proposition is
--   established for the exact event and WrongType.  The Form 11 is a tenant
--   assertion carrier; QSTARS is professional advice; the May QCAT order trail
--   concerns rent/order mechanics and does not state an s 185 premises-condition
--   merits finding in the source material reviewed.
------------------------------------------------------------------------

firstOpenElementReference : String
firstOpenElementReference =
  "Brighton s185 premises-condition / maintenance-failure merits element"

firstOpenElementEvaluation :
  (wrongTypeReference : DASHI.Interop.SensibLawOntologyTopology.StableId) →
  Legal.WrongElementEvaluation
firstOpenElementEvaluation wrong =
  Legal.wrongElementEvaluation
    wrong
    firstOpenElementReference
    Legal.elementUnresolved
    []
    "unresolved pending same-event merits evidence; assertion/advice/order-process carriers do not substitute"

firstOpenElementDispositionIsUnresolved :
  ∀ wrong →
  Legal.disposition (firstOpenElementEvaluation wrong) ≡ Legal.elementUnresolved
firstOpenElementDispositionIsUnresolved wrong = refl

data Form11AssertionPaysMeritsElement : Set where
data QSTARSAdvicePaysMeritsElement : Set where
data RentOrderPaysS185ConditionElement : Set where
data LaterExitCarrierAutomaticallyPaysJanuaryCondition : Set where

form11AssertionDoesNotPayMeritsElement : Form11AssertionPaysMeritsElement → ⊥
form11AssertionDoesNotPayMeritsElement ()

qstarsAdviceDoesNotPayMeritsElement : QSTARSAdvicePaysMeritsElement → ⊥
qstarsAdviceDoesNotPayMeritsElement ()

rentOrderDoesNotPayS185ConditionElement : RentOrderPaysS185ConditionElement → ⊥
rentOrderDoesNotPayS185ConditionElement ()

laterExitCarrierDoesNotAutoPayJanuaryCondition :
  LaterExitCarrierAutomaticallyPaysJanuaryCondition → ⊥
laterExitCarrierDoesNotAutoPayJanuaryCondition ()

record BrightonS185ViolationElementFrontierBoundary : Set where
  constructor brighton-s185-violation-element-frontier-boundary
  field
    firstOpenElementExplicit : Bool
    elementDispositionUnresolved : Bool
    requiresSameEventMeritsEvidence : Bool
    form11AssertionPaysMerits : Bool
    qstarsAdvicePaysMerits : Bool
    rentOrderPaysConditionMerits : Bool
    laterExitCarrierAutomaticallyPaysJanuaryCondition : Bool

canonicalBrightonS185ViolationElementFrontierBoundary :
  BrightonS185ViolationElementFrontierBoundary
canonicalBrightonS185ViolationElementFrontierBoundary =
  brighton-s185-violation-element-frontier-boundary
    true true true false false false false
