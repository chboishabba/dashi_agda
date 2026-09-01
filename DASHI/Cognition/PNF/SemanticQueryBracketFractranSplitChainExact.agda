module DASHI.Cognition.PNF.SemanticQueryBracketFractranSplitChainExact where

-- End-to-end finite BIDI witness:
--
--   coarse query -> non-distinguishing orbit -> bracket unavailable
--                -> distinguishing FRACTRAN rule disabled
--
--   finer provenance query -> worlds distinguishable -> bracket available
--                           -> rule enabled -> residual split authorised
--
-- This composes existing semantic-query and FRACTRAN-divisibility owners; it
-- does not claim every semantic query is compiled to prime 47 in production.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SemanticQueryResidualFibreSSSPBridgeExact as Query
import DASHI.Cognition.PNF.SemanticBracketFractranDivisibilityExact as Bracket
import DASHI.Biology.FRACTRANSSPTransitionExact as F

------------------------------------------------------------------------
-- 1. Compile the finite query refinement to the bracket gate.
------------------------------------------------------------------------

bracketForQuery : Query.ExampleQuery → Bracket.DiscriminatorBracket
bracketForQuery Query.coarseIdentityQuery = Bracket.bracketUnavailable
bracketForQuery Query.provenanceQuery = Bracket.bracketAvailable

coarseQueryUsesUnavailableBracket :
  bracketForQuery Query.coarseIdentityQuery ≡ Bracket.bracketUnavailable
coarseQueryUsesUnavailableBracket = refl

provenanceQueryUsesAvailableBracket :
  bracketForQuery Query.provenanceQuery ≡ Bracket.bracketAvailable
provenanceQueryUsesAvailableBracket = refl

------------------------------------------------------------------------
-- 2. Coarse query: worlds collapse and the distinguishing arithmetic rule is
--    disabled.
------------------------------------------------------------------------

coarseWorldsStillObservationEquivalent :
  Query.exampleObserve Query.coarseIdentityQuery Query.canonicalReferent ≡
  Query.exampleObserve Query.coarseIdentityQuery Query.impersonatorReferent
coarseWorldsStillObservationEquivalent = Query.coarseWorldsObservationEqual

coarseQueryDistinguishingRuleDisabled :
  F.ruleEnabled F.transfer47To59
    (Bracket.compileBracket (bracketForQuery Query.coarseIdentityQuery))
  ≡ false
coarseQueryDistinguishingRuleDisabled = refl

coarseQueryCannotAuthoriseResidualSplit :
  Bracket.ResidualSplitPermission
    (bracketForQuery Query.coarseIdentityQuery) →
  ⊥
coarseQueryCannotAuthoriseResidualSplit =
  Bracket.unavailableBracketCannotAuthoriseSplit

------------------------------------------------------------------------
-- 3. Finer query: the previous fibre is distinguishable, the gate opens, and
--    the split permission is inhabited.
------------------------------------------------------------------------

provenanceWorldsAreDistinguished :
  (Query.exampleObserve Query.provenanceQuery Query.canonicalReferent ≡
   Query.exampleObserve Query.provenanceQuery Query.impersonatorReferent) →
  ⊥
provenanceWorldsAreDistinguished = Query.provenanceWorldsSeparate

provenanceQueryDistinguishingRuleEnabled :
  F.ruleEnabled F.transfer47To59
    (Bracket.compileBracket (bracketForQuery Query.provenanceQuery))
  ≡ true
provenanceQueryDistinguishingRuleEnabled = refl

provenanceQueryAuthorisesResidualSplit :
  Bracket.ResidualSplitPermission
    (bracketForQuery Query.provenanceQuery)
provenanceQueryAuthorisesResidualSplit = Bracket.bracketAuthorisesSplit

------------------------------------------------------------------------
-- 4. End-to-end scope boundary.
------------------------------------------------------------------------

record QueryBracketSplitChainBoundary : Set where
  constructor queryBracketSplitChainBoundary
  field
    coarseQueryCollapsesWorlds : Bool
    coarseQueryCollapsesWorldsIsTrue : coarseQueryCollapsesWorlds ≡ true
    coarseQueryLeavesGateClosed : Bool
    coarseQueryLeavesGateClosedIsTrue : coarseQueryLeavesGateClosed ≡ true
    finerQuerySeparatesWorlds : Bool
    finerQuerySeparatesWorldsIsTrue : finerQuerySeparatesWorlds ≡ true
    finerQueryOpensGate : Bool
    finerQueryOpensGateIsTrue : finerQueryOpensGate ≡ true
    queryMeaningInferredFromPrimeWithoutCompiler : Bool
    queryMeaningInferredFromPrimeWithoutCompilerIsFalse :
      queryMeaningInferredFromPrimeWithoutCompiler ≡ false

canonicalQueryBracketSplitChainBoundary : QueryBracketSplitChainBoundary
canonicalQueryBracketSplitChainBoundary =
  queryBracketSplitChainBoundary
    true refl true refl true refl true refl false refl
