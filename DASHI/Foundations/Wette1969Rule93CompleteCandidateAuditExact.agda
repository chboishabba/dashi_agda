module DASHI.Foundations.Wette1969Rule93CompleteCandidateAuditExact where

------------------------------------------------------------------------
-- WETTE 1969: COMPLETE 9.3.1--30 CANDIDATE AUDIT FOR PREMISE 18
--
-- Primary source: printed p.145 of Wette 1969.  Section 1.61 explicitly calls
-- 9.3.1--30 the thirty implication rules.  This module gives every printed
-- candidate one source-stable constructor, records its printed premise count,
-- and classifies its source role for backward proof search.
--
-- The classification is intentionally conservative.  Only 9.3.9 is marked as
-- the direct rule whose conclusion *constructs an implication in the consequent
-- word* (L (w ∧ u) v -> L w (u -> v)).  Other schematic rules remain available
-- for further unification rather than being rejected merely because their
-- displayed metavariables look different from premise 18.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

data Rule93Candidate : Set where
  r931 r932 r933 r934 r935 r936 r937 r938 r939 r9310 : Rule93Candidate
  r9311 r9312 r9313 r9314 r9315 r9316 r9317 r9318 r9319 r9320 : Rule93Candidate
  r9321 r9322 r9323 r9324 r9325 r9326 r9327 r9328 r9329 r9330 : Rule93Candidate

candidateItem : Rule93Candidate → Nat
candidateItem r931 = 1
candidateItem r932 = 2
candidateItem r933 = 3
candidateItem r934 = 4
candidateItem r935 = 5
candidateItem r936 = 6
candidateItem r937 = 7
candidateItem r938 = 8
candidateItem r939 = 9
candidateItem r9310 = 10
candidateItem r9311 = 11
candidateItem r9312 = 12
candidateItem r9313 = 13
candidateItem r9314 = 14
candidateItem r9315 = 15
candidateItem r9316 = 16
candidateItem r9317 = 17
candidateItem r9318 = 18
candidateItem r9319 = 19
candidateItem r9320 = 20
candidateItem r9321 = 21
candidateItem r9322 = 22
candidateItem r9323 = 23
candidateItem r9324 = 24
candidateItem r9325 = 25
candidateItem r9326 = 26
candidateItem r9327 = 27
candidateItem r9328 = 28
candidateItem r9329 = 29
candidateItem r9330 = 30

candidateAddress : Rule93Candidate → Revision.HistoricalRuleAddress
candidateAddress candidate =
  Revision.historicalRuleAddress 9 3 (candidateItem candidate)

printedPremiseCount : Rule93Candidate → Nat
printedPremiseCount r931 = 2
printedPremiseCount r932 = 1
printedPremiseCount r933 = 2
printedPremiseCount r934 = 2
printedPremiseCount r935 = 2
printedPremiseCount r936 = 2
printedPremiseCount r937 = 2
printedPremiseCount r938 = 2
printedPremiseCount r939 = 1
printedPremiseCount r9310 = 1
printedPremiseCount r9311 = 1
printedPremiseCount r9312 = 1
printedPremiseCount r9313 = 4
printedPremiseCount r9314 = 3
printedPremiseCount r9315 = 4
printedPremiseCount r9316 = 3
printedPremiseCount r9317 = 1
printedPremiseCount r9318 = 1
printedPremiseCount r9319 = 0
printedPremiseCount r9320 = 0
printedPremiseCount r9321 = 0
printedPremiseCount r9322 = 0
printedPremiseCount r9323 = 5
printedPremiseCount r9324 = 4
printedPremiseCount r9325 = 4
printedPremiseCount r9326 = 6
printedPremiseCount r9327 = 4
printedPremiseCount r9328 = 3
printedPremiseCount r9329 = 4
printedPremiseCount r9330 = 3

data Rule93SourceRole : Set where
  implicationComposition : Rule93SourceRole
  implicationReflexivity : Rule93SourceRole
  affirmativeConnective : Rule93SourceRole
  implicationIntroduction : Rule93SourceRole
  implicationEliminationToConjunction : Rule93SourceRole
  exFalsoOrVerum : Rule93SourceRole
  quantifierTransport : Rule93SourceRole
  primitivePredicateOrInduction : Rule93SourceRole
  recursiveDefinitionConversion : Rule93SourceRole
  predicateMarkEquality : Rule93SourceRole
  predicateFormLogic : Rule93SourceRole

sourceRole : Rule93Candidate → Rule93SourceRole
sourceRole r931 = implicationComposition
sourceRole r932 = implicationReflexivity
sourceRole r933 = affirmativeConnective
sourceRole r934 = affirmativeConnective
sourceRole r935 = affirmativeConnective
sourceRole r936 = affirmativeConnective
sourceRole r937 = affirmativeConnective
sourceRole r938 = affirmativeConnective
sourceRole r939 = implicationIntroduction
sourceRole r9310 = implicationEliminationToConjunction
sourceRole r9311 = exFalsoOrVerum
sourceRole r9312 = exFalsoOrVerum
sourceRole r9313 = quantifierTransport
sourceRole r9314 = quantifierTransport
sourceRole r9315 = quantifierTransport
sourceRole r9316 = quantifierTransport
sourceRole r9317 = primitivePredicateOrInduction
sourceRole r9318 = primitivePredicateOrInduction
sourceRole r9319 = primitivePredicateOrInduction
sourceRole r9320 = primitivePredicateOrInduction
sourceRole r9321 = primitivePredicateOrInduction
sourceRole r9322 = primitivePredicateOrInduction
sourceRole r9323 = primitivePredicateOrInduction
sourceRole r9324 = recursiveDefinitionConversion
sourceRole r9325 = recursiveDefinitionConversion
sourceRole r9326 = predicateMarkEquality
sourceRole r9327 = predicateFormLogic
sourceRole r9328 = predicateFormLogic
sourceRole r9329 = predicateFormLogic
sourceRole r9330 = predicateFormLogic

data Premise18ConclusionFilter : Set where
  directOuterImplicationIntroduction : Premise18ConclusionFilter
  requiresFurtherUnification : Premise18ConclusionFilter

premise18ConclusionFilter : Rule93Candidate → Premise18ConclusionFilter
premise18ConclusionFilter r939 = directOuterImplicationIntroduction
premise18ConclusionFilter r931 = requiresFurtherUnification
premise18ConclusionFilter r932 = requiresFurtherUnification
premise18ConclusionFilter r933 = requiresFurtherUnification
premise18ConclusionFilter r934 = requiresFurtherUnification
premise18ConclusionFilter r935 = requiresFurtherUnification
premise18ConclusionFilter r936 = requiresFurtherUnification
premise18ConclusionFilter r937 = requiresFurtherUnification
premise18ConclusionFilter r938 = requiresFurtherUnification
premise18ConclusionFilter r9310 = requiresFurtherUnification
premise18ConclusionFilter r9311 = requiresFurtherUnification
premise18ConclusionFilter r9312 = requiresFurtherUnification
premise18ConclusionFilter r9313 = requiresFurtherUnification
premise18ConclusionFilter r9314 = requiresFurtherUnification
premise18ConclusionFilter r9315 = requiresFurtherUnification
premise18ConclusionFilter r9316 = requiresFurtherUnification
premise18ConclusionFilter r9317 = requiresFurtherUnification
premise18ConclusionFilter r9318 = requiresFurtherUnification
premise18ConclusionFilter r9319 = requiresFurtherUnification
premise18ConclusionFilter r9320 = requiresFurtherUnification
premise18ConclusionFilter r9321 = requiresFurtherUnification
premise18ConclusionFilter r9322 = requiresFurtherUnification
premise18ConclusionFilter r9323 = requiresFurtherUnification
premise18ConclusionFilter r9324 = requiresFurtherUnification
premise18ConclusionFilter r9325 = requiresFurtherUnification
premise18ConclusionFilter r9326 = requiresFurtherUnification
premise18ConclusionFilter r9327 = requiresFurtherUnification
premise18ConclusionFilter r9328 = requiresFurtherUnification
premise18ConclusionFilter r9329 = requiresFurtherUnification
premise18ConclusionFilter r9330 = requiresFurtherUnification

isDirectOuterImplicationIntroduction : Rule93Candidate → Bool
isDirectOuterImplicationIntroduction r939 = true
isDirectOuterImplicationIntroduction r931 = false
isDirectOuterImplicationIntroduction r932 = false
isDirectOuterImplicationIntroduction r933 = false
isDirectOuterImplicationIntroduction r934 = false
isDirectOuterImplicationIntroduction r935 = false
isDirectOuterImplicationIntroduction r936 = false
isDirectOuterImplicationIntroduction r937 = false
isDirectOuterImplicationIntroduction r938 = false
isDirectOuterImplicationIntroduction r9310 = false
isDirectOuterImplicationIntroduction r9311 = false
isDirectOuterImplicationIntroduction r9312 = false
isDirectOuterImplicationIntroduction r9313 = false
isDirectOuterImplicationIntroduction r9314 = false
isDirectOuterImplicationIntroduction r9315 = false
isDirectOuterImplicationIntroduction r9316 = false
isDirectOuterImplicationIntroduction r9317 = false
isDirectOuterImplicationIntroduction r9318 = false
isDirectOuterImplicationIntroduction r9319 = false
isDirectOuterImplicationIntroduction r9320 = false
isDirectOuterImplicationIntroduction r9321 = false
isDirectOuterImplicationIntroduction r9322 = false
isDirectOuterImplicationIntroduction r9323 = false
isDirectOuterImplicationIntroduction r9324 = false
isDirectOuterImplicationIntroduction r9325 = false
isDirectOuterImplicationIntroduction r9326 = false
isDirectOuterImplicationIntroduction r9327 = false
isDirectOuterImplicationIntroduction r9328 = false
isDirectOuterImplicationIntroduction r9329 = false
isDirectOuterImplicationIntroduction r9330 = false

rule939IsDirectOuterImplicationIntroduction :
  isDirectOuterImplicationIntroduction r939 ≡ true
rule939IsDirectOuterImplicationIntroduction = refl

record Wette1969Rule93CompleteCandidateAuditBoundary : Set where
  constructor wette1969Rule93CompleteCandidateAuditBoundary
  field
    allThirtyPrintedCandidatesHaveExplicitConstructors : Bool
    allThirtyPrintedCandidatesHaveExplicitConstructorsIsTrue :
      allThirtyPrintedCandidatesHaveExplicitConstructors ≡ true
    allThirtyPrintedPremiseCountsRecorded : Bool
    allThirtyPrintedPremiseCountsRecordedIsTrue :
      allThirtyPrintedPremiseCountsRecorded ≡ true
    allThirtyCandidatesHaveSourceRoleClassification : Bool
    allThirtyCandidatesHaveSourceRoleClassificationIsTrue :
      allThirtyCandidatesHaveSourceRoleClassification ≡ true
    rule939IsUniqueExplicitDirectImplicationBuilderInThisClassification : Bool
    rule939IsUniqueExplicitDirectImplicationBuilderInThisClassificationIsTrue :
      rule939IsUniqueExplicitDirectImplicationBuilderInThisClassification ≡ true
    non939CandidatesAreRejectedWithoutUnification : Bool
    non939CandidatesAreRejectedWithoutUnificationIsFalse :
      non939CandidatesAreRejectedWithoutUnification ≡ false
    completeCandidateAuditAlreadyProvesPremise18 : Bool
    completeCandidateAuditAlreadyProvesPremise18IsFalse :
      completeCandidateAuditAlreadyProvesPremise18 ≡ false

canonicalWette1969Rule93CompleteCandidateAuditBoundary :
  Wette1969Rule93CompleteCandidateAuditBoundary
canonicalWette1969Rule93CompleteCandidateAuditBoundary =
  wette1969Rule93CompleteCandidateAuditBoundary
    true refl true refl true refl true refl false refl false refl
