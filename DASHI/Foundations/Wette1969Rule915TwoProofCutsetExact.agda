module DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: TWO DECISIVE L-PROOF CUTSET
--
-- Section 1.632 identifies premises 18 and 27 as the two decisive substantive
-- L obligations. Once the formation/freshness/tuple/concatenation/substitution/
-- abbreviation scaffold is available, the only remaining premise evidence
-- needed by 9.1.5 is therefore the proof of premise 18 plus the proof of 27.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969Rule915CertifiedObligationApplicationExact as Certified915
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Later.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record Rule915SyntacticScaffoldEvidence
    (context : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set where
  constructor rule915SyntacticScaffoldEvidence
  field
    p01 : Rule915.premise915-01 firstSeven Finite.∈Context context
    p02 : Rule915.premise915-02 firstSeven Finite.∈Context context
    p03 : Rule915.premise915-03 firstSeven Finite.∈Context context
    p04 : Rule915.premise915-04 firstSeven Finite.∈Context context
    p05 : Rule915.premise915-05 firstSeven Finite.∈Context context
    p06 : Rule915.premise915-06 firstSeven Finite.∈Context context
    p07 : Rule915.premise915-07 firstSeven Finite.∈Context context

    p08 : Later.premise08 later Finite.∈Context context
    p09 : Later.premise09 later Finite.∈Context context
    p10 : Later.premise10 later Finite.∈Context context
    p11 : Later.premise11 later Finite.∈Context context
    p12 : Later.premise12 later Finite.∈Context context
    p13 : Later.premise13 later Finite.∈Context context
    p14 : Later.premise14 later Finite.∈Context context
    p15 : Later.premise15 later Finite.∈Context context
    p16 : Later.premise16 later Finite.∈Context context
    p17 : Later.premise17 later Finite.∈Context context

    p19 : Later.premise19 later Finite.∈Context context
    p20 : Later.premise20 later Finite.∈Context context
    p21 : Later.premise21 later Finite.∈Context context
    p22 : Later.premise22 later Finite.∈Context context
    p23 : Later.premise23 later Finite.∈Context context
    p24 : Later.premise24 later Finite.∈Context context
    p25 : Later.premise25 later Finite.∈Context context
    p26 : Later.premise26 later Finite.∈Context context

open Rule915SyntacticScaffoldEvidence public

record Rule915MajorProofEvidence
    (context : Context)
    (later : Later.Rule915LaterParameters) : Set where
  constructor rule915MajorProofEvidence
  field
    predecessorInductionProof : Later.premise18 later Finite.∈Context context
    definiensIndependenceProof : Later.premise27 later Finite.∈Context context

open Rule915MajorProofEvidence public

cutsetToObligationEvidence :
  {context : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  Rule915SyntacticScaffoldEvidence context firstSeven later →
  Rule915MajorProofEvidence context later →
  Obligations.Rule915ObligationEvidence
    context
    (Later.completeTypedTranscription firstSeven later)
cutsetToObligationEvidence firstSeven later scaffold major =
  Obligations.rule915ObligationEvidence
    (Obligations.firstSevenEvidence
      (p01 scaffold) (p02 scaffold) (p03 scaffold) (p04 scaffold)
      (p05 scaffold) (p06 scaffold) (p07 scaffold))
    shared
    (Obligations.predecessorInductionBranch
      (p08 scaffold) (p09 scaffold)
      (p16 scaffold) (p17 scaffold)
      (predecessorInductionProof major))
    (Obligations.definiensIndependenceBranch
      (p19 scaffold) (p20 scaffold) (p21 scaffold)
      (p22 scaffold) (p23 scaffold) (p24 scaffold) (p25 scaffold)
      (p26 scaffold) (definiensIndependenceProof major))
  where
    shared = Obligations.shared1015Evidence
      (p10 scaffold) (p11 scaffold) (p12 scaffold)
      (p13 scaffold) (p14 scaffold) (p15 scaffold)

selectRule915FromTwoProofCutset :
  {context : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (recursivePredicate : WordTerm) →
  Rule915SyntacticScaffoldEvidence context firstSeven later →
  Rule915MajorProofEvidence context later →
  PCRA.SelectedRuleApplication historicalSystem context
selectRule915FromTwoProofCutset
  {context} firstSeven later recursivePredicate scaffold major =
  Certified915.selectRule915FromObligationEvidence
    context
    (Later.completeTypedTranscription firstSeven later)
    (Later.arityWord later)
    recursivePredicate
    (cutsetToObligationEvidence firstSeven later scaffold major)

record Wette1969Rule915TwoProofCutsetBoundary : Set where
  constructor wette1969Rule915TwoProofCutsetBoundary
  field
    rule915EvidenceFactorsIntoScaffoldPlusTwoMajorProofs : Bool
    rule915EvidenceFactorsIntoScaffoldPlusTwoMajorProofsIsTrue :
      rule915EvidenceFactorsIntoScaffoldPlusTwoMajorProofs ≡ true
    premise18IsExplicitPredecessorInductionProofSocket : Bool
    premise18IsExplicitPredecessorInductionProofSocketIsTrue :
      premise18IsExplicitPredecessorInductionProofSocket ≡ true
    premise27IsExplicitDefiniensIndependenceProofSocket : Bool
    premise27IsExplicitDefiniensIndependenceProofSocketIsTrue :
      premise27IsExplicitDefiniensIndependenceProofSocket ≡ true
    syntacticScaffoldAlreadyGeneratedFromEmptyContext : Bool
    syntacticScaffoldAlreadyGeneratedFromEmptyContextIsFalse :
      syntacticScaffoldAlreadyGeneratedFromEmptyContext ≡ false
    twoProofCutsetAlreadyDischargesEitherMajorProof : Bool
    twoProofCutsetAlreadyDischargesEitherMajorProofIsFalse :
      twoProofCutsetAlreadyDischargesEitherMajorProof ≡ false

canonicalWette1969Rule915TwoProofCutsetBoundary :
  Wette1969Rule915TwoProofCutsetBoundary
canonicalWette1969Rule915TwoProofCutsetBoundary =
  wette1969Rule915TwoProofCutsetBoundary
    true refl true refl true refl false refl false refl
