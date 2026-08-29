module DASHI.Foundations.Wette1969Rule939ImplicationIntroductionExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.3.9: IMPLICATION INTRODUCTION / CURRYING
--
-- Direct transcription of printed p.145:
--
--   9.3.9   L (w ∧ u) v  ->  L w (u -> v)
--
-- The source writes the pure words without the explanatory parentheses used
-- above.  This owner only reconstructs that historical rule body and its
-- proof-carrying selector; it does not add a semantic deduction theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
import Data.Fin as Fin

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

conjoin : WordTerm → WordTerm → WordTerm
conjoin left right =
  Signature.binaryWordTerm Signature.conjunctionFunctor refl left right

implicationWord : WordTerm → WordTerm → WordTerm
implicationWord left right =
  Signature.binaryWordTerm Signature.implicationFunctor refl left right

rule9-3-9Address : Revision.HistoricalRuleAddress
rule9-3-9Address = Revision.historicalRuleAddress 9 3 9

rule9-3-9 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule9-3-9 w u v =
  RuleBody.historicalRuleBody
    rule9-3-9Address
    1
    (Judgment.implies (conjoin w u) v ∷ᵥ []ᵥ)
    (Judgment.implies w (implicationWord u v))

rule939PremisesHold :
  (context : Context) →
  (w u v : WordTerm) →
  Judgment.implies (conjoin w u) v Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context (rule9-3-9 w u v)
rule939PremisesHold context w u v evidence Fin.zero = evidence

selectRule939 :
  (context : Context) →
  (w u v : WordTerm) →
  Judgment.implies (conjoin w u) v Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule939 context w u v evidence =
  PCRA.selectedRuleApplication
    (rule9-3-9 w u v)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule9-3-9 w u v)
      (rule939PremisesHold context w u v evidence))

rule939HasOnePremise :
  (w u v : WordTerm) →
  RuleBody.premiseCount (rule9-3-9 w u v) ≡ 1
rule939HasOnePremise w u v = refl

rule939HasHistoricalAddress :
  (w u v : WordTerm) →
  RuleBody.address (rule9-3-9 w u v) ≡ rule9-3-9Address
rule939HasHistoricalAddress w u v = refl

rule939ConclusionHasImplicationHead :
  (w u v : WordTerm) →
  RuleBody.conclusion (rule9-3-9 w u v)
    ≡ Judgment.implies w (implicationWord u v)
rule939ConclusionHasImplicationHead w u v = refl

record Wette1969Rule939ImplicationIntroductionBoundary : Set where
  constructor wette1969Rule939ImplicationIntroductionBoundary
  field
    rule939BodyTranscribedFromPrintedP145 : Bool
    rule939BodyTranscribedFromPrintedP145IsTrue :
      rule939BodyTranscribedFromPrintedP145 ≡ true
    rule939HasExactlyOneHistoricalPremise : Bool
    rule939HasExactlyOneHistoricalPremiseIsTrue :
      rule939HasExactlyOneHistoricalPremise ≡ true
    rule939BuildsImplicationInConsequentWord : Bool
    rule939BuildsImplicationInConsequentWordIsTrue :
      rule939BuildsImplicationInConsequentWord ≡ true
    rule939SelectorRequiresActualPremiseEvidence : Bool
    rule939SelectorRequiresActualPremiseEvidenceIsTrue :
      rule939SelectorRequiresActualPremiseEvidence ≡ true
    rule939IsSemanticDeductionTheoremByDefinition : Bool
    rule939IsSemanticDeductionTheoremByDefinitionIsFalse :
      rule939IsSemanticDeductionTheoremByDefinition ≡ false

canonicalWette1969Rule939ImplicationIntroductionBoundary :
  Wette1969Rule939ImplicationIntroductionBoundary
canonicalWette1969Rule939ImplicationIntroductionBoundary =
  wette1969Rule939ImplicationIntroductionBoundary
    true refl true refl true refl true refl false refl
