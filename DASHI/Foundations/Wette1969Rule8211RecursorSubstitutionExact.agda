module DASHI.Foundations.Wette1969Rule8211RecursorSubstitutionExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 8.2.11: SUBSTITUTION THROUGH THE RECURSOR
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
--
-- Printed p.144 gives the recursor propagation rule in the form
--
--   J V W1, J V W, II W u W1 u1
--     -> II W (-1 V u) W1 (-1 V u1).
--
-- Section 1.62/1.63 says that 8.1.11/8.2.11 transfer the quantifier treatment
-- to the recursor and that confusion freedom for the recursor depends on its
-- binding regime.  Combined with the recovered B2 binder package, this rule is
-- the first historical bridge from a certified substitution in the definiens to
-- a certified substitution through the recursor itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
import Data.Fin as Fin

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision
import DASHI.Foundations.Wette1969RecursorBindingScopeExact as Recursor
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

recursor : WordTerm → WordTerm → WordTerm
recursor binder body =
  Signature.binaryWordTerm Signature.recursionFunctor refl binder body

rule8-2-11Address : Revision.HistoricalRuleAddress
rule8-2-11Address = Revision.historicalRuleAddress 8 2 11

rule8-2-11 :
  (binder substituend body replacement result : WordTerm) →
  RuleBody.HistoricalRuleBody
rule8-2-11 binder substituend body replacement result =
  RuleBody.historicalRuleBody
    rule8-2-11Address
    3
    ( Judgment.freeForSyntax binder replacement
    ∷ᵥ Judgment.freeForSyntax binder substituend
    ∷ᵥ Judgment.substitution substituend body replacement result
    ∷ᵥ []ᵥ )
    (Judgment.substitution
      substituend
      (recursor binder body)
      replacement
      (recursor binder result))

rule8211ForRecoveredBinder :
  (target : Recursor.RecursorBinderTarget) →
  (substituend body replacement result : WordTerm) →
  RuleBody.HistoricalRuleBody
rule8211ForRecoveredBinder target =
  rule8-2-11 (Recursor.binderPackage target)

rule8211HasThreePremises :
  (binder substituend body replacement result : WordTerm) →
  RuleBody.premiseCount
    (rule8-2-11 binder substituend body replacement result) ≡ 3
rule8211HasThreePremises binder substituend body replacement result = refl

rule8211PropagatesBodySubstitutionThroughRecursor :
  (binder substituend body replacement result : WordTerm) →
  RuleBody.conclusion
    (rule8-2-11 binder substituend body replacement result)
  ≡ Judgment.substitution
      substituend
      (recursor binder body)
      replacement
      (recursor binder result)
rule8211PropagatesBodySubstitutionThroughRecursor
  binder substituend body replacement result = refl

rule8211PremisesHold :
  (context : Context) →
  (binder substituend body replacement result : WordTerm) →
  Judgment.freeForSyntax binder replacement Finite.∈Context context →
  Judgment.freeForSyntax binder substituend Finite.∈Context context →
  Judgment.substitution substituend body replacement result
    Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    context
    (rule8-2-11 binder substituend body replacement result)
rule8211PremisesHold
  context binder substituend body replacement result
  replacementFresh substituendFresh bodySubstitution Fin.zero = replacementFresh
rule8211PremisesHold
  context binder substituend body replacement result
  replacementFresh substituendFresh bodySubstitution
  (Fin.suc Fin.zero) = substituendFresh
rule8211PremisesHold
  context binder substituend body replacement result
  replacementFresh substituendFresh bodySubstitution
  (Fin.suc (Fin.suc Fin.zero)) = bodySubstitution

selectRule8211 :
  (context : Context) →
  (binder substituend body replacement result : WordTerm) →
  Judgment.freeForSyntax binder replacement Finite.∈Context context →
  Judgment.freeForSyntax binder substituend Finite.∈Context context →
  Judgment.substitution substituend body replacement result
    Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule8211
  context binder substituend body replacement result
  replacementFresh substituendFresh bodySubstitution =
  PCRA.selectedRuleApplication
    (rule8-2-11 binder substituend body replacement result)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem
      context
      (rule8-2-11 binder substituend body replacement result)
      (rule8211PremisesHold
        context binder substituend body replacement result
        replacementFresh substituendFresh bodySubstitution))

recursorSubstitutionAvailableAfter8211 :
  (context : Context) →
  (binder substituend body replacement result : WordTerm) →
  (replacementFresh :
    Judgment.freeForSyntax binder replacement Finite.∈Context context) →
  (substituendFresh :
    Judgment.freeForSyntax binder substituend Finite.∈Context context) →
  (bodySubstitution :
    Judgment.substitution substituend body replacement result
      Finite.∈Context context) →
  Judgment.substitution
    substituend
    (recursor binder body)
    replacement
    (recursor binder result)
    Finite.∈Context
    (PCRA.applySelected
      (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
      (selectRule8211
        context binder substituend body replacement result
        replacementFresh substituendFresh bodySubstitution))
recursorSubstitutionAvailableAfter8211
  context binder substituend body replacement result
  replacementFresh substituendFresh bodySubstitution = Finite.here

record Wette1969Rule8211RecursorSubstitutionBoundary : Set where
  constructor wette1969Rule8211RecursorSubstitutionBoundary
  field
    rule8211NowLiteralHistoricalBody : Bool
    rule8211NowLiteralHistoricalBodyIsTrue :
      rule8211NowLiteralHistoricalBody ≡ true

    recoveredPiXBinderCanInstantiateRule8211 : Bool
    recoveredPiXBinderCanInstantiateRule8211IsTrue :
      recoveredPiXBinderCanInstantiateRule8211 ≡ true

    certifiedBodySubstitutionCanGenerateRecursorSubstitution : Bool
    certifiedBodySubstitutionCanGenerateRecursorSubstitutionIsTrue :
      certifiedBodySubstitutionCanGenerateRecursorSubstitution ≡ true

    rule8211AloneIsTotalCaptureAvoidingSubstitutionEvaluator : Bool
    rule8211AloneIsTotalCaptureAvoidingSubstitutionEvaluatorIsFalse :
      rule8211AloneIsTotalCaptureAvoidingSubstitutionEvaluator ≡ false

canonicalWette1969Rule8211RecursorSubstitutionBoundary :
  Wette1969Rule8211RecursorSubstitutionBoundary
canonicalWette1969Rule8211RecursorSubstitutionBoundary =
  wette1969Rule8211RecursorSubstitutionBoundary
    true refl
    true refl
    true refl
    false refl
