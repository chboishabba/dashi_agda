module DASHI.Foundations.Wette1969Rule8211RecursorSubstitutionExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 8.2.11: PROOF-CARRYING RECURSOR SUBSTITUTION ADAPTER
--
-- The literal historical rule body is owned by
-- Wette1969SubstitutionRuleSpineExact.  This module adds only the recovered
-- recursor-binder specialization and proof-carrying finite-context application;
-- it deliberately does not duplicate the rule table.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Fin as Fin

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969SubstitutionRuleSpineExact as Spine
import DASHI.Foundations.Wette1969RecursorBindingScopeExact as Recursor
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

recursor : WordTerm → WordTerm → WordTerm
recursor = Spine.binary Signature.recursionFunctor

rule8-2-11 : Spine.BinderRuleType
rule8-2-11 = Spine.rule8-2-11

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
  ≡ Judgment.substitution substituend
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
  Judgment.substitution substituend
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
    substitutionSpineOwnsLiteralRule8211 : Bool
    substitutionSpineOwnsLiteralRule8211IsTrue :
      substitutionSpineOwnsLiteralRule8211 ≡ true
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
    true refl true refl true refl false refl
