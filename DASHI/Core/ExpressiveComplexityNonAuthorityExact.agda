module DASHI.Core.ExpressiveComplexityNonAuthorityExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.QueryFactorisationSufficiency as Factor

------------------------------------------------------------------------
-- EXPRESSIVE COMPLEXITY IS NOT SEMANTIC / EVIDENTIAL AUTHORITY
--
-- If a declared consumer factors through a semantic representation, then any
-- independent complexity coordinate (verbosity, vocabulary, rhetorical
-- sophistication, reading level, etc.) cannot silently alter that consumer.
-- Complexity may still be an explicitly declared consumer axis in applications.
------------------------------------------------------------------------

record ExpressiveAsymmetryWitness
    {State Semantic Complexity : Set}
    (semantic : State → Semantic)
    (complexity : State → Complexity) : Set where
  constructor expressiveAsymmetryWitness
  field
    left right : State
    sameSemantic : semantic left ≡ semantic right
    differentComplexity : complexity left ≡ complexity right → ⊥

open ExpressiveAsymmetryWitness public

factorizedQueryIgnoresIndependentComplexity :
  ∀ {State Semantic Complexity Query : Set}
    {questions : Factor.InquiryQuestionFamily State Query}
    {semantic : State → Semantic}
    (complexity : State → Complexity)
    {query : Query} →
  Factor.FactorsThrough questions semantic query →
  (left right : State) →
  semantic left ≡ semantic right →
  Factor.ask questions query left ≡ Factor.ask questions query right
factorizedQueryIgnoresIndependentComplexity complexity factor left right same =
  trans
    (Factor.factorisation factor left)
    (trans
      (cong (Factor.quotientAnswer factor) same)
      (sym (Factor.factorisation factor right)))

expressiveAsymmetryCannotChangeQuery :
  ∀ {State Semantic Complexity Query : Set}
    {questions : Factor.InquiryQuestionFamily State Query}
    {semantic : State → Semantic}
    {complexity : State → Complexity}
    {query : Query} →
  Factor.FactorsThrough questions semantic query →
  (witness : ExpressiveAsymmetryWitness semantic complexity) →
  Factor.ask questions query (left witness)
  ≡ Factor.ask questions query (right witness)
expressiveAsymmetryCannotChangeQuery {complexity = complexity} factor witness =
  factorizedQueryIgnoresIndependentComplexity complexity factor
    (left witness) (right witness) (sameSemantic witness)

record ExpressiveComplexityBoundary : Set where
  constructor expressiveComplexityBoundary
  field
    verbosityAutomaticallyAddsSemanticWeight : Bool
    rhetoricAutomaticallyAddsEvidentialAuthority : Bool
    consumerMayExplicitlyDeclareComplexityAxis : Bool
    factorizedConsumerIsInvariantToUndeclaredComplexity : Bool

canonicalExpressiveComplexityBoundary : ExpressiveComplexityBoundary
canonicalExpressiveComplexityBoundary =
  expressiveComplexityBoundary false false true true
