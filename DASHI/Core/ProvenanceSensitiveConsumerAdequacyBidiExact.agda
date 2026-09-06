module DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as Fly
import DASHI.Core.ConsumerAdequacyJointPolicyBidiCompilerExact as Adequacy

------------------------------------------------------------------------
-- PROVENANCE-SENSITIVE CONSUMER ADEQUACY
--
-- Reverse x-pollination from Lean Integration.Kernel.EvidenceDependence and
-- ConsumerPromotion.  Agda already owns consumer adequacy and Drosophila
-- provenance dependence; this file makes their missing joint condition explicit.
-- No Lean theorem is transported into Agda.
------------------------------------------------------------------------

record ProvenanceAdequacyPolicy
    (Evidence Root Consumer : Set) : Set₁ where
  constructor provenance-adequacy-policy
  field
    rootOf : Evidence → Root → Set
    supports : Evidence → Consumer → Set
    policyReference : String

open ProvenanceAdequacyPolicy public

IndependentSupport :
  ∀ {Evidence Root Consumer : Set} →
  ProvenanceAdequacyPolicy Evidence Root Consumer →
  Evidence → Evidence → Set
IndependentSupport policy left right =
  ∀ root → rootOf policy left root → rootOf policy right root → ⊥

AdequatePairFor :
  ∀ {Evidence Root Consumer : Set} →
  ProvenanceAdequacyPolicy Evidence Root Consumer →
  Consumer → Evidence → Evidence → Set
AdequatePairFor policy consumer left right =
  supports policy left consumer ×
  (supports policy right consumer × IndependentSupport policy left right)

adequatePairCarriesIndependentSupport :
  ∀ {Evidence Root Consumer : Set}
    {policy : ProvenanceAdequacyPolicy Evidence Root Consumer}
    {consumer : Consumer} {left right : Evidence} →
  AdequatePairFor policy consumer left right →
  IndependentSupport policy left right
adequatePairCarriesIndependentSupport receipt = proj₂ (proj₂ receipt)

------------------------------------------------------------------------
-- Finite collision: two visible support items can both support the same
-- consumer while sharing the same relevant root.  Count=2 therefore does not
-- manufacture provenance-independent adequacy.
------------------------------------------------------------------------

data ToyEvidence : Set where firstReport secondReport : ToyEvidence
data ToyRoot : Set where sharedRoot : ToyRoot
data ToyConsumer : Set where targetConsumer : ToyConsumer

toyRootOf : ToyEvidence → ToyRoot → Set
toyRootOf firstReport sharedRoot = ⊤
toyRootOf secondReport sharedRoot = ⊤

toySupports : ToyEvidence → ToyConsumer → Set
toySupports firstReport targetConsumer = ⊤
toySupports secondReport targetConsumer = ⊤

toyPolicy : ProvenanceAdequacyPolicy ToyEvidence ToyRoot ToyConsumer
toyPolicy = provenance-adequacy-policy toyRootOf toySupports
  "two visible supports share one provenance root"

toyBothSupport :
  supports toyPolicy firstReport targetConsumer ×
  supports toyPolicy secondReport targetConsumer
toyBothSupport = tt , tt

toyPairNotIndependent : IndependentSupport toyPolicy firstReport secondReport → ⊥
toyPairNotIndependent independent = independent sharedRoot tt tt

toyVisibleCountDoesNotCloseIndependentAdequacy :
  AdequatePairFor toyPolicy targetConsumer firstReport secondReport → ⊥
toyVisibleCountDoesNotCloseIndependentAdequacy receipt =
  toyPairNotIndependent (adequatePairCarriesIndependentSupport receipt)

record ProvenanceSensitiveAdequacyBoundary : Set where
  constructor provenance-sensitive-adequacy-boundary
  field
    supportCountIsIndependentRootCount : Bool
    sharedRootMayBlockIndependentAdequacy : Bool
    provenanceCanBeConsumerPolicyInput : Bool
    provenanceAdequacyCreatesActionAuthority : Bool

canonicalProvenanceSensitiveAdequacyBoundary :
  ProvenanceSensitiveAdequacyBoundary
canonicalProvenanceSensitiveAdequacyBoundary =
  provenance-sensitive-adequacy-boundary false true true false
