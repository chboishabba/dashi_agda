module DASHI.Core.HeterogeneousPNFObservableBridgeExact where

-- DASHI context-indexed PNF transport: heterogeneous observable spaces.
-- The consumer must provide explicit interpretations into a *common
-- operation-specific* outcome and a preservation proof for the mapping.
-- Mere native ID equality, QID alignment, or source co-occurrence does
-- not construct this licence.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)

import DASHI.Core.ContextIndexedPNFComparisonTransportExact as Base

record HeterogeneousLicence
  (A B OutA OutB Common : Set)
  (observeA : A → OutA)
  (observeB : B → OutB)
  (toCommonA : OutA → Common)
  (toCommonB : OutB → Common) : Set where
  constructor heterogeneous-licence
  field
    mapRepresentation : A → B
    preserveSelectedConsumer :
      ∀ x →
        toCommonB (observeB (mapRepresentation x)) ≡
          toCommonA (observeA x)
open HeterogeneousLicence public

-- A heterogeneous licence transports only the *selected* common
-- observable. Its index includes both original observable functions;
-- it makes no claim about other consumers or other interpretation axes.
heterogeneousConsumerPreservation :
  ∀ {A B OutA OutB Common : Set}
    {a : A → OutA} {b : B → OutB}
    {f : OutA → Common} {g : OutB → Common} →
  (licence : HeterogeneousLicence A B OutA OutB Common a b f g) →
  ∀ x →
    g (b (mapRepresentation licence x)) ≡ f (a x)
heterogeneousConsumerPreservation l = preserveSelectedConsumer l

-- Heterogeneous bridges compose when *the intermediate representation,
-- observable, and embedding into the shared consumer coordinate coincide*.
composeHeterogeneous :
  ∀ {A B C OutA OutB OutC Common : Set}
    {a : A → OutA} {b : B → OutB} {c : C → OutC}
    {f : OutA → Common} {g : OutB → Common} {h : OutC → Common} →
  HeterogeneousLicence A B OutA OutB Common a b f g →
  HeterogeneousLicence B C OutB OutC Common b c g h →
  HeterogeneousLicence A C OutA OutC Common a c f h
composeHeterogeneous l m =
  heterogeneous-licence
    (λ x → mapRepresentation m (mapRepresentation l x))
    (λ x → Base.transEq
      (preserveSelectedConsumer m (mapRepresentation l x))
      (preserveSelectedConsumer l x))

record EvidenceScopedHeterogeneousLicence
  (A B OutA OutB Common : Set)
  (a : A → OutA) (b : B → OutB)
  (f : OutA → Common) (g : OutB → Common) : Set where
  constructor evidence-scoped-licence
  field
    originalSourceRevisions : List String
    consumerRef : String
    licensingEvidenceRefs : List String
    originalProvenanceRefs : List String
    underlyingLicence : HeterogeneousLicence A B OutA OutB Common a b f g
open EvidenceScopedHeterogeneousLicence public

-- The evidence/provenance list is not itself a proof that the
-- original NLP interpretation is correct. The transport proof only
-- applies after its independently sourced premises are discharged.
