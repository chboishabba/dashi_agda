module DASHI.Core.ProvenanceQuorumAdequacyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact as Provenance

------------------------------------------------------------------------
-- HEADCOUNT QUORUM != INDEPENDENT-PROVENANCE QUORUM
--
-- Two visible supporting items may satisfy a headcount threshold while sharing
-- one ultimate provenance root. Independent corroboration therefore requires a
-- separate root-separation receipt, not merely enough supporting documents.
------------------------------------------------------------------------

HeadcountQuorumTwo :
  ∀ {Evidence Root Consumer : Set} →
  Provenance.ProvenanceAdequacyPolicy Evidence Root Consumer →
  Consumer → Evidence → Evidence → Set
HeadcountQuorumTwo policy consumer left right =
  Provenance.supports policy left consumer ×
  Provenance.supports policy right consumer

IndependentProvenanceQuorumTwo :
  ∀ {Evidence Root Consumer : Set} →
  Provenance.ProvenanceAdequacyPolicy Evidence Root Consumer →
  Consumer → Evidence → Evidence → Set
IndependentProvenanceQuorumTwo = Provenance.AdequatePairFor

independentQuorumCarriesHeadcount :
  ∀ {Evidence Root Consumer : Set}
    {policy : Provenance.ProvenanceAdequacyPolicy Evidence Root Consumer}
    {consumer : Consumer} {left right : Evidence} →
  IndependentProvenanceQuorumTwo policy consumer left right →
  HeadcountQuorumTwo policy consumer left right
independentQuorumCarriesHeadcount receipt =
  proj₁ receipt , proj₁ (proj₂ receipt)

------------------------------------------------------------------------
-- Exact calibration reuses the existing two-report / one-root fixture.
------------------------------------------------------------------------

toyHeadcountQuorum :
  HeadcountQuorumTwo
    Provenance.toyPolicy
    Provenance.targetConsumer
    Provenance.firstReport
    Provenance.secondReport
toyHeadcountQuorum = Provenance.toyBothSupport

toyHeadcountDoesNotCreateIndependentQuorum :
  IndependentProvenanceQuorumTwo
    Provenance.toyPolicy
    Provenance.targetConsumer
    Provenance.firstReport
    Provenance.secondReport → ⊥
toyHeadcountDoesNotCreateIndependentQuorum =
  Provenance.toyVisibleCountDoesNotCloseIndependentAdequacy

record QuorumReceipt {Evidence Root Consumer : Set}
    (policy : Provenance.ProvenanceAdequacyPolicy Evidence Root Consumer)
    (consumer : Consumer)
    (left right : Evidence) : Set₁ where
  constructor quorum-receipt
  field
    headcount : HeadcountQuorumTwo policy consumer left right
    independentRoots : Provenance.IndependentSupport policy left right
    quorumReference : String

open QuorumReceipt public

quorumReceiptCompilesToIndependentAdequacy :
  ∀ {Evidence Root Consumer : Set}
    {policy : Provenance.ProvenanceAdequacyPolicy Evidence Root Consumer}
    {consumer : Consumer} {left right : Evidence} →
  QuorumReceipt policy consumer left right →
  IndependentProvenanceQuorumTwo policy consumer left right
quorumReceiptCompilesToIndependentAdequacy receipt =
  proj₁ (headcount receipt) ,
  (proj₂ (headcount receipt) , independentRoots receipt)

data HeadcountDeterminesIndependentProvenanceQuorum : Set where
data InstitutionalMultiplicityDeterminesRootMultiplicity : Set where

aHeadcountDoesNotDetermineIndependentQuorum :
  HeadcountDeterminesIndependentProvenanceQuorum → ⊥
aHeadcountDoesNotDetermineIndependentQuorum ()

institutionalMultiplicityDoesNotDetermineRootMultiplicity :
  InstitutionalMultiplicityDeterminesRootMultiplicity → ⊥
institutionalMultiplicityDoesNotDetermineRootMultiplicity ()

record ProvenanceQuorumBoundary : Set where
  constructor provenance-quorum-boundary
  field
    headcountAndIndependentQuorumSeparated : Bool
    independentQuorumCarriesSupportCount : Bool
    supportCountCreatesRootSeparation : Bool
    sharedRootMayDefeatQuorum : Bool
    quorumCreatesActionAuthority : Bool

canonicalProvenanceQuorumBoundary : ProvenanceQuorumBoundary
canonicalProvenanceQuorumBoundary =
  provenance-quorum-boundary true true false true false
