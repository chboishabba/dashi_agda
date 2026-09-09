module DASHI.Interop.AristotleWikibaseZelphBraidedPromotionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BraidedPromotionTransportBidiExact as Braided
import DASHI.Interop.SensibLawWikibaseZelphItemSurfaceExact as Join
import DASHI.Interop.SensibLawNatZelphPeerCohortExact as Peer
import DASHI.Interop.SensibLawNatPeerPressureWeldExact as Weld
import DASHI.Interop.SensibLawNatZelphPipelineExact as Pipeline

-- Concrete provenance strands for the actual Nat/Wikimedia route.
data NatEvidenceStrand : Set where
  nativeWikibaseStrand
  zelphGraphStrand
  governedReviewStrand
  migrationPolicyStrand : NatEvidenceStrand

record NatBraidedEvidenceObligations : Set where
  constructor nat-braided-evidence-obligations
  field
    nativeStatementReference : String
    graphContextReference : String
    peerReviewReference : String
    policyAuthorityReference : String
    nativeOwnsGuidSnakRankQualifierReference : Bool
    nativeOwnsGuidSnakRankQualifierReferenceIsTrue :
      nativeOwnsGuidSnakRankQualifierReference ≡ true
    graphOwnsBoundedRelationContext : Bool
    graphOwnsBoundedRelationContextIsTrue : graphOwnsBoundedRelationContext ≡ true
    reviewOwnsTrustedCohortAdmission : Bool
    reviewOwnsTrustedCohortAdmissionIsTrue : reviewOwnsTrustedCohortAdmission ≡ true
    policyOwnsMigrationAuthority : Bool
    policyOwnsMigrationAuthorityIsTrue : policyOwnsMigrationAuthority ≡ true
open NatBraidedEvidenceObligations public

-- The two evidence planes and the downstream review/policy strands remain
-- conjunctive but non-fungible.
data NativeStatementImpliesGraphCompleteness : Set where
data GraphSoundnessImpliesNativeStatementSemantics : Set where
data ExactPeerImpliesPolicyAuthority : Set where
data LogicalClosureBackfillsProvenanceStrands : Set where

nativeStatementDoesNotCreateGraphCompleteness :
  NativeStatementImpliesGraphCompleteness → ⊥
nativeStatementDoesNotCreateGraphCompleteness ()

graphSoundnessDoesNotCreateNativeStatementSemantics :
  GraphSoundnessImpliesNativeStatementSemantics → ⊥
graphSoundnessDoesNotCreateNativeStatementSemantics ()

exactPeerDoesNotCreatePolicyAuthority :
  ExactPeerImpliesPolicyAuthority → ⊥
exactPeerDoesNotCreatePolicyAuthority ()

logicalClosureDoesNotBackfillStrands :
  LogicalClosureBackfillsProvenanceStrands → ⊥
logicalClosureDoesNotBackfillStrands ()

record AristotleWikibaseZelphBraidedBoundary : Set where
  constructor aristotle-wikibase-zelph-braided-boundary
  field
    nativeAndGraphEvidenceRemainSeparateStrands : Bool
    governedReviewIsSeparateStrand : Bool
    migrationPolicyIsSeparateStrand : Bool
    braidCoordinationMakesStrandsFungible : Bool
    peerExactCreatesPolicyAuthority : Bool
    logicalClosureReconstructsMissingProvenance : Bool

canonicalAristotleWikibaseZelphBraidedBoundary :
  AristotleWikibaseZelphBraidedBoundary
canonicalAristotleWikibaseZelphBraidedBoundary =
  aristotle-wikibase-zelph-braided-boundary true true true false false false

wikibaseZelphBraidedStatement : String
wikibaseZelphBraidedStatement =
  "The Nat/Wikimedia pipeline is a concrete braided promotion transport: native Wikibase owns GUID/snak/rank/qualifier/reference semantics, Zelph owns bounded graph relation context, governed review owns trusted-cohort admission, and migration policy owns promotion authority. Their receipts may coordinate but are not fungible; graph soundness does not reconstruct native statement semantics, an exact peer residual does not create policy authority, and logical closure does not backfill missing provenance strands."
