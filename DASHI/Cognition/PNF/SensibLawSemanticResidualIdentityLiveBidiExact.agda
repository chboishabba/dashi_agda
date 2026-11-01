module DASHI.Cognition.PNF.SensibLawSemanticResidualIdentityLiveBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SemanticQueryResidualFibreSSSPBridgeExact as Query
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawAntecedentIdentityRefinementBidiExact as Identity

------------------------------------------------------------------------
-- LIVE RESIDUAL-QUERY -> ANTECEDENT / IDENTITY BIDI
--
-- The existing query-fibre owner already supplies a two-world regression where
-- canonical and impersonator referents collide under a coarse identity query
-- and separate under a provenance query.  Here that exact witness is consumed
-- as a live identity-refinement specimen.
------------------------------------------------------------------------

exampleSubject : Status.SemanticSubject
exampleSubject =
  Status.semanticSubject
    "referent:query-regression"
    Status.entityReferent
    Status.participantUnresolved
    Status.legalParticipantUnresolved
    Status.identityCandidateSet
    Status.antecedentCandidateSet

coarseIdentitySnapshot : Identity.BindingCandidateSnapshot
coarseIdentitySnapshot =
  Identity.bindingCandidateSnapshot
    "query-fibre:coarse-identity"
    ("canonicalReferent" ∷ "impersonatorReferent" ∷ [])
    (Constitution.sameSentence ∷ Constitution.precedingDiscourseUnit ∷ [])
    ("coarse observation equality" ∷ [])

provenanceRefinedSnapshot : Identity.BindingCandidateSnapshot
provenanceRefinedSnapshot =
  Identity.bindingCandidateSnapshot
    "query-fibre:provenance-refined"
    ("canonicalReferent" ∷ [])
    (Constitution.sameSentence ∷ Constitution.precedingDiscourseUnit ∷ [])
    ("provenance observation separates alternatives" ∷ [])

coarseToProvenanceRefinement :
  Identity.AntecedentRefinementReceipt exampleSubject
coarseToProvenanceRefinement =
  Identity.candidateNarrowingWithoutIdentityClosure
    exampleSubject
    coarseIdentitySnapshot
    provenanceRefinedSnapshot
    "SemanticQueryResidualFibreSSSPBridgeExact.provenanceQuery"
    "query-indexed residual refinement"

identityStayedCandidateDuringNarrowing :
  Identity.identityBefore coarseToProvenanceRefinement
  ≡ Identity.identityAfter coarseToProvenanceRefinement
identityStayedCandidateDuringNarrowing =
  Identity.identityUnchanged coarseToProvenanceRefinement

record ProvenanceDiscriminatorReceipt : Set where
  constructor provenanceDiscriminatorReceipt
  field
    coarseCollision :
      Query.exampleObserve Query.coarseIdentityQuery Query.canonicalReferent
      ≡ Query.exampleObserve Query.coarseIdentityQuery Query.impersonatorReferent
    provenanceSeparation :
      Query.exampleObserve Query.provenanceQuery Query.canonicalReferent
      ≡ Query.exampleObserve Query.provenanceQuery Query.impersonatorReferent → ⊥
    refinedAntecedent : Identity.AntecedentRefinementReceipt exampleSubject
    candidateHistoryReference : String

open ProvenanceDiscriminatorReceipt public

canonicalProvenanceDiscriminator : ProvenanceDiscriminatorReceipt
canonicalProvenanceDiscriminator =
  provenanceDiscriminatorReceipt
    Query.coarseWorldsObservationEqual
    Query.provenanceWorldsSeparate
    coarseToProvenanceRefinement
    "coarse canonical/impersonator pair retained as prior residual fibre"

canonicalIdentityClosure : Identity.IdentityClosureReceipt exampleSubject
canonicalIdentityClosure =
  Identity.identityClosureReceipt
    provenanceRefinedSnapshot
    Status.identityResolvedSame
    ("provenanceQuery=pos for canonicalReferent" ∷
     "provenanceQuery=neg for impersonatorReferent" ∷ [])
    "SemanticQueryResidualFibreSSSPBridgeExact"
    "identity closure requires provenance discriminator"
    "governed identity-resolution authority"

canonicalIdentityInformsFutureAntecedent :
  Identity.IdentityInformedAntecedentReceipt exampleSubject
canonicalIdentityInformsFutureAntecedent =
  Identity.identityInformedAntecedentReceipt
    canonicalIdentityClosure
    coarseToProvenanceRefinement
    provenanceRefinedSnapshot
    Status.antecedentResolved
    "query-fibre:coarse-identity"

------------------------------------------------------------------------
-- No backwards rewrite of the coarse observation.
------------------------------------------------------------------------

data LaterProvenanceMakesCoarseQueryUnique : Set where
data SingletonCandidateSetWasAlwaysIdentityProof : Set where

laterProvenanceDoesNotRewriteCoarseQuery :
  LaterProvenanceMakesCoarseQueryUnique → ⊥
laterProvenanceDoesNotRewriteCoarseQuery ()

singletonWasNotRetroactiveIdentityProof :
  SingletonCandidateSetWasAlwaysIdentityProof → ⊥
singletonWasNotRetroactiveIdentityProof ()
