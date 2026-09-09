module DASHI.Wikimedia.ScientificReferenceQidValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas
import DASHI.Wikimedia.ScientificCitationQidBindingsExact as Citation
import DASHI.Wikimedia.ScientificReferenceResidualAcquisitionExact as Residual
import DASHI.Physics.YangMills.SourceEntityQidBindingsExact as YM
import DASHI.Physics.Closure.NavierStokesSourceEntityQidBindingsExact as NS
import DASHI.Physics.Closure.NavierStokesCitationIdentityAuditExact as NSAudit
import DASHI.Analysis.RiemannSourceEntityQidBindingsExact as RH
import DASHI.Analysis.RiemannExtendedSourceEntityQidBindingsExact as RHExtended

atlasTreatsQidsAsMetadata :
  Atlas.ScientificReferenceEntityAtlasBoundary.qidIsExternalIdentityMetadata
    Atlas.canonicalScientificReferenceEntityAtlasBoundary ≡ true
atlasTreatsQidsAsMetadata = refl

atlasKeepsPublicationIdentityPrimary :
  Atlas.ScientificReferenceEntityAtlasBoundary.publicationIdentifierRemainsPrimary
    Atlas.canonicalScientificReferenceEntityAtlasBoundary ≡ true
atlasKeepsPublicationIdentityPrimary = refl

atlasKeepsUnresolvedMappingsOpen :
  Atlas.ScientificReferenceEntityAtlasBoundary.unresolvedMappingsRemainExplicit
    Atlas.canonicalScientificReferenceEntityAtlasBoundary ≡ true
atlasKeepsUnresolvedMappingsOpen = refl

referenceDemandIsExactResidualIndexed :
  Residual.ScientificReferenceResidualBoundary.acquisitionIsIndexedByExactResidual
    Residual.canonicalScientificReferenceResidualBoundary ≡ true
referenceDemandIsExactResidualIndexed = refl

referenceRetrievalDoesNotPayResidual :
  Residual.ScientificReferenceResidualBoundary.retrievalEqualsPayment
    Residual.canonicalScientificReferenceResidualBoundary ≡ false
referenceRetrievalDoesNotPayResidual = refl

referenceCandidateQidDoesNotProveSamePerson :
  Residual.ScientificReferenceResidualBoundary.candidateQidEqualsSamePersonProof
    Residual.canonicalScientificReferenceResidualBoundary ≡ false
referenceCandidateQidDoesNotProveSamePerson = refl

ymQidDoesNotCloseClay :
  YM.YMReferenceEntityBoundary.qidClosesClayObligation
    YM.canonicalYMReferenceEntityBoundary ≡ false
ymQidDoesNotCloseClay = refl

nsQidDoesNotClosePackageA :
  NS.NSReferenceEntityBoundary.qidClosesPackageA
    NS.canonicalNSReferenceEntityBoundary ≡ false
nsQidDoesNotClosePackageA = refl

rhQidDoesNotCreateProof :
  RH.RiemannReferenceEntityBoundary.qidCreatesRiemannHypothesisProof
    RH.canonicalRiemannReferenceEntityBoundary ≡ false
rhQidDoesNotCreateProof = refl

cknQidCannotRepairWrongDoi :
  NSAudit.NavierStokesCitationIdentityAuditBoundary.qidCanReplaceDoiCorrection
    NSAudit.canonicalNavierStokesCitationIdentityAuditBoundary ≡ false
cknQidCannotRepairWrongDoi = refl

-- Import-level witnesses that each domain reaches the canonical citation layer.
ymSourceDomainWitness : Citation.CitationDomain
ymSourceDomainWitness = Citation.domain Citation.faddeevPopov1967

nsSourceDomainWitness : Citation.CitationDomain
nsSourceDomainWitness = Citation.domain Citation.ckn

rhPolymathDomainWitness : Citation.CitationDomain
rhPolymathDomainWitness = Citation.domain Citation.polymath2019

rhExtendedBindingWitness : RHExtended.ExtendedRiemannSourceBinding
rhExtendedBindingWitness = RHExtended.bombieriClayRH

robertKohnDemandWitness : Residual.ScientificReferenceAcquisitionDemand Residual.robertKohnIdentityResidual
robertKohnDemandWitness = Residual.robertKohnIdentityDemand
