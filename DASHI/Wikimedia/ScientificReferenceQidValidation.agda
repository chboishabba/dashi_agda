module DASHI.Wikimedia.ScientificReferenceQidValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas
import DASHI.Wikimedia.ScientificCitationQidBindingsExact as Citation
import DASHI.Physics.YangMills.SourceEntityQidBindingsExact as YM
import DASHI.Physics.Closure.NavierStokesSourceEntityQidBindingsExact as NS
import DASHI.Analysis.RiemannSourceEntityQidBindingsExact as RH

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

-- Import-level witnesses that each domain reaches the canonical citation layer.
ymCKNSeparationWitness : Citation.CitationDomain
ymCKNSeparationWitness = Citation.domain Citation.faddeevPopov1967

nsCKNDomainWitness : Citation.CitationDomain
nsCKNDomainWitness = Citation.domain Citation.ckn

rhPolymathDomainWitness : Citation.CitationDomain
rhPolymathDomainWitness = Citation.domain Citation.polymath2019
