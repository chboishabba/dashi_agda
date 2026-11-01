module DASHI.Interop.ArtHiddenTopologyEmpiricalBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.ArtTopologyGazeContactBridge as Gaze
import DASHI.Topology.VisualPersistentHomologyCore as PH

------------------------------------------------------------------------
-- Source-bound intake for Dmitruk et al. (2026), not a universal theorem of
-- art.  The paper reports persistent-homology separation, feature/gaze-map
-- correspondence, Alexander-duality-violation differences, and a cluster near
-- 0.4 for the sampled canonical abstract artworks.  DASHI stores those claims
-- with the exact 2/5 comparison socket while keeping all promotion gates shut.

data ReportedClaimKind : Set where
  persistentTopologySeparatesStudiedSets : ReportedClaimKind
  topologyMapsToGazeFixations : ReportedClaimKind
  alexanderResidualDiffersAcrossStudiedSets : ReportedClaimKind
  eminentArtistsClusterNearTwoFifths : ReportedClaimKind
  galleryContextChangesAttention : ReportedClaimKind

record SourceBoundClaim : Set where
  constructor mkSourceBoundClaim
  field
    claimKind : ReportedClaimKind
    claimLabel : String
    reportedBySource : Bool
    reportedBySourceIsTrue : reportedBySource ≡ true
    promotedAsUniversalTheorem : Bool
    promotedAsUniversalTheoremIsFalse :
      promotedAsUniversalTheorem ≡ false
    promotedAsCausalLaw : Bool
    promotedAsCausalLawIsFalse :
      promotedAsCausalLaw ≡ false

open SourceBoundClaim public

canonicalSourceBoundClaims : List SourceBoundClaim
canonicalSourceBoundClaims =
  mkSourceBoundClaim
    persistentTopologySeparatesStudiedSets
    "persistent-homology features distinguished the studied art and perturbed-BigGAN image sets"
    true refl false refl false refl
  ∷ mkSourceBoundClaim
    topologyMapsToGazeFixations
    "topological feature maps were related to gaze-fixation heat maps in the laboratory analysis"
    true refl false refl false refl
  ∷ mkSourceBoundClaim
    alexanderResidualDiffersAcrossStudiedSets
    "normalized Alexander-duality residual distributions differed between the sampled sets"
    true refl false refl false refl
  ∷ mkSourceBoundClaim
    eminentArtistsClusterNearTwoFifths
    "sampled works by eminent abstract artists clustered around the reported dimensionless value 0.4"
    true refl false refl false refl
  ∷ mkSourceBoundClaim
    galleryContextChangesAttention
    "the gallery setting measurably changed attention duration and image engagement"
    true refl false refl false refl
  ∷ []

record ArtHiddenTopologyEmpiricalBoundary : Set where
  constructor mkArtHiddenTopologyEmpiricalBoundary
  field
    paperTitle : String
    paperDOI : String
    publicationDate : String
    sourceRepository : String

    reportedGoldenRuleTarget : PH.RationalTarget
    sourceBoundClaims : List SourceBoundClaim

    goldenRuleIsUniversalAestheticLaw : Bool
    goldenRuleIsUniversalAestheticLawIsFalse :
      goldenRuleIsUniversalAestheticLaw ≡ false

    persistentHomologySeparatesAllArtFromAllAI : Bool
    persistentHomologySeparatesAllArtFromAllAIIsFalse :
      persistentHomologySeparatesAllArtFromAllAI ≡ false

    topologyDeterminesAestheticExperience : Bool
    topologyDeterminesAestheticExperienceIsFalse :
      topologyDeterminesAestheticExperience ≡ false

    gazeContactRecoversArtistIntent : Bool
    gazeContactRecoversArtistIntentIsFalse :
      gazeContactRecoversArtistIntent ≡ false

    sourceBoundOnly : Bool
    sourceBoundOnlyIsTrue : sourceBoundOnly ≡ true

    authorityBundle : Authority.AuthorityNonPromotionBundle
    scientificAuthorityIsFalse :
      Authority.authorityFlag
        Authority.scientificAuthority authorityBundle
      ≡ false
    empiricalAuthorityIsFalse :
      Authority.authorityFlag
        Authority.empiricalAuthority authorityBundle
      ≡ false
    culturalAuthorityIsFalse :
      Authority.authorityFlag
        Authority.culturalAuthority authorityBundle
      ≡ false

open ArtHiddenTopologyEmpiricalBoundary public

artHiddenTopologyAuthority : Authority.AuthorityNonPromotionBundle
artHiddenTopologyAuthority =
  Authority.mkClosedAuthorityNonPromotionBundle
    "Dmitruk et al. art-topology source intake: no universal aesthetic, causal, cultural, or empirical promotion"

canonicalArtHiddenTopologyEmpiricalBoundary :
  ArtHiddenTopologyEmpiricalBoundary
canonicalArtHiddenTopologyEmpiricalBoundary =
  mkArtHiddenTopologyEmpiricalBoundary
    "Art's hidden topology: A window into human perception"
    "10.1371/journal.pcbi.1014156"
    "2026-05-14"
    "edd26/arttoppaper"
    PH.twoFifthsTarget
    canonicalSourceBoundClaims
    false refl
    false refl
    false refl
    false refl
    true refl
    artHiddenTopologyAuthority
    (Authority.authorityFlagIsFalse
      Authority.scientificAuthority
      artHiddenTopologyAuthority)
    (Authority.authorityFlagIsFalse
      Authority.empiricalAuthority
      artHiddenTopologyAuthority)
    (Authority.authorityFlagIsFalse
      Authority.culturalAuthority
      artHiddenTopologyAuthority)

canonicalGoldenRuleRemainsCandidateOnly :
  goldenRuleIsUniversalAestheticLaw
    canonicalArtHiddenTopologyEmpiricalBoundary
  ≡ false
canonicalGoldenRuleRemainsCandidateOnly = refl

canonicalSourceDoesNotClassifyAllAI :
  persistentHomologySeparatesAllArtFromAllAI
    canonicalArtHiddenTopologyEmpiricalBoundary
  ≡ false
canonicalSourceDoesNotClassifyAllAI = refl
