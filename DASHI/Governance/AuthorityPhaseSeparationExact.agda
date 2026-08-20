module DASHI.Governance.AuthorityPhaseSeparationExact where

------------------------------------------------------------------------
-- PHASE-SEPARATED AUTHORITY COMPOSITION
--
-- Response, adjudication, sentencing and repair are distinct authority phases.
-- A single coarse "authority" surface cannot determine the phase-specific role
-- in the finite witness below.  This does not prevent compatible authorities
-- from composing: the existing council BundleSheaf glues compatible local
-- sections and restricts back exactly, while explicitly refusing to create
-- political authority from the formal analogy.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Governance.LocalGlobalCouncilGluing as Council

------------------------------------------------------------------------
-- Phase-specific authority is not a single intrinsic actor property.
------------------------------------------------------------------------

data InterventionPhase : Set where
  responsePhase adjudicationPhase sentencingPhase repairPhase :
    InterventionPhase

data PhaseAuthorityRole : Set where
  responseAuthorityRole adjudicationAuthorityRole : PhaseAuthorityRole
  sentencingAuthorityRole repairAuthorityRole : PhaseAuthorityRole

data CoarseAuthoritySurface : Set where
  authorityPresentSurface : CoarseAuthoritySurface

coarseAuthorityProjection : InterventionPhase → CoarseAuthoritySurface
coarseAuthorityProjection phase = authorityPresentSurface

phaseAuthorityRole : InterventionPhase → PhaseAuthorityRole
phaseAuthorityRole responsePhase = responseAuthorityRole
phaseAuthorityRole adjudicationPhase = adjudicationAuthorityRole
phaseAuthorityRole sentencingPhase = sentencingAuthorityRole
phaseAuthorityRole repairPhase = repairAuthorityRole

responseAndRepairAuthorityDiffer :
  phaseAuthorityRole responsePhase ≡ phaseAuthorityRole repairPhase → ⊥
responseAndRepairAuthorityDiffer ()

phaseAuthorityNonFactorability :
  NonFactor.NonFactorabilityWitness
    coarseAuthorityProjection
    phaseAuthorityRole
phaseAuthorityNonFactorability =
  NonFactor.nonFactorabilityWitness
    responsePhase
    repairPhase
    refl
    responseAndRepairAuthorityDiffer

oneAuthoritySurfaceCannotDetermineEveryPhase :
  NonFactor.FactorsThrough
    coarseAuthorityProjection
    phaseAuthorityRole →
  ⊥
oneAuthoritySurfaceCannotDetermineEveryPhase =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    phaseAuthorityNonFactorability

responseAuthorityDoesNotDetermineAdjudicationAuthority :
  phaseAuthorityRole responsePhase
  ≡ phaseAuthorityRole adjudicationPhase →
  ⊥
responseAuthorityDoesNotDetermineAdjudicationAuthority ()

adjudicationAuthorityDoesNotDetermineRepairAuthority :
  phaseAuthorityRole adjudicationPhase
  ≡ phaseAuthorityRole repairPhase →
  ⊥
adjudicationAuthorityDoesNotDetermineRepairAuthority ()

------------------------------------------------------------------------
-- Composition without sovereignty collapse.
------------------------------------------------------------------------

record PhaseSeparatedCompatibleAuthorityComposition : Set₁ where
  constructor phaseSeparatedCompatibleAuthorityComposition
  field
    phaseSeparation :
      NonFactor.NonFactorabilityWitness
        coarseAuthorityProjection
        phaseAuthorityRole
    localCompatibility :
      Council.CompatibleCouncilFamily Council.canonicalLocalCouncilFamily
    globalSection : Council.GlobalCouncilSection
    globalSectionIsCanonical :
      globalSection ≡ Council.canonicalGlobalCouncilSection
    neighbourhoodRestrictionIsExact :
      Stage.BundleSheaf.restrict
        Council.rceppCouncilBundleSheaf
        globalSection
        Council.neighbourhoodPoint
      ≡ Council.canonicalLocalCouncilFamily Council.neighbourhoodPoint
    displacedConstituencyRestrictionIsExact :
      Stage.BundleSheaf.restrict
        Council.rceppCouncilBundleSheaf
        globalSection
        Council.idpCampPoint
      ≡ Council.canonicalLocalCouncilFamily Council.idpCampPoint
    compositionDoesNotCreatePoliticalAuthority :
      Council.sheafAnalogyCreatesPoliticalAuthority
        Council.canonicalCouncilGluingBoundary
      ≡ false

open PhaseSeparatedCompatibleAuthorityComposition public

canonicalPhaseSeparatedCompatibleAuthorityComposition :
  PhaseSeparatedCompatibleAuthorityComposition
canonicalPhaseSeparatedCompatibleAuthorityComposition =
  phaseSeparatedCompatibleAuthorityComposition
    phaseAuthorityNonFactorability
    Council.canonicalCouncilCompatibility
    Council.canonicalGlobalCouncilSection
    refl
    Council.canonicalGlobalRestrictsToNeighbourhood
    Council.canonicalGlobalRestrictsToIDPCamp
    refl

CompatibleSituatedAuthoritiesCanComposeWithoutSovereigntyCollapse :
  PhaseSeparatedCompatibleAuthorityComposition
CompatibleSituatedAuthoritiesCanComposeWithoutSovereigntyCollapse =
  canonicalPhaseSeparatedCompatibleAuthorityComposition

record AuthorityPhaseSeparationBoundary : Set where
  constructor authorityPhaseSeparationBoundary
  field
    responseAuthorityEqualsAdjudicationAuthorityByDefault : Bool
    adjudicationAuthorityEqualsSentencingAuthorityByDefault : Bool
    sentencingAuthorityEqualsRepairAuthorityByDefault : Bool
    oneCoarseAuthoritySurfaceDeterminesAllPhases : Bool
    compatiblePhasesMayCompose : Bool
    formalCompositionCreatesSovereignty : Bool

canonicalAuthorityPhaseSeparationBoundary : AuthorityPhaseSeparationBoundary
canonicalAuthorityPhaseSeparationBoundary =
  authorityPhaseSeparationBoundary false false false false true false
