module DASHI.Governance.SexedHistoricalStratifiedCollectiveGluingExact where

------------------------------------------------------------------------
-- STRATIFIED COLLECTIVE GLUING OF BRANCHING HISTORICAL FIBRES
--
-- This owner lifts the bracketed descendant-fibre lane from one history into
-- several local histories.  A global continuation exists only with an explicit
-- compatibility witness.  Local branch availability alone is insufficient.
--
-- Base369 centre/face/edge/corner strata are reused only as exact geometric
-- strata / finite indexing vocabulary.  They do not acquire social meaning by
-- themselves.  This owner supplies the separate historical interpretation.
--
-- PR #666's stronger stratified-fibre lane is design inspiration only and is
-- intentionally NOT imported while that PR remains open.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.LocalGlobalCouncilGluing as CouncilGluing
import DASHI.Governance.SexedHistoricalCollectiveThresholdNetworkExact as Collective
import DASHI.Governance.SexedHistoricalBracketedMultiverseTSFVBridgeExact as Branching
import DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact as Ecology

------------------------------------------------------------------------
-- 1. Three local actors / sites of the finite comparison.
------------------------------------------------------------------------

data LocalSite : Set where
  feminineSite masculineSite institutionalSite : LocalSite

data LocalContinuation : LocalSite → Set where
  feminineReciprocal femininePlural : LocalContinuation feminineSite
  masculineReciprocal masculineCounterformation : LocalContinuation masculineSite
  institutionAccommodates institutionResists : LocalContinuation institutionalSite

------------------------------------------------------------------------
-- 2. Stratum-indexed local availability.
--
-- The stratum constrains admissibility, but does not identify the branch.
------------------------------------------------------------------------

data LocalAtStratum :
  (site : LocalSite) → Strata.VoxelStratum → LocalContinuation site → Set where
  feminineReciprocalAtFace :
    LocalAtStratum feminineSite Strata.faceCentreStratum feminineReciprocal
  femininePluralAtFace :
    LocalAtStratum feminineSite Strata.faceCentreStratum femininePlural

  masculineReciprocalAtEdge :
    LocalAtStratum masculineSite Strata.edgeCentreStratum masculineReciprocal
  masculineCounterAtEdge :
    LocalAtStratum masculineSite Strata.edgeCentreStratum masculineCounterformation

  institutionAccommodatesAtCentre :
    LocalAtStratum institutionalSite Strata.centreStratum institutionAccommodates
  institutionResistsAtCentre :
    LocalAtStratum institutionalSite Strata.centreStratum institutionResists

------------------------------------------------------------------------
-- 3. Local branch family and locally-live receipt.
------------------------------------------------------------------------

record LocalBranchFamily : Set where
  constructor local-branch-family
  field
    feminineBranch : LocalContinuation feminineSite
    masculineBranch : LocalContinuation masculineSite
    institutionalBranch : LocalContinuation institutionalSite
open LocalBranchFamily public

record AllLocallyLive (family : LocalBranchFamily) : Set where
  constructor all-locally-live
  field
    feminineLive :
      LocalAtStratum feminineSite Strata.faceCentreStratum (feminineBranch family)
    masculineLive :
      LocalAtStratum masculineSite Strata.edgeCentreStratum (masculineBranch family)
    institutionLive :
      LocalAtStratum institutionalSite Strata.centreStratum (institutionalBranch family)
open AllLocallyLive public

reciprocalFamily : LocalBranchFamily
reciprocalFamily =
  local-branch-family feminineReciprocal masculineReciprocal institutionAccommodates

blockedCollectiveFamily : LocalBranchFamily
blockedCollectiveFamily =
  local-branch-family feminineReciprocal masculineReciprocal institutionResists

counterformationFamily : LocalBranchFamily
counterformationFamily =
  local-branch-family femininePlural masculineCounterformation institutionResists

reciprocalFamilyLocallyLive : AllLocallyLive reciprocalFamily
reciprocalFamilyLocallyLive =
  all-locally-live
    feminineReciprocalAtFace
    masculineReciprocalAtEdge
    institutionAccommodatesAtCentre

blockedCollectiveFamilyLocallyLive : AllLocallyLive blockedCollectiveFamily
blockedCollectiveFamilyLocallyLive =
  all-locally-live
    feminineReciprocalAtFace
    masculineReciprocalAtEdge
    institutionResistsAtCentre

counterformationFamilyLocallyLive : AllLocallyLive counterformationFamily
counterformationFamilyLocallyLive =
  all-locally-live
    femininePluralAtFace
    masculineCounterAtEdge
    institutionResistsAtCentre

------------------------------------------------------------------------
-- 4. Global compatibility is stricter than pointwise local availability.
------------------------------------------------------------------------

data CompatibleFamily : LocalBranchFamily → Set where
  reciprocalCompatible : CompatibleFamily reciprocalFamily
  counterformationCompatible : CompatibleFamily counterformationFamily

blockedCollectiveFamilyCannotGlue :
  CompatibleFamily blockedCollectiveFamily → ⊥
blockedCollectiveFamilyCannotGlue ()

------------------------------------------------------------------------
-- 5. Global continuation / restriction receipt.
------------------------------------------------------------------------

record GlobalContinuation : Set where
  constructor global-continuation
  field
    localFamily : LocalBranchFamily
    compatibility : CompatibleFamily localFamily
open GlobalContinuation public

glue : (family : LocalBranchFamily) → CompatibleFamily family → GlobalContinuation
glue family witness = global-continuation family witness

canonicalGlobalContinuation : GlobalContinuation
canonicalGlobalContinuation = glue reciprocalFamily reciprocalCompatible

restrictFeminine : GlobalContinuation → LocalContinuation feminineSite
restrictFeminine global = feminineBranch (localFamily global)

restrictMasculine : GlobalContinuation → LocalContinuation masculineSite
restrictMasculine global = masculineBranch (localFamily global)

restrictInstitution : GlobalContinuation → LocalContinuation institutionalSite
restrictInstitution global = institutionalBranch (localFamily global)

canonicalGlobalRestrictsToFeminine :
  restrictFeminine canonicalGlobalContinuation ≡ feminineReciprocal
canonicalGlobalRestrictsToFeminine = refl

canonicalGlobalRestrictsToMasculine :
  restrictMasculine canonicalGlobalContinuation ≡ masculineReciprocal
canonicalGlobalRestrictsToMasculine = refl

canonicalGlobalRestrictsToInstitution :
  restrictInstitution canonicalGlobalContinuation ≡ institutionAccommodates
canonicalGlobalRestrictsToInstitution = refl

------------------------------------------------------------------------
-- 6. Stratum is not enough to recover the local branch.
------------------------------------------------------------------------

data FeminineFineAtFace : Set where
  faceReciprocal facePlural : FeminineFineAtFace

feminineStratumSurface : FeminineFineAtFace → Strata.VoxelStratum
feminineStratumSurface _ = Strata.faceCentreStratum

feminineContinuationSurface :
  FeminineFineAtFace → LocalContinuation feminineSite
feminineContinuationSurface faceReciprocal = feminineReciprocal
feminineContinuationSurface facePlural = femininePlural

stratumCannotRecoverLocalContinuation :
  INF.FactorsThrough feminineStratumSurface feminineContinuationSurface → ⊥
stratumCannotRecoverLocalContinuation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness faceReciprocal facePlural refl (λ ()))

------------------------------------------------------------------------
-- 7. Same global public surface cannot recover local compatibility integrity.
------------------------------------------------------------------------

data GlobalFineState : Set where
  genuinelyCompatiblePublicEquality
  suppressedIncompatibilityPublicEquality
  : GlobalFineState

data GlobalPublicSurface : Set where
  formalEqualityAndReciprocalNorm : GlobalPublicSurface

data GlobalIntegrity : Set where
  compatibleLocalEndorsement forcedHomogenisation : GlobalIntegrity

globalPublicSurface : GlobalFineState → GlobalPublicSurface
globalPublicSurface _ = formalEqualityAndReciprocalNorm

globalIntegrity : GlobalFineState → GlobalIntegrity
globalIntegrity genuinelyCompatiblePublicEquality = compatibleLocalEndorsement
globalIntegrity suppressedIncompatibilityPublicEquality = forcedHomogenisation

globalSurfaceCannotRecoverLocalIntegrity :
  INF.FactorsThrough globalPublicSurface globalIntegrity → ⊥
globalSurfaceCannotRecoverLocalIntegrity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      genuinelyCompatiblePublicEquality
      suppressedIncompatibilityPublicEquality
      refl
      (λ ()))

------------------------------------------------------------------------
-- 8. Minimal compatibility extension = a proof-bearing gluing threshold.
--
-- The local reciprocal branches are held fixed.  Replacing institutional
-- resistance with accommodation changes the family from locally-live but
-- unglueable to globally compatible.
------------------------------------------------------------------------

record MinimalCompatibilityExtension : Set where
  constructor minimal-compatibility-extension
  field
    before : LocalBranchFamily
    after : LocalBranchFamily
    beforeLocallyLive : AllLocallyLive before
    afterLocallyLive : AllLocallyLive after
    beforeNotGlueable : CompatibleFamily before → ⊥
    afterGlueable : CompatibleFamily after

canonicalMinimalCompatibilityExtension : MinimalCompatibilityExtension
canonicalMinimalCompatibilityExtension =
  minimal-compatibility-extension
    blockedCollectiveFamily
    reciprocalFamily
    blockedCollectiveFamilyLocallyLive
    reciprocalFamilyLocallyLive
    blockedCollectiveFamilyCannotGlue
    reciprocalCompatible

------------------------------------------------------------------------
-- 9. Cross-owner continuity: collective threshold and local/global gluing keep
-- their existing boundaries.
------------------------------------------------------------------------

collectiveThresholdStillDoesNotGuaranteeVictory :
  Collective.ThresholdCrossingGuaranteesVictory → ⊥
collectiveThresholdStillDoesNotGuaranteeVictory =
  Collective.thresholdCrossingDoesNotGuaranteeVictory

councilGluingStillRequiresCompatibility :
  CouncilGluing.CouncilGluingBoundary
councilGluingStillRequiresCompatibility =
  CouncilGluing.canonicalCouncilGluingBoundary

historyEcologyBoundaryStillIndependent :
  Ecology.HistoryEcologyOptionConeBoundary
historyEcologyBoundaryStillIndependent =
  Ecology.canonicalHistoryEcologyOptionConeBoundary

branchingPresentStillDoesNotRecoverFuture :
  INF.FactorsThrough Branching.coarsePresent Branching.branchFutureCone → ⊥
branchingPresentStillDoesNotRecoverFuture =
  Branching.samePresentCannotRecoverDescendantFuture

------------------------------------------------------------------------
-- 10. No-promotion boundaries.
------------------------------------------------------------------------

data EveryLocallyLiveFamilyGloballyGlueable : Set where

data GlobalSurfaceImpliesCompatibleLocals : Set where

data SameStratumImpliesSameHistoricalBranch : Set where

data GluingRequiresUniformSubjectFormation : Set where

data Base369StratumIsHistoricalMeaning : Set where

data MinimalCompatibilityExtensionIsUniversalCriticalMass : Set where

data InstitutionalAccommodationGuaranteesLiberatoryOutcome : Set where

localAvailabilityDoesNotGuaranteeGlobalGlueability :
  EveryLocallyLiveFamilyGloballyGlueable → ⊥
localAvailabilityDoesNotGuaranteeGlobalGlueability ()

globalSurfaceDoesNotGuaranteeCompatibleLocals :
  GlobalSurfaceImpliesCompatibleLocals → ⊥
globalSurfaceDoesNotGuaranteeCompatibleLocals ()

sameStratumDoesNotIdentifyHistoricalBranch :
  SameStratumImpliesSameHistoricalBranch → ⊥
sameStratumDoesNotIdentifyHistoricalBranch ()

gluingDoesNotRequireUniformSubjectFormation :
  GluingRequiresUniformSubjectFormation → ⊥
gluingDoesNotRequireUniformSubjectFormation ()

base369StratumDoesNotSupplyHistoricalSemantics :
  Base369StratumIsHistoricalMeaning → ⊥
base369StratumDoesNotSupplyHistoricalSemantics ()

minimalCompatibilityExtensionIsNotUniversalCriticalMass :
  MinimalCompatibilityExtensionIsUniversalCriticalMass → ⊥
minimalCompatibilityExtensionIsNotUniversalCriticalMass ()

institutionalAccommodationDoesNotGuaranteeLiberatoryOutcome :
  InstitutionalAccommodationGuaranteesLiberatoryOutcome → ⊥
institutionalAccommodationDoesNotGuaranteeLiberatoryOutcome ()

record StratifiedCollectiveGluingBoundary : Set where
  constructor stratified-collective-gluing-boundary
  field
    localBranchesRemainExplicit : Bool
    stratumConditionsLocalAvailability : Bool
    sameStratumDeterminesLocalBranch : Bool
    everyLocallyLiveFamilyIsGloballyGlueable : Bool
    compatibilityWitnessRequiredForGlobalContinuation : Bool
    globalContinuationRestrictsToLocalBranches : Bool
    publicGlobalSurfaceRecoversCompatibilityIntegrity : Bool
    minimalCompatibilityExtensionCanBeWitnessed : Bool
    minimalExtensionIsUniversalCriticalMass : Bool
    Base369StratumCarriesHistoricalMeaningByItself : Bool

canonicalStratifiedCollectiveGluingBoundary : StratifiedCollectiveGluingBoundary
canonicalStratifiedCollectiveGluingBoundary =
  stratified-collective-gluing-boundary
    true true false false true true false true false false
