module DASHI.Cognition.StateInstitutionEpistemicNonPrivilegeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- State / institutional source non-privilege.
--
-- Government, intelligence, police, regulator, court, vendor, academic and
-- media sources may all carry high-value evidence.  None is a God's-eye view.
-- A source may prove what the institution says, did, searched, seized or found;
-- it does not automatically prove completeness of reality or neutrality of the
-- institution's own scope, incentives or omissions.
------------------------------------------------------------------------

record InstitutionalEpistemicBoundary : Set where
  constructor institutional-epistemic-boundary
  field
    stateSourceCreatesGroundTruth : Bool
    institutionalSelfCertificationClosesQuestion : Bool
    highAuthorityEliminatesConflictOfInterest : Bool
    absenceFromHoldingsProvesNonOccurrence : Bool
    demonstratedCapabilityProvesSpecificUse : Bool
    adverseInstitutionalHistoryMakesEveryCurrentClaimFalse : Bool
    claimLocalCorroborationRequired : Bool
    adversarialOrIndependentCoverageRaisesClosureStrength : Bool
    disclosedScopeAndMethodMatter : Bool
    retainedAlternativesMatter : Bool
open InstitutionalEpistemicBoundary public

canonicalInstitutionalEpistemicBoundary : InstitutionalEpistemicBoundary
canonicalInstitutionalEpistemicBoundary = institutional-epistemic-boundary
  false false false false false false true true true true

data StateSourceImpliesGroundTruth : Set where
data SelfInvestigationImpliesExhaustiveReality : Set where
data InstitutionalDistrustImpliesAutomaticFalsehood : Set where

stateSourceDoesNotCreateGroundTruth : StateSourceImpliesGroundTruth → ⊥
stateSourceDoesNotCreateGroundTruth ()

selfInvestigationDoesNotCreateRealityCompleteness :
  SelfInvestigationImpliesExhaustiveReality → ⊥
selfInvestigationDoesNotCreateRealityCompleteness ()

distrustDoesNotCreateAutomaticFalsehood :
  InstitutionalDistrustImpliesAutomaticFalsehood → ⊥
distrustDoesNotCreateAutomaticFalsehood ()
