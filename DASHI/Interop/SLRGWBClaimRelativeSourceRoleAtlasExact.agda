module DASHI.Interop.SLRGWBClaimRelativeSourceRoleAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB
import DASHI.Interop.SLRGWBWikimediaIdentityResidualContractionExact as Identity

------------------------------------------------------------------------
-- GWB CLAIM-RELATIVE SOURCE ROLE ATLAS
--
-- Runtime/source inventory:
--   gwb-source-inventory.json
-- Fixture:
--   fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl
--
-- This atlas types source roles only.  It does not read source role as truth
-- authority.  Primaryness is always relative to a claim class.
------------------------------------------------------------------------

data GWBSourceRole : Set where
  officialExecutiveArchiveBiography : GWBSourceRole
  secondaryEncyclopediaBiography : GWBSourceRole
  institutionalHistoricalBiography : GWBSourceRole
  presidentialLibraryInstitutionalBiography : GWBSourceRole
  presidentialCenterInstitutionalBiography : GWBSourceRole
  scholarlyInstitutionalBiography : GWBSourceRole
  secondaryInvestigativeBook : GWBSourceRole
  institutionalScholarlyHistory : GWBSourceRole
  firstPersonPresidentialMemoir : GWBSourceRole

record ClaimRelativeSourceRole : Set where
  constructor claimRelativeSourceRole
  field
    documentReference : String
    role : GWBSourceRole
    primaryForReference : String
    notAuthorityForReference : String
    sourceObjectIdentityPaid : Bool
    topicAnchorPaid : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ClaimRelativeSourceRole public

gwbClaimRelativeSourceRoles : List ClaimRelativeSourceRole
gwbClaimRelativeSourceRoles =
  claimRelativeSourceRole "GWB document 1" officialExecutiveArchiveBiography
    "archived official presidential self/institutional presentation"
    "independent historical truth or all underlying event claims"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 2" secondaryEncyclopediaBiography
    "no automatic primary claim class"
    "first-person recollection, official institutional position, automatic event truth"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 3" institutionalHistoricalBiography
    "publisher institution's presented historical account"
    "independent event truth by institutional status alone"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 4" presidentialLibraryInstitutionalBiography
    "presidential library's institutional presentation"
    "independent historical truth or all underlying event claims"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 5" presidentialCenterInstitutionalBiography
    "Bush Center's institutional/self-presentation"
    "independent historical truth or all underlying event claims"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 6" scholarlyInstitutionalBiography
    "institution's authored analytical presentation"
    "first-person recollection or automatic event truth"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 7" secondaryInvestigativeBook
    "authors' own published allegations/analysis"
    "underlying allegation truth without supporting evidence"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 8" secondaryInvestigativeBook
    "author's own published allegations/analysis"
    "underlying allegation truth without supporting evidence"
    true false true false
  ∷ claimRelativeSourceRole "GWB document 9" institutionalScholarlyHistory
    "editors/authors' published historical synthesis"
    "George H. W. Bush first-person recollection unless separately attributed; automatic event truth"
    false true true false
  ∷ claimRelativeSourceRole "GWB document 10" firstPersonPresidentialMemoir
    "George W. Bush's stated recollections, positions and self-description"
    "independent truth of every event, other actors' mental states, uncorroborated causal truth"
    true false true false
  ∷ []

record SourceRoleBoundary : Set where
  constructor sourceRoleBoundary
  field
    officialSourceCreatesIndependentTruth : Bool
    memoirPrimaryForEveryUnderlyingEvent : Bool
    investigativeBookAllegationCreatesTruth : Bool
    institutionalStatusCreatesEventTruth : Bool
    primarynessClaimRelative : Bool
    sourceRoleSeparateFromSourceIdentity : Bool
    topicAnchorSeparateFromSourceRole : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SourceRoleBoundary public

canonicalSourceRoleBoundary : SourceRoleBoundary
canonicalSourceRoleBoundary = sourceRoleBoundary
  false false false false true true true true false

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

gwbCarrierAnchor : GWB.GWBCandidateWorldBoundary
gwbCarrierAnchor = GWB.canonicalGWBCandidateWorldBoundary

identityContractionAnchor : Identity.GWBIdentityContractionBoundary
identityContractionAnchor = Identity.canonicalGWBIdentityContractionBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OfficialSourceIsIndependentTruth : Set where
data MemoirIsPrimaryForEveryEvent : Set where
data InvestigativeAllegationIsUnderlyingTruth : Set where
data SourceRoleIsSourceObjectIdentity : Set where
data TopicAnchorDeterminesSourceRole : Set where

officialSourceDoesNotCreateIndependentTruth : OfficialSourceIsIndependentTruth → ⊥
officialSourceDoesNotCreateIndependentTruth ()

memoirIsNotPrimaryForEveryEvent : MemoirIsPrimaryForEveryEvent → ⊥
memoirIsNotPrimaryForEveryEvent ()

investigativeAllegationDoesNotCreateTruth : InvestigativeAllegationIsUnderlyingTruth → ⊥
investigativeAllegationDoesNotCreateTruth ()

sourceRoleDoesNotCreateIdentity : SourceRoleIsSourceObjectIdentity → ⊥
sourceRoleDoesNotCreateIdentity ()

topicAnchorDoesNotDetermineSourceRole : TopicAnchorDeterminesSourceRole → ⊥
topicAnchorDoesNotDetermineSourceRole ()
