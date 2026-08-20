module DASHI.Governance.AuthorityBearingLegibilityFailureExact where

------------------------------------------------------------------------
-- AUTHORITY-BEARING LEGIBILITY FAILURE
--
-- A lossy representation is more consequential when an institution acts on
-- that representation.  This module separates representation loss, authority
-- and downstream material consequence.
--
-- Sources / bounded roles:
--
-- Cooper v Stuart (1889) 14 App Cas 286 (Privy Council), no DOI asserted.
-- Source role: historical settled-colony doctrine and the language concerning
-- absence of "settled inhabitants" / "settled law".
--
-- Mabo v Queensland (No 2) [1992] HCA 23; 175 CLR 1.
-- High Court of Australia, 3 June 1992. No DOI asserted.
-- Source role: rejection of the enlarged terra-nullius/settled-colony fiction
-- as an impediment to recognition of native title.  This file does not convert
-- that legal correction into a claim that dispossession was thereby repaired.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record SocialWorld : Set where
  constructor socialWorld
  field
    lawPresent : Bool
    polityPresent : Bool
    landRelationsPresent : Bool

record AuthorityRepresentation : Set where
  constructor authorityRepresentation
  field
    recognisesLaw : Bool
    recognisesPolity : Bool
    recognisesLandRelations : Bool

record AuthorityAction : Set where
  constructor authorityAction
  field
    actionLabel : Nat

record LegibilityFailure : Set where
  constructor legibilityFailure
  field
    world : SocialWorld
    representation : AuthorityRepresentation
    lawLost : SocialWorld.lawPresent world ≡ true
            × AuthorityRepresentation.recognisesLaw representation ≡ false
    polityLost : SocialWorld.polityPresent world ≡ true
               × AuthorityRepresentation.recognisesPolity representation ≡ false

indigenousWorldWitness : SocialWorld
indigenousWorldWitness = socialWorld true true true

settledColonyRepresentationWitness : AuthorityRepresentation
settledColonyRepresentationWitness = authorityRepresentation false false false

canonicalLegibilityFailure : LegibilityFailure
canonicalLegibilityFailure =
  legibilityFailure indigenousWorldWitness settledColonyRepresentationWitness
    (refl , refl) (refl , refl)

record AuthorityBearingFailure : Set where
  constructor authorityBearingFailure
  field
    failure : LegibilityFailure
    institutionalAuthorityActs : Bool
    materialConsequencePresent : Bool

canonicalAuthorityBearingFailure : AuthorityBearingFailure
canonicalAuthorityBearingFailure = authorityBearingFailure canonicalLegibilityFailure true true

data RepresentationLossPromotesMotive : Set where

data LegalCorrectionPromotesMaterialRepair : Set where

data SocialWorldDifferencePromotesMoralHierarchy : Set where

representationLossDoesNotPromoteMotive : RepresentationLossPromotesMotive → ⊥
representationLossDoesNotPromoteMotive ()

legalCorrectionDoesNotPromoteMaterialRepair : LegalCorrectionPromotesMaterialRepair → ⊥
legalCorrectionDoesNotPromoteMaterialRepair ()

socialWorldDifferenceDoesNotPromoteMoralHierarchy : SocialWorldDifferencePromotesMoralHierarchy → ⊥
socialWorldDifferenceDoesNotPromoteMoralHierarchy ()

record AuthorityBearingLegibilityBoundary : Set where
  constructor authorityBearingLegibilityBoundary
  field
    lossyRepresentationCanFeedInstitutionalAction : Bool
    representationLossEqualsMotive : Bool
    judicialCorrectionEqualsCompleteMaterialRepair : Bool
    terraNulliusCorrectionRetainsHistoricalConsequencesAsSeparateQuestion : Bool

canonicalAuthorityBearingLegibilityBoundary : AuthorityBearingLegibilityBoundary
canonicalAuthorityBearingLegibilityBoundary =
  authorityBearingLegibilityBoundary true false false true
