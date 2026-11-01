module DASHI.Wikimedia.IbrahimSnowballWitchGenealogyHistoricalAttributionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballQiHexagramWitchDivinationBidiExact as Symbolic
import DASHI.Governance.SuffrageWitchReclamationGenealogyExact as Genealogy
import DASHI.Governance.WitchTrialEvidenceSubjectAttributionExact as Trial
import DASHI.Culture.WitchSelfIdentificationPredicateUseBidiExact as SelfId

------------------------------------------------------------------------
-- IBRAHIM / QID / SNOWBALL HISTORICAL WELD
--
-- The shared lexical neighbourhood around "witch" is not an identity edge.
-- We retain separately:
--   * witchcraft as a cultural/conceptual object;
--   * an accused person and a prosecution event;
--   * modern Wicca;
--   * nineteenth-century Spiritualism;
--   * women's-suffrage politics;
--   * feminist symbolic reclamation;
--   * present self-identification.
--
-- QIDs below are current external identity/navigation coordinates inspected
-- 2026-09-10.  They import neither historical continuity nor metaphysical,
-- legal, religious, political, community or self-identification authority.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim witch genealogy / historical attribution BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-10; no same-object, genealogy, affiliation or authority promotion")

salemTrialsQid : Identity.ExternalIdentityDemand
salemTrialsQid = mkQid "Salem witch trials" "Q219698"

spiritualismQid : Identity.ExternalIdentityDemand
spiritualismQid = mkQid "Spiritualism (19th-century religious movement)" "Q829348"

womensSuffrageMovementQid : Identity.ExternalIdentityDemand
womensSuffrageMovementQid = mkQid "women's suffrage movement" "Q1222730"

feminismQid : Identity.ExternalIdentityDemand
feminismQid = mkQid "feminism" "Q7252"

witchcraftQid : Identity.ExternalIdentityDemand
witchcraftQid = Symbolic.witchcraftQid

wiccaQid : Identity.ExternalIdentityDemand
wiccaQid = Symbolic.wiccaQid

------------------------------------------------------------------------
-- Same lexical surface, different historical/source role.
------------------------------------------------------------------------

data WitchHistoricalCase : Set where
  accusedUnderProsecution : WitchHistoricalCase
  modernReligiousSelfIdentification : WitchHistoricalCase
  feministSymbolicReclamation : WitchHistoricalCase

data WitchLexicalSurface : Set where sameWitchToken : WitchLexicalSurface

data WitchHistoricalRole : Set where
  accusationRole : WitchHistoricalRole
  selfIdentificationRole : WitchHistoricalRole
  reclamationRole : WitchHistoricalRole

witchLexicalSurface : WitchHistoricalCase → WitchLexicalSurface
witchLexicalSurface _ = sameWitchToken

witchHistoricalRole : WitchHistoricalCase → WitchHistoricalRole
witchHistoricalRole accusedUnderProsecution = accusationRole
witchHistoricalRole modernReligiousSelfIdentification = selfIdentificationRole
witchHistoricalRole feministSymbolicReclamation = reclamationRole

witchLexicalHistoricalDefect :
  INF.NonFactorabilityWitness witchLexicalSurface witchHistoricalRole
witchLexicalHistoricalDefect = INF.nonFactorabilityWitness
  accusedUnderProsecution
  modernReligiousSelfIdentification
  refl
  (λ ())

witchTokenCannotFactorHistoricalRole :
  INF.FactorsThrough witchLexicalSurface witchHistoricalRole → ⊥
witchTokenCannotFactorHistoricalRole =
  INF.witnessRulesOutEveryFlatFactorisation witchLexicalHistoricalDefect

------------------------------------------------------------------------
-- Same broad movement-neighbourhood surface, different genealogy edge kind.
-- This blocks a graph traversal from upgrading adjacency/overlap/reclamation
-- into practitioner or institutional continuity.
------------------------------------------------------------------------

data GenealogyCase : Set where
  movementOverlapCase culturalAntecedentCase practitionerLineageCase : GenealogyCase

data GenealogyNeighbourhoodSurface : Set where sameMovementNeighbourhood : GenealogyNeighbourhoodSurface

data GenealogyEdgeReading : Set where
  overlapReading antecedentReading lineageReading : GenealogyEdgeReading

genealogyNeighbourhoodSurface : GenealogyCase → GenealogyNeighbourhoodSurface
genealogyNeighbourhoodSurface _ = sameMovementNeighbourhood

genealogyEdgeReading : GenealogyCase → GenealogyEdgeReading
genealogyEdgeReading movementOverlapCase = overlapReading
genealogyEdgeReading culturalAntecedentCase = antecedentReading
genealogyEdgeReading practitionerLineageCase = lineageReading

genealogyKindDefect :
  INF.NonFactorabilityWitness genealogyNeighbourhoodSurface genealogyEdgeReading
genealogyKindDefect = INF.nonFactorabilityWitness
  movementOverlapCase culturalAntecedentCase refl (λ ())

graphNeighbourhoodCannotFactorGenealogyKind :
  INF.FactorsThrough genealogyNeighbourhoodSurface genealogyEdgeReading → ⊥
graphNeighbourhoodCannotFactorGenealogyKind =
  INF.witnessRulesOutEveryFlatFactorisation genealogyKindDefect

------------------------------------------------------------------------
-- Reuse the exact existing owners rather than restating their historical claims.
------------------------------------------------------------------------

genealogyBoundary : Genealogy.SuffrageWitchGenealogyBoundary
genealogyBoundary = Genealogy.canonicalSuffrageWitchGenealogyBoundary

selfIdentificationBoundary :
  INF.FactorsThrough SelfId.witchSentence SelfId.witchUse → ⊥
selfIdentificationBoundary = SelfId.sameSentenceCannotRecoverUse

accusationAndSelfIdentificationDiffer :
  Trial.externallyAccusedWitch ≡ Trial.selfIdentifiedWitch → ⊥
accusationAndSelfIdentificationDiffer = Trial.accusation≠selfIdentification

symbolicBoundary : Symbolic.QiHexagramWitchDivinationBoundary
symbolicBoundary = Symbolic.canonicalQiHexagramWitchDivinationBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints forced back into broader Ibrahim nodes.
------------------------------------------------------------------------

record HistoricalReverseConstraint : Set where
  constructor historical-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open HistoricalReverseConstraint public

historyConstraint : HistoricalReverseConstraint
historyConstraint = historical-reverse-constraint
  "History"
  "accusation, prosecution record, later interpretation, movement genealogy, reclamation and present identity remain temporally/source indexed"
  false

religionConstraint : HistoricalReverseConstraint
religionConstraint = historical-reverse-constraint
  "Religion"
  "Spiritualism, Wicca, broader witchcraft vocabulary, ritual practice and individual affiliation remain distinct"
  false

politicsConstraint : HistoricalReverseConstraint
politicsConstraint = historical-reverse-constraint
  "Politics / feminism / suffrage"
  "women's-suffrage rights, movement participation, feminist critique and symbolic reclamation do not manufacture religious lineage"
  false

cultureConstraint : HistoricalReverseConstraint
cultureConstraint = historical-reverse-constraint
  "Culture / anthropology"
  "emic self-description, imposed category, observer classification, archival record and later cultural reuse retain separate source roles"
  false

------------------------------------------------------------------------
-- Explicit no-promotion gates.
------------------------------------------------------------------------

data SalemQidCreatesWiccanIdentity : Set where
data WitchcraftQidCreatesAccusedPersonIdentity : Set where
data SpiritualismCreatesWiccanContinuity : Set where
data SuffrageCreatesWitchAffiliation : Set where
data FeministReclamationRewritesHistoricalSelfIdentification : Set where
data GraphAdjacencyCreatesGenealogy : Set where

salemQidDoesNotCreateWiccanIdentity : SalemQidCreatesWiccanIdentity → ⊥
salemQidDoesNotCreateWiccanIdentity ()

witchcraftQidDoesNotCreateAccusedPersonIdentity :
  WitchcraftQidCreatesAccusedPersonIdentity → ⊥
witchcraftQidDoesNotCreateAccusedPersonIdentity ()

spiritualismDoesNotCreateWiccanContinuity : SpiritualismCreatesWiccanContinuity → ⊥
spiritualismDoesNotCreateWiccanContinuity ()

suffrageDoesNotCreateWitchAffiliation : SuffrageCreatesWitchAffiliation → ⊥
suffrageDoesNotCreateWitchAffiliation ()

feministReclamationDoesNotRewriteHistoricalSelfIdentification :
  FeministReclamationRewritesHistoricalSelfIdentification → ⊥
feministReclamationDoesNotRewriteHistoricalSelfIdentification ()

graphAdjacencyDoesNotCreateGenealogy : GraphAdjacencyCreatesGenealogy → ⊥
graphAdjacencyDoesNotCreateGenealogy ()

record WitchGenealogyHistoricalAttributionBoundary : Set where
  constructor witch-genealogy-historical-attribution-boundary
  field
    externalQidsSeparatedByObject : Bool
    accusationAndSelfIdentificationSeparated : Bool
    historicalEventAndModernAffiliationSeparated : Bool
    movementOverlapAndPractitionerLineageSeparated : Bool
    culturalAntecedentAndInstitutionalContinuitySeparated : Bool
    feministReclamationRetainsSourceAndTime : Bool
    historicalSourceRoleRetained : Bool
    twoEyedParticipantAndArchiveViewsRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    graphNeighbourhoodCreatesGenealogy : Bool
    presentAxisVocabularyClaimedComplete : Bool
open WitchGenealogyHistoricalAttributionBoundary public

canonicalWitchGenealogyHistoricalAttributionBoundary :
  WitchGenealogyHistoricalAttributionBoundary
canonicalWitchGenealogyHistoricalAttributionBoundary =
  witch-genealogy-historical-attribution-boundary
    true true true true true true true true true false false
