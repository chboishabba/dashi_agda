module DASHI.Law.SensibLawReligiousSocialBrokerageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.InstitutionalNormProductionExact as Norm
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Lobbying

------------------------------------------------------------------------
-- RELIGIOUS / SOCIAL BROKERAGE BOUNDARY
--
-- Source-bounded generic adapter for the proposition that religious and other
-- community institutions can create social networks, brokerage and political
-- communication channels.  It does not encode any user's family anecdote as
-- fact and does not infer corruption, quid pro quo, organised crime, influence
-- or a particular political outcome from membership, donation or clergy ties.
------------------------------------------------------------------------

stovelShawBrokerageSource : Source.AttributedSource
stovelShawBrokerageSource = Source.mkDOISource
  "Katherine Stovel and Lynette Shaw"
  "Brokerage"
  "Annual Review of Sociology 38:139-158"
  "2012"
  "10.1146/annurev-soc-081309-150054"
  "https://www.annualreviews.org/content/journals/10.1146/annurev-soc-081309-150054"
  Source.academicArticleSource
  "General sociological source for brokerage as a mechanism connecting otherwise disconnected actors/groups and for the possibility of both integrative and exploitative macro-level consequences. It does not establish brokerage, corruption or influence in any particular network."
  Source.publicAttribution

smithPoliticsParishSource : Source.AttributedSource
smithPoliticsParishSource = Source.mkNoDOISource
  "Gregory Allen Smith"
  "Politics in the Parish: The Political Influence of Catholic Priests"
  "Georgetown University Press"
  "2008"
  "https://press.georgetown.edu/Book/Politics-in-the-Parish"
  Source.academicBookSource
  "Publisher-source identity for an empirical study of Catholic clergy and parishioner political attitudes. The publisher description itself stresses that influence is nuanced, limited in magnitude and indirect; this source does not establish influence by any particular priest, parish, donor or family."
  Source.publicAttribution

religiousSocialBrokerageSources : List Source.AttributedSource
religiousSocialBrokerageSources =
  stovelShawBrokerageSource ∷ smithPoliticsParishSource ∷ []

religiousSocialBrokerageAtlas : Source.AttributedSourceAtlas
religiousSocialBrokerageAtlas = Source.mkSourceAtlas
  "religious and social brokerage source atlas"
  "DASHI.Law.SensibLawReligiousSocialBrokerageExact"
  religiousSocialBrokerageSources
  "General brokerage plus bounded empirical Catholic-parish political-influence scholarship. No case-specific relationship, corruption, quid pro quo, organised-crime or policy-outcome claim is promoted."

parentNormProductionBoundary : Norm.InstitutionalNormProductionBoundary
parentNormProductionBoundary = Norm.canonicalInstitutionalNormProductionBoundary

-- Reuse the existing investigative relation-kind discipline.  The Springfield
-- owner already separates donation, registered lobbying contact, employment,
-- partnership, corporate control, infrastructure alliance and ownership.
parentLobbyingSourceAtlas : Source.AttributedSourceAtlas
parentLobbyingSourceAtlas = Lobbying.springfieldInfluenceAtlas

record ReligiousSocialBrokerageBoundary : Set where
  constructor religiousSocialBrokerageBoundary
  field
    parentNormProductionReused : Bool
    parentLobbyingEdgeDisciplineReused : Bool
    generalBrokerageLiteraturePaid : Bool
    religiousNetworkPoliticalInfluenceLiteraturePaid : Bool
    churchMembershipAutomaticallyPoliticalInfluence : Bool
    religiousDonationAutomaticallyQuidProQuo : Bool
    clergyRelationshipAutomaticallyCorruption : Bool
    parishBelongingAutomaticallyMoralReliability : Bool
    institutionalRespectabilityAutomaticallySubstantiveAdequacy : Bool
    personalAnecdoteAutomaticallyHistoricalFact : Bool
    sourceScholarshipAutomaticallyCaseSpecificFinding : Bool

open ReligiousSocialBrokerageBoundary public

canonicalReligiousSocialBrokerageBoundary : ReligiousSocialBrokerageBoundary
canonicalReligiousSocialBrokerageBoundary =
  religiousSocialBrokerageBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Empty bad-promotion propositions for downstream use.
------------------------------------------------------------------------

data ChurchMembershipEstablishesPoliticalInfluence : Set where
data ClergyRelationshipEstablishesCorruption : Set where
data ReligiousDonationEstablishesQuidProQuo : Set where

churchMembershipDoesNotEstablishPoliticalInfluence :
  ChurchMembershipEstablishesPoliticalInfluence → ⊥
churchMembershipDoesNotEstablishPoliticalInfluence ()

clergyRelationshipDoesNotEstablishCorruption :
  ClergyRelationshipEstablishesCorruption → ⊥
clergyRelationshipDoesNotEstablishCorruption ()

religiousDonationDoesNotEstablishQuidProQuo :
  ReligiousDonationEstablishesQuidProQuo → ⊥
religiousDonationDoesNotEstablishQuidProQuo ()
