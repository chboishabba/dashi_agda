module DASHI.Law.SensibLawIsraelWestBankOperationalLegalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawOperationalLegalityExact as Operational

------------------------------------------------------------------------
-- ISRAEL / WEST BANK OPERATIONAL-LEGALITY FIXTURE
--
-- Source-bound consumer of the generic formal-rule / enforcement separation.
-- This file does not define Israeli domestic law, individual criminal
-- responsibility, settler identity, military status, intent, genocide, or a
-- complete account of the conflict.  The ICJ advisory opinion pays only the
-- international-law propositions it states; a separate joint opinion records
-- non-unanimity on the occupation-wide continued-presence conclusion.
------------------------------------------------------------------------

icj2024AdvisoryOpinion : Source.AttributedSource
icj2024AdvisoryOpinion = Source.mkNoDOISource
  "International Court of Justice"
  "Legal Consequences arising from the Policies and Practices of Israel in the Occupied Palestinian Territory, including East Jerusalem — Advisory Opinion of 19 July 2024"
  "International Court of Justice"
  "2024"
  "https://www.icj-cij.org/index.php/node/204160"
  (Source.namedSourceKind "international court advisory opinion")
  "Primary ICJ source for the Court's international-law findings on the settlement regime, its statement that outposts may be established contrary to Israeli domestic legislation and later regularised, and its finding of systematic failure to prevent or punish specified settler attacks. It is not an Israeli domestic-law authority and does not establish individual settler or soldier culpability."
  Source.publicAttribution

icj2024TomkaAbrahamAurescuJointOpinion : Source.AttributedSource
icj2024TomkaAbrahamAurescuJointOpinion = Source.mkNoDOISource
  "Judges Peter Tomka, Ronny Abraham and Bogdan Aurescu"
  "Joint opinion of Judges Tomka, Abraham and Aurescu"
  "International Court of Justice"
  "2024"
  "https://www.icj-cij.org/index.php/node/204164"
  (Source.namedSourceKind "judicial joint opinion")
  "Primary separate judicial source recording disagreement with the Court's conclusion that Israel's continued presence as occupying Power is itself unlawful. It records non-unanimity on that proposition and does not negate the propositions on settlement policy separately stated by the Court."
  Source.publicAttribution

israelWestBankOperationalLegalitySources : List Source.AttributedSource
israelWestBankOperationalLegalitySources =
  icj2024AdvisoryOpinion ∷
  icj2024TomkaAbrahamAurescuJointOpinion ∷
  []

israelWestBankOperationalLegalityAtlas : Source.AttributedSourceAtlas
israelWestBankOperationalLegalityAtlas = Source.mkSourceAtlas
  "Israel / West Bank operational-legality source atlas"
  "DASHI.Law.SensibLawIsraelWestBankOperationalLegalityExact"
  israelWestBankOperationalLegalitySources
  "ICJ primary advisory-opinion and joint-opinion sources retained separately. Domestic legality, international legality, enforcement practice, state attribution and individual responsibility remain distinct coordinates."

parentOperationalLegalityBoundary : Operational.OperationalLegalityBoundary
parentOperationalLegalityBoundary = Operational.canonicalOperationalLegalityBoundary

------------------------------------------------------------------------
-- Source-paid bounded coordinates.
------------------------------------------------------------------------

record IsraelWestBankOperationalLegalityBoundary : Set where
  constructor israelWestBankOperationalLegalityBoundary
  field
    parentOperationalLegalityReused : Bool
    icj2024AdvisoryOpinionPaid : Bool
    settlementRegimeInternationalIllegalityPaid : Bool
    domesticOutpostContraventionAndRegularisationPaid : Bool
    systematicFailurePreventPunishSettlerAttacksPaid : Bool
    advisoryOpinionUnanimousOnContinuedPresenceIllegality : Bool
    domesticLawfulnessAutomaticallyInternationalLawfulness : Bool
    internationalIllegalityAutomaticallyDomesticIllegality : Bool
    outpostDomesticContraventionAutomaticallyAllSettlementsDomesticIllegality : Bool
    nonEnforcementAutomaticallyEstablishesIndividualIntent : Bool
    settlerIdentityAutomaticallyStateAttribution : Bool
    settlerIdentityAutomaticallyIndividualCulpability : Bool
    conscriptionAutomaticallyIndividualCulpability : Bool
    materialSupportAutomaticallyIndividualIntent : Bool
    icjOpinionAutomaticallyIsraeliDomesticLawAuthority : Bool
    structuralFixtureAutomaticallyHistoricalEquivalence : Bool

open IsraelWestBankOperationalLegalityBoundary public

canonicalIsraelWestBankOperationalLegalityBoundary :
  IsraelWestBankOperationalLegalityBoundary
canonicalIsraelWestBankOperationalLegalityBoundary =
  israelWestBankOperationalLegalityBoundary
    true
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
    false
    false
    false
    false

------------------------------------------------------------------------
-- Empty bad-promotion propositions for downstream attribution/responsibility
-- consumers.
------------------------------------------------------------------------

data DomesticLawfulnessEstablishesInternationalLawfulness : Set where
data NonEnforcementEstablishesIndividualIntent : Set where
data SettlerIdentityEstablishesStateAttribution : Set where
data ConscriptionEstablishesIndividualCulpability : Set where

domesticLawfulnessDoesNotEstablishInternationalLawfulness :
  DomesticLawfulnessEstablishesInternationalLawfulness → ⊥
domesticLawfulnessDoesNotEstablishInternationalLawfulness ()

nonEnforcementDoesNotEstablishIndividualIntent :
  NonEnforcementEstablishesIndividualIntent → ⊥
nonEnforcementDoesNotEstablishIndividualIntent ()

settlerIdentityDoesNotEstablishStateAttribution :
  SettlerIdentityEstablishesStateAttribution → ⊥
settlerIdentityDoesNotEstablishStateAttribution ()

conscriptionDoesNotEstablishIndividualCulpability :
  ConscriptionEstablishesIndividualCulpability → ⊥
conscriptionDoesNotEstablishIndividualCulpability ()
