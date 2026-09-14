module DASHI.Law.NaziBureaucraticParticipationResponsibilitySourceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.FragmentationCompositionExact as Fragmentation
import DASHI.Law.SensibLawInstitutionalResponsibilityExact as Responsibility

------------------------------------------------------------------------
-- NAZI BUREAUCRATIC PARTICIPATION / RESPONSIBILITY — SOURCE BOUNDARY
--
-- Historical fixture over the generic local/global fragmentation and typed
-- responsibility parents.  It source-binds the documented participation of
-- ordinary administrative roles in Nazi persecution and the Nürnberg superior-
-- orders principle without turning role membership into automatic guilt or
-- making every structurally fragmented modern institution historically/legal-
-- equivalent to Nazi Germany.
------------------------------------------------------------------------

ushmmBystandersSource : Source.AttributedSource
ushmmBystandersSource = Source.mkNoDOISource
  "United States Holocaust Memorial Museum"
  "Bystanders"
  "Holocaust Encyclopedia"
  "current public encyclopedia surface"
  "https://encyclopedia.ushmm.org/content/en/article/bystanders"
  Source.institutionalSource
  "Institutional historical source documenting involvement across levels of society, including civil servants performing ordinary administrative tasks such as tax/property processing and clerical identity-record work, as part of Nazi racial and antisemitic policies. It does not assign criminal liability to every holder of an administrative role."
  Source.publicAttribution

nurembergPrincipleIVSource : Source.AttributedSource
nurembergPrincipleIVSource = Source.mkNoDOISource
  "United Nations — International Law Commission / General Assembly"
  "Principles of International Law Recognized in the Charter of the Nürnberg Tribunal and in the Judgment of the Tribunal — Principle IV"
  "United Nations Audiovisual Library of International Law"
  "1950 / current explanatory surface"
  "https://legal.un.org/avl/ha/ga_95-I/ga_95-I.html"
  (Source.namedSourceKind "international legal source")
  "International-law source for Principle IV: acting pursuant to Government/superior order does not itself relieve responsibility where a moral choice was in fact possible. It does not eliminate the need for offence elements, individual facts, defences or competent adjudication."
  Source.publicAttribution

naziBureaucraticParticipationSources : List Source.AttributedSource
naziBureaucraticParticipationSources =
  ushmmBystandersSource ∷ nurembergPrincipleIVSource ∷ []

naziBureaucraticParticipationAtlas : Source.AttributedSourceAtlas
naziBureaucraticParticipationAtlas = Source.mkSourceAtlas
  "Nazi bureaucratic participation / responsibility source atlas"
  "DASHI.Law.NaziBureaucraticParticipationResponsibilitySourceBoundaryExact"
  naziBureaucraticParticipationSources
  "Historical participation and superior-orders responsibility sources retained separately; ordinary-role participation, causal contribution, knowledge, choice and legal culpability remain distinct coordinates."

parentFragmentationBoundary : Fragmentation.FragmentationBoundary
parentFragmentationBoundary = Fragmentation.canonicalFragmentationBoundary

parentResponsibilityBoundary : Responsibility.InstitutionalResponsibilityBoundary
parentResponsibilityBoundary = Responsibility.canonicalInstitutionalResponsibilityBoundary

record NaziBureaucraticParticipationBoundary : Set where
  constructor naziBureaucraticParticipationBoundary
  field
    parentFragmentationReused : Bool
    parentResponsibilitySeparationReused : Bool
    ushmmBureaucraticParticipationSourcePaid : Bool
    nurembergSuperiorOrdersPrinciplePaid : Bool
    routineAdministrativeTaskAutomaticallyHarmless : Bool
    localProceduralIntelligibilityAutomaticallyGlobalDefensibility : Bool
    roleMembershipAutomaticallyIndividualCriminalCulpability : Bool
    causalContributionAutomaticallyCriminalCulpability : Bool
    superiorOrderAutomaticallyEliminatesResponsibility : Bool
    lackOfSystemOverviewAutomaticallyEliminatesResponsibility : Bool
    sharedFragmentationStructureAutomaticallyHistoricalEquivalence : Bool
    historicalSourceAutomaticallyDeterminesModernCaseResponsibility : Bool

open NaziBureaucraticParticipationBoundary public

canonicalNaziBureaucraticParticipationBoundary :
  NaziBureaucraticParticipationBoundary
canonicalNaziBureaucraticParticipationBoundary =
  naziBureaucraticParticipationBoundary
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

data RoutineTaskEstablishesHarmlessness : Set where
data RoleMembershipEstablishesCriminalCulpability : Set where
data SuperiorOrderEliminatesResponsibility : Set where

routineTaskDoesNotEstablishHarmlessness :
  RoutineTaskEstablishesHarmlessness → ⊥
routineTaskDoesNotEstablishHarmlessness ()

roleMembershipDoesNotEstablishCriminalCulpability :
  RoleMembershipEstablishesCriminalCulpability → ⊥
roleMembershipDoesNotEstablishCriminalCulpability ()

superiorOrderDoesNotAutomaticallyEliminateResponsibility :
  SuperiorOrderEliminatesResponsibility → ⊥
superiorOrderDoesNotAutomaticallyEliminateResponsibility ()
