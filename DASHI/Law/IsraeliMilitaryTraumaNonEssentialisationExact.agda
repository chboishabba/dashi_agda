module DASHI.Law.IsraeliMilitaryTraumaNonEssentialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Israeli military trauma / moral-injury evidence with strict population
-- non-essentialisation.  Clinical findings about exposed combatants do not
-- become behavioural attributes of Israelis, Jews, Zionists, or emigrants.
------------------------------------------------------------------------

data TraumaSourceRole : Set where
  peerReviewedClinicalStudy
  militaryClinicalCohort
  prospectiveCombatantStudy
  veteranLongitudinalStudy
  dashiClinicalBoundary : TraumaSourceRole

data TraumaProposition : Set where
  moralInjuryAssociatedWithPsychiatricSymptoms
  ptsdObservedAmongCombatVeterans
  moralInjuryTrajectoriesAssociatedWithPTSDSymptoms
  combatExposureCanProducePsychologicalExternalities
  exConscriptBehaviourGenerallyIndicatesPTSD
  israeliBehaviourGenerallyIndicatesPTSD
  zionistBehaviourGenerallyIndicatesPTSD : TraumaProposition

record TraumaReceipt : Set where
  constructor traumaReceipt
  field
    proposition : TraumaProposition
    role : TraumaSourceRole
    sourceReference : String
    boundedDescription : String

open TraumaReceipt public

prospectiveMoralInjuryReceipt : TraumaReceipt
prospectiveMoralInjuryReceipt = traumaReceipt
  moralInjuryAssociatedWithPsychiatricSymptoms prospectiveCombatantStudy
  "Prospective study of 335 Israeli active-duty combatants, PMCID PMC10411436 / related publication"
  "Exposure to potentially morally injurious events was studied as a contributor to psychiatric and post-traumatic symptoms among Israeli combatants; the result concerns an exposed sample, not Israelis generally."

veteranTrajectoryReceipt : TraumaReceipt
veteranTrajectoryReceipt = traumaReceipt
  moralInjuryTrajectoriesAssociatedWithPTSDSymptoms veteranLongitudinalStudy
  "Levinstein et al., Journal of Psychiatric Research 177 (2024) 321-329, PMID 39067256"
  "Recently discharged Israeli veterans showed heterogeneous moral-injury trajectories associated with post-traumatic stress symptoms."

combatStressCohortReceipt : TraumaReceipt
combatStressCohortReceipt = traumaReceipt
  ptsdObservedAmongCombatVeterans militaryClinicalCohort
  "Representative/clinical cohort of IDF veterans seeking Combat Stress Reactions Unit assistance, 2000-2024"
  "PTSD symptoms are documented among combat veterans seeking military clinical assistance; help-seeking cohorts are not population-wide behavioural samples."

------------------------------------------------------------------------
-- Non-essentialisation firewall.
------------------------------------------------------------------------

record TraumaPopulationBoundary : Set where
  constructor traumaPopulationBoundary
  field
    veteranClinicalFindingImpliesEveryExConscriptHasPTSD : Bool
    veteranClinicalFindingImpliesEveryExConscriptHasPTSDIsFalse : veteranClinicalFindingImpliesEveryExConscriptHasPTSD ≡ false
    exConscriptUnusualBehaviourDiagnosesPTSD : Bool
    exConscriptUnusualBehaviourDiagnosesPTSDIsFalse : exConscriptUnusualBehaviourDiagnosesPTSD ≡ false
    ptsdFindingExplainsIsraeliNationalBehaviour : Bool
    ptsdFindingExplainsIsraeliNationalBehaviourIsFalse : ptsdFindingExplainsIsraeliNationalBehaviour ≡ false
    ptsdFindingExplainsZionistIdeology : Bool
    ptsdFindingExplainsZionistIdeologyIsFalse : ptsdFindingExplainsZionistIdeology ≡ false
    jewishIdentityCarriesMilitaryTrauma : Bool
    jewishIdentityCarriesMilitaryTraumaIsFalse : jewishIdentityCarriesMilitaryTrauma ≡ false

canonicalTraumaPopulationBoundary : TraumaPopulationBoundary
canonicalTraumaPopulationBoundary =
  traumaPopulationBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- BIDI claims.
------------------------------------------------------------------------

data TraumaClaim : Set where
  exposedVeteranMayHavePTSDOrMoralInjury
  particularPersonHasPTSD
  traumaContributedToParticularBehaviour
  diasporaExConscriptBehaviourIsTraumaDriven
  collectivePoliticalCultureIsPTSD : TraumaClaim

data TraumaProducer : Set where
  cohortClinicalProducer
  individualClinicalAssessmentProducer
  individualCausalClinicalProducer
  individualHistoryAndAssessmentProducer
  populationPsychosocialCausalProducer : TraumaProducer

reverseTrauma : TraumaClaim → TraumaProducer
reverseTrauma exposedVeteranMayHavePTSDOrMoralInjury = cohortClinicalProducer
reverseTrauma particularPersonHasPTSD = individualClinicalAssessmentProducer
reverseTrauma traumaContributedToParticularBehaviour = individualCausalClinicalProducer
reverseTrauma diasporaExConscriptBehaviourIsTraumaDriven = individualHistoryAndAssessmentProducer
reverseTrauma collectivePoliticalCultureIsPTSD = populationPsychosocialCausalProducer
