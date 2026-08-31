module DASHI.Governance.DrugGovernanceClassifierEvolutionPathExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.HistoricalDrugGovernanceClassifierExact as Historical
import DASHI.Governance.DrugGovernanceClassifierRevisionBackpropExact as Revision
import DASHI.Governance.WarOnDrugsHistoricalGenealogyExact as Genealogy

------------------------------------------------------------------------
-- DRUG-GOVERNANCE CLASSIFIER EVOLUTION PATH
--
-- Institutional classifiers evolve, but "changed" is not synonymous with
-- "learned the truth".  A revision may be evidence-responsive, political,
-- bureaucratic, commercial, rights/sovereignty-driven, or mixed.  This keeps
-- institutional adaptation distinct from epistemic improvement.
------------------------------------------------------------------------

data RevisionMode : Set where
  evidenceResponsiveRevision
  politicalStrategicRevision
  bureaucraticConsolidationRevision
  punitiveEscalationRevision
  commercialMedicalizationRevision
  rightsSovereigntyRevision
  mixedInstitutionalRevision
  : RevisionMode

data RevisionDriver : Set where
  scientificClinicalDriver
  treatmentCapacityDriver
  enforcementDriver
  electoralPoliticalDriver
  countercultureConflictDriver
  bureaucraticReorganizationDriver
  commercialInvestmentDriver
  rightsSovereigntyDriver
  publicHealthOutcomeDriver
  : RevisionDriver

record ClassifierTransition
    (before after : Historical.ClassifierVersion) : Set where
  constructor classifierTransition
  field
    mode : RevisionMode
    primaryDriver : RevisionDriver
    sourceReference : String
    evidenceReference : String
    politicalInstitutionalReference : String
    affectedRuleReference : String
    transitionMeansKnowledgeImprovement : Bool

open ClassifierTransition public

anslingerToNixon :
  ClassifierTransition
    Historical.federalNarcoticsVersion
    Historical.nixonEnforcementTreatmentVersion
anslingerToNixon = classifierTransition
  mixedInstitutionalRevision
  bureaucraticReorganizationDriver
  "Controlled Substances Act / 1971 presidential drug-war launch / later DEA consolidation"
  "treatment and scientific evidence remain separate from enforcement architecture"
  "Nixon-era classifier combines enforcement, treatment/public-health and internal policy dissent"
  "federal prohibition architecture revised into modern bifurcated enforcement/treatment classifier"
  false

nixonToReagan :
  ClassifierTransition
    Historical.nixonEnforcementTreatmentVersion
    Historical.reaganEscalationVersion
nixonToReagan = classifierTransition
  punitiveEscalationRevision
  enforcementDriver
  "Reagan-era punitive escalation and Anti-Drug Abuse Act context"
  "policy-outcome evidence does not become the definition of the transition"
  "sentencing/enforcement/prevention expansion"
  "punitive rule weights and reachable punishment cone strengthened"
  false

reaganToTrumpSplit :
  ClassifierTransition
    Historical.reaganEscalationVersion
    Historical.trumpPunitiveTherapeuticSplitVersion
reaganToTrumpSplit = classifierTransition
  mixedInstitutionalRevision
  scientificClinicalDriver
  "2026 punitive national drug strategy coexists with accelerated psychedelic/veteran therapeutic research"
  "psychedelic clinical/research evidence and regulatory access development"
  "punitive illicit-supply governance remains active while selected therapeutic routes reopen"
  "selected veteran/diagnosed/clinical carrier rules revised without globally removing punitive routes"
  false

------------------------------------------------------------------------
-- Indexed evolution path.
------------------------------------------------------------------------

data EvolutionPath :
    Historical.ClassifierVersion →
    Historical.ClassifierVersion → Set where
  pathRefl :
    ∀ {version} → EvolutionPath version version
  pathStep :
    ∀ {before middle after} →
    ClassifierTransition before middle →
    EvolutionPath middle after →
    EvolutionPath before after

canonicalClassifierEvolution :
  EvolutionPath
    Historical.federalNarcoticsVersion
    Historical.trumpPunitiveTherapeuticSplitVersion
canonicalClassifierEvolution =
  pathStep anslingerToNixon
    (pathStep nixonToReagan
      (pathStep reaganToTrumpSplit pathRefl))

------------------------------------------------------------------------
-- Path dependence: the 2026 classifier is historically downstream of several
-- distinct transition modes.  Present route does not erase those transitions.
------------------------------------------------------------------------

data HistoricalClassifierResidue : Set where
  federalProhibitionResidue
  nixonEnforcementTreatmentBifurcationResidue
  countercultureConflictResidue
  reaganPunitiveEscalationResidue
  psychedelicResearchReopeningResidue
  veteranTherapeuticPriorityResidue
  : HistoricalClassifierResidue

record EvolutionResidueLedger : Set where
  constructor evolutionResidueLedger
  field
    federalProhibitionRetained : Bool
    nixonBifurcationRetained : Bool
    countercultureConflictRetained : Bool
    reaganEscalationRetained : Bool
    psychedelicReopeningRetained : Bool
    veteranPriorityRetained : Bool

open EvolutionResidueLedger public

canonical2026ResidueLedger : EvolutionResidueLedger
canonical2026ResidueLedger = evolutionResidueLedger
  true true true true true true

------------------------------------------------------------------------
-- A changed classifier may be adaptive without being epistemically superior.
------------------------------------------------------------------------

data ClassifierChangePromotesEpistemicImprovement : Set where

data LaterClassifierPromotesJusticeImprovement : Set where

data TherapeuticExceptionPromotesGlobalDecriminalization : Set where

classifierChangeDoesNotPromoteEpistemicImprovement :
  ClassifierChangePromotesEpistemicImprovement → ⊥
classifierChangeDoesNotPromoteEpistemicImprovement ()

laterClassifierDoesNotPromoteJusticeImprovement :
  LaterClassifierPromotesJusticeImprovement → ⊥
laterClassifierDoesNotPromoteJusticeImprovement ()

therapeuticExceptionDoesNotPromoteGlobalDecriminalization :
  TherapeuticExceptionPromotesGlobalDecriminalization → ⊥
therapeuticExceptionDoesNotPromoteGlobalDecriminalization ()

genealogyBoundary : Genealogy.WarOnDrugsHistoricalGenealogyBoundary
genealogyBoundary = Genealogy.canonicalWarOnDrugsHistoricalGenealogyBoundary

revisionBoundary : Revision.DrugGovernanceClassifierRevisionBoundary
revisionBoundary = Revision.canonicalDrugGovernanceClassifierRevisionBoundary

record DrugGovernanceClassifierEvolutionBoundary : Set where
  constructor drugGovernanceClassifierEvolutionBoundary
  field
    classifierEvolutionIsPathIndexed : Bool
    classifierEvolutionIsPathIndexedIsTrue :
      classifierEvolutionIsPathIndexed ≡ true
    policyRevisionCanHaveMultipleDriverKinds : Bool
    policyRevisionCanHaveMultipleDriverKindsIsTrue :
      policyRevisionCanHaveMultipleDriverKinds ≡ true
    classifierChangeEqualsEpistemicLearning : Bool
    classifierChangeEqualsEpistemicLearningIsFalse :
      classifierChangeEqualsEpistemicLearning ≡ false
    laterClassifierAutomaticallyMoreJust : Bool
    laterClassifierAutomaticallyMoreJustIsFalse :
      laterClassifierAutomaticallyMoreJust ≡ false
    presentTherapeuticRouteErasesPunitiveHistory : Bool
    presentTherapeuticRouteErasesPunitiveHistoryIsFalse :
      presentTherapeuticRouteErasesPunitiveHistory ≡ false

canonicalDrugGovernanceClassifierEvolutionBoundary :
  DrugGovernanceClassifierEvolutionBoundary
canonicalDrugGovernanceClassifierEvolutionBoundary =
  drugGovernanceClassifierEvolutionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
