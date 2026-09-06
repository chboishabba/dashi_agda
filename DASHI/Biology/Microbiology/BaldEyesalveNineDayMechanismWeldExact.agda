module DASHI.Biology.Microbiology.BaldEyesalveNineDayMechanismWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AlliumMolecularTrajectoryExact as Trajectory
import DASHI.Biology.Protein.StaphylococcusAllicinThiolomeExact as Thiolome
import DASHI.Biology.Microbiology.BaldEyesalveMechanismBoundaryExact as Eyesalve
import DASHI.Biology.Microbiology.QuorumSensingContextExact as QS

------------------------------------------------------------------------
-- NINE-DAY PREPARATION -> MOLECULAR-MECHANISM WELD
--
-- This closes a structural gap in the earlier tranche: known Allium chemical
-- transformations and direct S. aureus allicin-thiolome evidence now feed the
-- eyesalve mechanism frontier through explicit target-preparation obligations.
-- Nothing here claims the relevant compounds were measured in the historical
-- mixture at day 9; that remains an experimental producer.
------------------------------------------------------------------------

data MechanismLane : Set where
  allicinThiolStress
  bacillithiolRedoxShift
  proteinSThioallylation
  transcriptionalRegulatorPerturbation
  quorumRelatedRegulatoryPerturbation
  biofilmMatrixOrPenetration
  downstreamOrganosulfurChemistry
  : MechanismLane

record NineDayMechanismCandidate : Set where
  constructor nineDayMechanismCandidate
  field
    lane : MechanismLane
    chemistrySource : String
    targetOrganismSource : String
    targetPreparationPresenceMeasured : Bool
    targetPreparationMolecularActionMeasured : Bool
    phenotypeMediationMeasured : Bool
    interpretation : String

open NineDayMechanismCandidate public

allicinThiolCandidate : NineDayMechanismCandidate
allicinThiolCandidate = nineDayMechanismCandidate
  allicinThiolStress
  "Allium allicin identity and thiol chemistry"
  "Loi et al. 2019 S. aureus allicin thiolome"
  true
  false
  false
  "allicin is evidenced in reconstructed eyesalve work, but the full day-9 target-system thiolome remains unmeasured"

staphRegulatorCandidate : NineDayMechanismCandidate
staphRegulatorCandidate = nineDayMechanismCandidate
  transcriptionalRegulatorPerturbation
  "allicin S-thioallylation chemistry"
  "MgrA/SarA/SarH1/SarS targets in S. aureus under allicin stress"
  true
  false
  false
  "direct species-level target evidence sharpens the candidate without proving that the complete eyesalve phenotype is mediated through these regulators"

quorumCandidate : NineDayMechanismCandidate
quorumCandidate = nineDayMechanismCandidate
  quorumRelatedRegulatoryPerturbation
  "garlic organosulfur / ajoene quorum-sensing literature"
  "S. aureus regulator and stress-response literature plus Pseudomonas anti-QS literature"
  false
  false
  false
  "remains a hypothesis lane until compound presence, reporter response, and mediation are measured in the target preparation and organism"

downstreamChemistryCandidate : NineDayMechanismCandidate
downstreamChemistryCandidate = nineDayMechanismCandidate
  downstreamOrganosulfurChemistry
  "allicin can transform into DADS/DATS/polysulfanes/vinyl dithiins/ajoene in context-dependent processing chemistry"
  "compound-specific biological actions are source-indexed"
  false
  false
  false
  "nine-day maturation makes time-resolved sulfur speciation a high-value missing producer"

record DirectPromotionReceipt : Set where
  constructor directPromotionReceipt
  field
    candidate : NineDayMechanismCandidate
    compoundPresenceDayResolved : Bool
    concentrationOrExposureResolved : Bool
    molecularTargetChangeObserved : Bool
    functionalPathwayChangeObserved : Bool
    phenotypeCovariesWithMechanism : Bool
    perturbationOrRescueSupportsMediation : Bool
    validationReference : String

open DirectPromotionReceipt public

record NineDayMechanismBoundary : Set where
  constructor nineDayMechanismBoundary
  field
    maturationEfficacyDifferenceProvesChemicalIdentityOfCause : Bool
    maturationEfficacyDifferenceProvesChemicalIdentityOfCauseIsFalse :
      maturationEfficacyDifferenceProvesChemicalIdentityOfCause ≡ false

    directSAureusAllicinThiolomeProvesWholeEyesalveMechanism : Bool
    directSAureusAllicinThiolomeProvesWholeEyesalveMechanismIsFalse :
      directSAureusAllicinThiolomeProvesWholeEyesalveMechanism ≡ false

    garlicQuorumLiteratureProvesEyesalveQuorumMediation : Bool
    garlicQuorumLiteratureProvesEyesalveQuorumMediationIsFalse :
      garlicQuorumLiteratureProvesEyesalveQuorumMediation ≡ false

    tangentialMechanismEvidenceCanReduceExperimentalSearchSpace : Bool
    tangentialMechanismEvidenceCanReduceExperimentalSearchSpaceIsTrue :
      tangentialMechanismEvidenceCanReduceExperimentalSearchSpace ≡ true

    shortestProducerIsTimeResolvedChemistryThenMechanismAssay : Bool
    shortestProducerIsTimeResolvedChemistryThenMechanismAssayIsTrue :
      shortestProducerIsTimeResolvedChemistryThenMechanismAssay ≡ true

canonicalNineDayMechanismBoundary : NineDayMechanismBoundary
canonicalNineDayMechanismBoundary = nineDayMechanismBoundary
  false refl false refl false refl true refl true refl

------------------------------------------------------------------------
-- BIDI exports: existing owners are consumed explicitly so this is not a
-- parallel ontology.  The new frontier is the missing weld among preparation
-- trajectory, S. aureus thiolome, quorum context, and eyesalve phenotype.
------------------------------------------------------------------------

existingTrajectoryBoundary : Trajectory.MolecularTrajectoryBoundary
existingTrajectoryBoundary = Trajectory.canonicalMolecularTrajectoryBoundary

existingStaphBoundary : Thiolome.StaphylococcusAllicinBoundary
existingStaphBoundary = Thiolome.canonicalStaphylococcusAllicinBoundary

existingEyesalveBoundary : Eyesalve.BaldEyesalveMechanismBoundary
existingEyesalveBoundary = Eyesalve.canonicalBaldEyesalveMechanismBoundary

existingQuorumBoundary : QS.QuorumSensingBoundary
existingQuorumBoundary = QS.canonicalQuorumSensingBoundary
