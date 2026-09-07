module DASHI.Biology.Microbiology.BaldEyesalveNineDayMechanismWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AlliumMolecularTrajectoryExact as Trajectory
import DASHI.Biology.Protein.StaphylococcusAllicinThiolomeExact as Thiolome
import DASHI.Biology.Cell.StaphylococcusAllicinRedoxRecoveryBidiExact as CellRedox
import DASHI.Biology.Microbiology.BaldEyesalveMechanismBoundaryExact as Eyesalve
import DASHI.Biology.Microbiology.QuorumSensingContextExact as QS

------------------------------------------------------------------------
-- NINE-DAY PREPARATION -> MOLECULAR-MECHANISM -> RECOVERY WELD
------------------------------------------------------------------------

data MechanismLane : Set where
  allicinThiolStress : MechanismLane
  bacillithiolRedoxShift : MechanismLane
  proteinSThioallylation : MechanismLane
  transcriptionalRegulatorPerturbation : MechanismLane
  quorumRelatedRegulatoryPerturbation : MechanismLane
  biofilmMatrixOrPenetration : MechanismLane
  downstreamOrganosulfurChemistry : MechanismLane
  detoxificationRecoveryCompetition : MechanismLane


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
  true false false
  "allicin is evidenced in reconstructed eyesalve work, but the full day-9 target-system thiolome remains unmeasured"

staphRegulatorCandidate : NineDayMechanismCandidate
staphRegulatorCandidate = nineDayMechanismCandidate
  transcriptionalRegulatorPerturbation
  "allicin S-thioallylation chemistry"
  "MgrA/SarA/SarH1/SarS targets in S. aureus under allicin stress"
  true false false
  "direct species-level target evidence sharpens the candidate without proving mixture-level mediation"

quorumCandidate : NineDayMechanismCandidate
quorumCandidate = nineDayMechanismCandidate
  quorumRelatedRegulatoryPerturbation
  "garlic organosulfur / ajoene quorum-sensing literature"
  "S. aureus regulator/stress literature plus Pseudomonas anti-QS literature"
  false false false
  "requires compound-presence, reporter-response and mediation welds in the target preparation and organism"

downstreamChemistryCandidate : NineDayMechanismCandidate
downstreamChemistryCandidate = nineDayMechanismCandidate
  downstreamOrganosulfurChemistry
  "allicin can transform into DADS/DATS/polysulfanes/vinyl dithiins/ajoene in context-dependent processing chemistry"
  "compound-specific biological actions remain source-indexed"
  false false false
  "nine-day maturation makes time-resolved sulfur speciation a high-value missing producer"

recoveryCompetitionCandidate : NineDayMechanismCandidate
recoveryCompetitionCandidate = nineDayMechanismCandidate
  detoxificationRecoveryCompetition
  "allicin-mediated thiol modification opposed by cellular thiol-recovery chemistry"
  "Loi et al. 2019 DOI 10.1016/j.freeradbiomed.2019.05.018; BSH/BrxAB/YpdA/MerA"
  true false false
  "phenotype depends on disturbance-versus-recovery dynamics, not chemical insult alone; the complete eyesalve recovery trajectory remains unmeasured"

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
    detoxificationResponseProvesCompletePhenotypicRecovery : Bool
    detoxificationResponseProvesCompletePhenotypicRecoveryIsFalse :
      detoxificationResponseProvesCompletePhenotypicRecovery ≡ false
    tangentialMechanismEvidenceCanReduceExperimentalSearchSpace : Bool
    tangentialMechanismEvidenceCanReduceExperimentalSearchSpaceIsTrue :
      tangentialMechanismEvidenceCanReduceExperimentalSearchSpace ≡ true
    shortestProducerIsTimeResolvedChemistryThenMechanismAssay : Bool
    shortestProducerIsTimeResolvedChemistryThenMechanismAssayIsTrue :
      shortestProducerIsTimeResolvedChemistryThenMechanismAssay ≡ true

canonicalNineDayMechanismBoundary : NineDayMechanismBoundary
canonicalNineDayMechanismBoundary = nineDayMechanismBoundary
  false refl false refl false refl false refl true refl true refl

------------------------------------------------------------------------
-- BIDI exports: consume canonical owners explicitly, including the newly
-- extended generic cell-recovery seam through the S. aureus-specific adapter.
------------------------------------------------------------------------

existingTrajectoryBoundary : Trajectory.MolecularTrajectoryBoundary
existingTrajectoryBoundary = Trajectory.canonicalMolecularTrajectoryBoundary

existingStaphBoundary : Thiolome.StaphylococcusAllicinBoundary
existingStaphBoundary = Thiolome.canonicalStaphylococcusAllicinBoundary

existingCellRedoxBoundary : CellRedox.RedoxRecoveryInterpretationBoundary
existingCellRedoxBoundary = CellRedox.canonicalRedoxRecoveryInterpretationBoundary

existingEyesalveBoundary : Eyesalve.BaldEyesalveMechanismBoundary
existingEyesalveBoundary = Eyesalve.canonicalBaldEyesalveMechanismBoundary

existingQuorumBoundary : QS.QSBoundary
existingQuorumBoundary = QS.canonicalQSBoundary
