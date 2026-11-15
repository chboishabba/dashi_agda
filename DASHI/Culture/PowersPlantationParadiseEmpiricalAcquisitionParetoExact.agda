module DASHI.Culture.PowersPlantationParadiseEmpiricalAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierContractExact as Contract
import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical

------------------------------------------------------------------------
-- POWERS EMPIRICAL ACQUISITION PARETO ROUTER
--
-- Calibration is recomputed after evidence acquisition.  Cost/gain values are
-- routing coordinates only, never truth, importance, culpability, welfare or
-- causal-effect scores.  Off-frontier requirements remain live requirements.
------------------------------------------------------------------------

data AcquisitionRequirement : Set where
  primaryCorpusSaturation : AcquisitionRequirement
  compensationLedgerRecovery : AcquisitionRequirement
  distributionalIncidenceRecovery : AcquisitionRequirement
  causalIdentificationRecovery : AcquisitionRequirement
  seatingPrimaryRecordRecovery : AcquisitionRequirement
  performerPrimaryRecordRecovery : AcquisitionRequirement

primaryCorpusCell : Pareto.RequirementCandidate AcquisitionRequirement
primaryCorpusCell =
  Pareto.requirement-candidate
    primaryCorpusSaturation
    true true true true
    2 8
    "root exact Affiches/DLOC/ANOM event rows; resolves multiple performer, chronology, payment and access fibres"

-- After recovering Minette's exact contracted amount and documented nonpayment,
-- compensation's remaining leaf is narrower: estate settlement and actual
-- benefit-night proceeds.  It is still required, but no longer Pareto-frontier
-- optimal against the broader corpus route.
compensationLedgerCell : Pareto.RequirementCandidate AcquisitionRequirement
compensationLedgerCell =
  Pareto.requirement-candidate
    compensationLedgerRecovery
    true true true true
    4 6
    "Saint-Martin estate/executor settlement plus benefit-night net-receipt evidence"

-- Actor-level distribution remains broader than the currently paid category and
-- contribution x burden joins because benefit, surplus and voice are still open.
distributionalIncidenceCell : Pareto.RequirementCandidate AcquisitionRequirement
distributionalIncidenceCell =
  Pareto.requirement-candidate
    distributionalIncidenceRecovery
    true true true true
    5 10
    "same-object contribution/benefit/burden/voice join across named actor, venue and time"

causalIdentificationCell : Pareto.RequirementCandidate AcquisitionRequirement
causalIdentificationCell =
  Pareto.requirement-candidate
    causalIdentificationRecovery
    true true true true
    8 7
    "case-specific counterfactual/identification design after richer descriptive trajectories exist"

seatingPrimaryCell : Pareto.RequirementCandidate AcquisitionRequirement
seatingPrimaryCell =
  Pareto.requirement-candidate
    seatingPrimaryRecordRecovery
    true true true true
    3 5
    "ANOM theatre-plan original plus Saint-Domingue-specific seating/admission rules"

performerPrimaryCell : Pareto.RequirementCandidate AcquisitionRequirement
performerPrimaryCell =
  Pareto.requirement-candidate
    performerPrimaryRecordRecovery
    true true true true
    4 6
    "exact primary rows for Minette, Lise and other named performers after current secondary-coordinate recovery"

acquisitionPortfolio : List (Pareto.RequirementCandidate AcquisitionRequirement)
acquisitionPortfolio =
  primaryCorpusCell
  ∷ compensationLedgerCell
  ∷ distributionalIncidenceCell
  ∷ causalIdentificationCell
  ∷ seatingPrimaryCell
  ∷ performerPrimaryCell
  ∷ []

empiricalAcquisitionFrontier : List (Pareto.RequirementCandidate AcquisitionRequirement)
empiricalAcquisitionFrontier = Pareto.paretoFrontier acquisitionPortfolio

primaryCorpusOnCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio primaryCorpusCell ≡ true
primaryCorpusOnCurrentFrontier = refl

compensationLedgerOffCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio compensationLedgerCell ≡ false
compensationLedgerOffCurrentFrontier = refl

distributionalIncidenceOnCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio distributionalIncidenceCell ≡ true
distributionalIncidenceOnCurrentFrontier = refl

causalIdentificationOffCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio causalIdentificationCell ≡ false
causalIdentificationOffCurrentFrontier = refl

seatingPrimaryOffCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio seatingPrimaryCell ≡ false
seatingPrimaryOffCurrentFrontier = refl

performerPrimaryOffCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio performerPrimaryCell ≡ false
performerPrimaryOffCurrentFrontier = refl

currentFrontierIsCorpusDistribution :
  empiricalAcquisitionFrontier
  ≡ primaryCorpusCell ∷ distributionalIncidenceCell ∷ []
currentFrontierIsCorpusDistribution = refl

primaryCorpusLeaf : Empirical.EmpiricalProgrammeLeaf
primaryCorpusLeaf = Empirical.primaryCorpusSaturationLeaf

compensationLeaf : Empirical.EmpiricalProgrammeLeaf
compensationLeaf = Empirical.compensationPaymentLeaf

distributionLeaf : Empirical.EmpiricalProgrammeLeaf
distributionLeaf = Empirical.distributionalIncidenceLeaf

causalLeaf : Empirical.EmpiricalProgrammeLeaf
causalLeaf = Empirical.causalMobilityLeaf

seatingLeaf : Empirical.EmpiricalProgrammeLeaf
seatingLeaf = Empirical.venueSeatingAccessLeaf

performerLeaf : Empirical.EmpiricalProgrammeLeaf
performerLeaf = Empirical.namedPerformerStatusLeaf

paretoContract : Contract.FiniteRequirementParetoContract
paretoContract = Contract.canonicalFiniteRequirementParetoContract

record PowersEmpiricalAcquisitionParetoBoundary : Set where
  constructor powers-empirical-acquisition-pareto-boundary
  field
    currentFrontierHasMultipleRoutes : Bool
    currentFrontierHasMultipleRoutesIsTrue : currentFrontierHasMultipleRoutes ≡ true
    compensationStillRequiredOffFrontier : Bool
    compensationStillRequiredOffFrontierIsTrue : compensationStillRequiredOffFrontier ≡ true
    frontierMembershipPaysHistoricalClaim : Bool
    frontierMembershipPaysHistoricalClaimIsFalse : frontierMembershipPaysHistoricalClaim ≡ false
    offFrontierDeletesRequirement : Bool
    offFrontierDeletesRequirementIsFalse : offFrontierDeletesRequirement ≡ false
    costGainCalibrationIsTruthScore : Bool
    costGainCalibrationIsTruthScoreIsFalse : costGainCalibrationIsTruthScore ≡ false
    causalIdentificationStillRequired : Bool
    causalIdentificationStillRequiredIsTrue : causalIdentificationStillRequired ≡ true

canonicalPowersEmpiricalAcquisitionParetoBoundary : PowersEmpiricalAcquisitionParetoBoundary
canonicalPowersEmpiricalAcquisitionParetoBoundary =
  powers-empirical-acquisition-pareto-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
