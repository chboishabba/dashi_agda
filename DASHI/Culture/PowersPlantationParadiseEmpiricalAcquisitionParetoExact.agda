module DASHI.Culture.PowersPlantationParadiseEmpiricalAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierContractExact as Contract
import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical

------------------------------------------------------------------------
-- POWERS EMPIRICAL ACQUISITION PARETO ROUTER
--
-- Cost/gain coordinates are acquisition-routing calibration only.  They are
-- not truth probabilities, historical importance scores, culpability weights,
-- welfare weights or causal-effect magnitudes.  Frontier membership does not
-- pay the requirement.
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
    "St Andrews performance database + Affiches Americaines issue-level saturation"

compensationLedgerCell : Pareto.RequirementCandidate AcquisitionRequirement
compensationLedgerCell =
  Pareto.requirement-candidate
    compensationLedgerRecovery
    true true true true
    3 9
    "contracts, benefit-night receipts, payroll/account fragments and settlement evidence"

distributionalIncidenceCell : Pareto.RequirementCandidate AcquisitionRequirement
distributionalIncidenceCell =
  Pareto.requirement-candidate
    distributionalIncidenceRecovery
    true true true true
    5 10
    "same-object contribution/benefit/burden/voice join across performer, venue and time"

causalIdentificationCell : Pareto.RequirementCandidate AcquisitionRequirement
causalIdentificationCell =
  Pareto.requirement-candidate
    causalIdentificationRecovery
    true true true true
    8 7
    "case-specific counterfactual/identification design after richer observational fibres exist"

seatingPrimaryCell : Pareto.RequirementCandidate AcquisitionRequirement
seatingPrimaryCell =
  Pareto.requirement-candidate
    seatingPrimaryRecordRecovery
    true true true true
    3 5
    "ANOM theatre-plan original plus applicable seating/admission regulations"

performerPrimaryCell : Pareto.RequirementCandidate AcquisitionRequirement
performerPrimaryCell =
  Pareto.requirement-candidate
    performerPrimaryRecordRecovery
    true true true true
    4 7
    "exact Affiches/Moreau/litigation rows for named performers such as Minette and Lise"

acquisitionPortfolio :
  List (Pareto.RequirementCandidate AcquisitionRequirement)
acquisitionPortfolio =
  primaryCorpusCell
  ∷ compensationLedgerCell
  ∷ distributionalIncidenceCell
  ∷ causalIdentificationCell
  ∷ seatingPrimaryCell
  ∷ performerPrimaryCell
  ∷ []

empiricalAcquisitionFrontier :
  List (Pareto.RequirementCandidate AcquisitionRequirement)
empiricalAcquisitionFrontier = Pareto.paretoFrontier acquisitionPortfolio

primaryCorpusOnCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio primaryCorpusCell ≡ true
primaryCorpusOnCurrentFrontier = refl

compensationLedgerOnCurrentFrontier :
  Pareto.onParetoFrontier? acquisitionPortfolio compensationLedgerCell ≡ true
compensationLedgerOnCurrentFrontier = refl

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

currentFrontierIsCorpusCompensationDistribution :
  empiricalAcquisitionFrontier
  ≡ primaryCorpusCell ∷ compensationLedgerCell ∷ distributionalIncidenceCell ∷ []
currentFrontierIsCorpusCompensationDistribution = refl

------------------------------------------------------------------------
-- Link routing cells back to the typed empirical programme leaves.
------------------------------------------------------------------------

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
    currentFrontierHasMultipleRoutesIsTrue :
      currentFrontierHasMultipleRoutes ≡ true
    frontierMembershipPaysHistoricalClaim : Bool
    frontierMembershipPaysHistoricalClaimIsFalse :
      frontierMembershipPaysHistoricalClaim ≡ false
    offFrontierDeletesRequirement : Bool
    offFrontierDeletesRequirementIsFalse :
      offFrontierDeletesRequirement ≡ false
    costGainCalibrationIsTruthScore : Bool
    costGainCalibrationIsTruthScoreIsFalse :
      costGainCalibrationIsTruthScore ≡ false
    causalIdentificationStillRequired : Bool
    causalIdentificationStillRequiredIsTrue :
      causalIdentificationStillRequired ≡ true

canonicalPowersEmpiricalAcquisitionParetoBoundary :
  PowersEmpiricalAcquisitionParetoBoundary
canonicalPowersEmpiricalAcquisitionParetoBoundary =
  powers-empirical-acquisition-pareto-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
