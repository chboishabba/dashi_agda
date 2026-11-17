module DASHI.Cognition.USInstitutionalCaptureVerificationRisk20261013Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- US institutional capture / verification-risk context.
--
-- These facts alter how much independent corroboration is rationally demanded;
-- they do not invert every federal statement into falsehood.
------------------------------------------------------------------------

record VerificationRiskBoundary : Set where
  constructor verification-risk-boundary
  field
    trumpDismissedComeyPaid : Bool
    currentFBIDirectorTrumpAppointeePaid : Bool
    currentSCOTUSSixThreeConservativePaid : Bool
    project2025PersonnelImplementationPaid : Bool
    civilServiceProtectionReductionPaid : Bool
    institutionalEnvironmentCanAffectVerificationRisk : Bool
    captureRiskProvesSpecificFindingFalse : Bool
    politicalAppointmentMakesAllAgencyWorkInvalid : Bool
    strongerIndependentCorroborationRational : Bool
open VerificationRiskBoundary public

canonicalVerificationRiskBoundary : VerificationRiskBoundary
canonicalVerificationRiskBoundary = verification-risk-boundary
  true true true true true true false false true

record VerificationRiskReceipt : Set where
  constructor verification-risk-receipt
  field
    source : String
    boundedFinding : String
    riskContextPaid : Bool
open VerificationRiskReceipt public

fbiLeadershipReceipt : VerificationRiskReceipt
fbiLeadershipReceipt = verification-risk-receipt
  "DOJ/Comey record; Reuters 2026 FBI leadership reporting"
  "Trump dismissed FBI Director James Comey in 2017; in 2026 the FBI is led by Trump appointee Kash Patel. These are institutional-governance facts, not proof that any particular FBI evidentiary finding is false."
  true

judicialEnvironmentReceipt : VerificationRiskReceipt
judicialEnvironmentReceipt = verification-risk-receipt
  "Reuters 2026 Supreme Court reporting"
  "The US Supreme Court has a 6-3 conservative majority and has repeatedly adjudicated disputes over Trump executive authority. Ideological composition is relevant institutional context but does not predetermine every case."
  true

stateCapacityReceipt : VerificationRiskReceipt
stateCapacityReceipt = verification-risk-receipt
  "Reuters 2026 civil-service reporting; Project 2025 implementation owners"
  "The administration implemented major civil-service changes reducing protections for tens of thousands of policy-influencing employees, alongside documented Project 2025 author-to-office implementation chains. This raises institutional-independence and chilling-effect questions requiring claim-local evidence."
  true

data CaptureRiskImpliesSpecificFalsehood : Set where
data AppointmentImpliesAgencyFabrication : Set where

captureRiskDoesNotCreateSpecificFalsehood : CaptureRiskImpliesSpecificFalsehood → ⊥
captureRiskDoesNotCreateSpecificFalsehood ()

appointmentDoesNotCreateAgencyFabrication : AppointmentImpliesAgencyFabrication → ⊥
appointmentDoesNotCreateAgencyFabrication ()
