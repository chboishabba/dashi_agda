module DASHI.Law.SensibLawBrightonS185ApplicabilityEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BRIGHTON s 185(3)(a): APPLICABILITY / CONTINUING-TENANCY SOURCE RECEIPTS
--
-- Private Form 18a carrier reviewed from connected source:
--   premises: 17 Gordon St, Brighton QLD 4017
--   general tenancy agreement
--   fixed term: 9 August 2022 to 8 February 2023
--
-- Therefore 24 January 2023 lies within the stated fixed term.
-- The carrier is not a moveable-dwelling-site agreement of the kind excluded by
-- s 185(1).  These receipts do not establish objective unfitness or breach.
------------------------------------------------------------------------

data BrightonTenancyContinuing24Jan2023 : Set where
  form18a-fixed-term-contains-24jan2023 : BrightonTenancyContinuing24Jan2023

data BrightonS185Applies24Jan2023 : Set where
  form18a-general-tenancy-s185-applies : BrightonS185Applies24Jan2023

brightonTenancyContinuing24Jan2023 : BrightonTenancyContinuing24Jan2023
brightonTenancyContinuing24Jan2023 = form18a-fixed-term-contains-24jan2023

brightonS185Applies24Jan2023 : BrightonS185Applies24Jan2023
brightonS185Applies24Jan2023 = form18a-general-tenancy-s185-applies

record BrightonS185ApplicabilityEvidence : Set where
  constructor brighton-s185-applicability-evidence
  field
    exactPremisesPinned : Bool
    generalTenancyForm18aPinned : Bool
    fixedTermStartPinned : Bool
    fixedTermEndPinned : Bool
    evaluationDatePinned : Bool
    evaluationDateInsideStatedFixedTerm : Bool
    moveableDwellingSiteExclusionEngaged : Bool
    continuingTenancyCoordinatePaid : Bool
    subsection185AppliesCoordinatePaid : Bool
    objectiveUnfitnessPaid : Bool
    subsection3aNonPerformancePaid : Bool
    privateRawLeasePublished : Bool
    receiptReference : String

canonicalBrightonS185ApplicabilityEvidence : BrightonS185ApplicabilityEvidence
canonicalBrightonS185ApplicabilityEvidence =
  brighton-s185-applicability-evidence
    true true true true true true
    false
    true true
    false false false
    "private Form 18a source receipt: fixed term 2022-08-09 to 2023-02-08; evaluation 2023-01-24"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ContinuingTenancyAutomaticallyProvesUnfitness : Set where
data ApplicabilityAutomaticallyProvesViolation : Set where

continuingTenancyDoesNotProveUnfitness :
  ContinuingTenancyAutomaticallyProvesUnfitness → ⊥
continuingTenancyDoesNotProveUnfitness ()

applicabilityDoesNotProveViolation :
  ApplicabilityAutomaticallyProvesViolation → ⊥
applicabilityDoesNotProveViolation ()
