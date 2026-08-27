module DASHI.Governance.WaringProductionBoundaryNonfactorabilityExact where

open import DASHI.Core.Prelude
import DASHI.Core.MeasurementBoundaryNonfactorabilityExact as Measurement
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- WARING: COUNTED ECONOMIC VALUE != MATERIAL PROVISIONING CONTRIBUTION
--
-- Source calibration:
-- Marilyn Waring, If Women Counted: A New Feminist Economics, Harper & Row,
-- 1988, ISBN 9780062509338.
-- Corroborating reassessment: Caroline Saunders & Paul Dalziel,
-- Feminist Economics 23(2), DOI 10.1080/13545701.2016.1178854.
--
-- The finite witness is DASHI-owned.  It represents the source-level critique
-- that unpaid household/care work can be excluded by a production-accounting
-- boundary while remaining materially relevant to social provisioning.  It does
-- not encode a dollar valuation of unpaid work or claim an exact historical SNA
-- numerical estimate.
------------------------------------------------------------------------

data Activity : Set where
  absentActivity unpaidCareActivity : Activity

data AccountStatus : Set where
  outsideCoreProductionBoundary : AccountStatus

data ProvisioningContribution : Set where
  noProvisioningContribution careProvisioningContribution : ProvisioningContribution

accountObserver : Activity → AccountStatus
accountObserver _ = outsideCoreProductionBoundary

provisioningContribution : Activity → ProvisioningContribution
provisioningContribution absentActivity = noProvisioningContribution
provisioningContribution unpaidCareActivity = careProvisioningContribution

waringBoundary :
  Measurement.MeasurementBoundary Activity AccountStatus ProvisioningContribution
waringBoundary = Measurement.measurementBoundary accountObserver provisioningContribution

unpaidCareBoundaryLoss : Measurement.BoundaryLossWitness waringBoundary
unpaidCareBoundaryLoss =
  Measurement.boundaryLossWitness
    absentActivity unpaidCareActivity refl (λ ())

provisioningDoesNotDescendThroughAccountingBoundary :
  Consumer.FactorsThrough accountObserver provisioningContribution → ⊥
provisioningDoesNotDescendThroughAccountingBoundary =
  Measurement.boundaryLossBlocksFactorization unpaidCareBoundaryLoss

source : Sources.SourceReference
source = Sources.waring1988

corroboratingSource : Sources.SourceReference
corroboratingSource = Sources.saundersDalziel2017

record WaringProductionBoundary : Set where
  constructor waringProductionBoundary
  field
    notCountedMeansNoProvisioningContribution : Bool
    notCountedMeansNoProvisioningContributionIsFalse :
      notCountedMeansNoProvisioningContribution ≡ false
    accountingBoundaryIsNeutralFactIndependentOfConvention : Bool
    accountingBoundaryIsNeutralFactIndependentOfConventionIsFalse :
      accountingBoundaryIsNeutralFactIndependentOfConvention ≡ false
    finiteWitnessIsDollarEstimateOfUnpaidCare : Bool
    finiteWitnessIsDollarEstimateOfUnpaidCareIsFalse :
      finiteWitnessIsDollarEstimateOfUnpaidCare ≡ false

canonicalWaringProductionBoundary : WaringProductionBoundary
canonicalWaringProductionBoundary =
  waringProductionBoundary false refl false refl false refl
