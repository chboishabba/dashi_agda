module DASHI.Education.DigitalESDICTLifecycleCircularitySnowballRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT

l1410MethodPaidRegression :
  ICT.ICTLifecycleCircularityAcquisition.ictLCAMethodSourcePaid
    ICT.canonicalICTLifecycleCircularityAcquisition
  ≡ true
l1410MethodPaidRegression = refl

l1023CircularityMethodPaidRegression :
  ICT.ICTLifecycleCircularityAcquisition.ictCircularityMethodSourcePaid
    ICT.canonicalICTLifecycleCircularityAcquisition
  ≡ true
l1023CircularityMethodPaidRegression = refl

l1410DoesNotPaySameObjectInventoryRegression :
  ICT.ICTLifecycleMethodPaysDeploymentInventory → ⊥
l1410DoesNotPaySameObjectInventoryRegression =
  ICT.ictLifecycleMethodDoesNotPayDeploymentInventory

l1023DoesNotPayDeploymentCircularityRegression :
  ICT.CircularityMethodPaysDeploymentCircularity → ⊥
l1023DoesNotPayDeploymentCircularityRegression =
  ICT.circularityMethodDoesNotPayDeploymentCircularity

methodDoesNotPayDurabilityRegression :
  ICT.CircularityMethodProvesDeploymentDurability → ⊥
methodDoesNotPayDurabilityRegression =
  ICT.circularityMethodDoesNotProveDeploymentDurability

sourceRoleRetentionRegression :
  ICT.ICTLifecycleCircularityAcquisition.sourceRolesRetained
    ICT.canonicalICTLifecycleCircularityAcquisition
  ≡ true
sourceRoleRetentionRegression = refl

citationAuthorityRegression :
  ICT.ICTLifecycleCircularityAcquisition.citationCreatesAuthority
    ICT.canonicalICTLifecycleCircularityAcquisition
  ≡ false
citationAuthorityRegression = refl

parentResidualStillUnpaidRegression :
  Acquisition.paymentState Acquisition.openInteroperabilityDurability
  ≡ Acquisition.unpaid
parentResidualStillUnpaidRegression = refl

refinedSameObjectLifecycleResidualRegression :
  ICT.refinedPaymentState ICT.deploymentSpecificLCI
  ≡ ICT.unpaidRefined
refinedSameObjectLifecycleResidualRegression = refl

refinedHardwareCircularityResidualRegression :
  ICT.refinedPaymentState ICT.deploymentHardwareCircularity
  ≡ ICT.unpaidRefined
refinedHardwareCircularityResidualRegression = refl

methodCoordinatesPaidRegression :
  ICT.refinedPaymentState ICT.ictLifecycleMethod
  ≡ ICT.sourceRolePaidRefined
methodCoordinatesPaidRegression = refl

circularityCoordinatesPaidRegression :
  ICT.refinedPaymentState ICT.ictCircularityMethod
  ≡ ICT.sourceRolePaidRefined
circularityCoordinatesPaidRegression = refl
