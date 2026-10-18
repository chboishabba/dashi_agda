module DASHI.Law.GenericReviewedDeltaCampaignKernelRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.GenericReviewedDeltaCampaignKernelExact as Kernel

boundary : Kernel.GenericReviewedDeltaCampaignKernelBoundary
boundary = Kernel.canonicalGenericReviewedDeltaCampaignKernelBoundary

recomputesResiduals :
  Kernel.kernelOwnsResidualRecomputation boundary ≡ true
recomputesResiduals =
  Kernel.kernelOwnsResidualRecomputationIsTrue boundary

selectsFreshDemand :
  Kernel.kernelMaySelectFreshDemand boundary ≡ true
selectsFreshDemand =
  Kernel.kernelMaySelectFreshDemandIsTrue boundary

reviewedDeltaOnly :
  Kernel.kernelAcceptsOnlyReviewedDeltaInterface boundary ≡ true
reviewedDeltaOnly =
  Kernel.kernelAcceptsOnlyReviewedDeltaInterfaceIsTrue boundary

rawSourceCannotPromote :
  Kernel.kernelMayConvertRawSourceIntoReviewedDelta boundary ≡ false
rawSourceCannotPromote =
  Kernel.kernelMayConvertRawSourceIntoReviewedDeltaIsFalse boundary

domainReviewCannotBeBypassed :
  Kernel.kernelMayBypassDomainReview boundary ≡ false
domainReviewCannotBeBypassed =
  Kernel.kernelMayBypassDomainReviewIsFalse boundary

kernelIsNotContractSpecific :
  Kernel.kernelRequiresContractDoctrine boundary ≡ false
kernelIsNotContractSpecific =
  Kernel.kernelRequiresContractDoctrineIsFalse boundary
