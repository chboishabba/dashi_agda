module DASHI.Governance.DrugGovernanceErrorAsymmetryOptionConeExact where

open import DASHI.Core.Prelude

import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Governance.DrugGovernanceErrorAsymmetryBurdenAllocationExact as Burden

------------------------------------------------------------------------
-- ERROR-SPECIFIC OPTION CONES
--
-- Each error family can contract a different reachable-option coordinate.
-- These finite witnesses establish geometry only; they do not assert real-world
-- rates, magnitudes, or causal prevalence.
------------------------------------------------------------------------

data ErrorWorld : Set where
  baselineWorld
  punitiveErrorWorld
  careDenialWorld
  authorityCaptureWorld
  commercialCaptureWorld
  sovereigntyOverrideWorld
  : ErrorWorld

data GovernanceOption : Set where
  futureHelpSeeking
  careAccess
  categoryContest
  fairBenefitClaim
  sovereignCeremonialGovernance
  ordinarySafetySupport
  : GovernanceOption

data Available : ErrorWorld → GovernanceOption → Set where
  baselineHelp : Available baselineWorld futureHelpSeeking
  baselineCare : Available baselineWorld careAccess
  baselineContest : Available baselineWorld categoryContest
  baselineBenefit : Available baselineWorld fairBenefitClaim
  baselineSovereignty : Available baselineWorld sovereignCeremonialGovernance
  baselineSafety : Available baselineWorld ordinarySafetySupport

  punitiveSafety : Available punitiveErrorWorld ordinarySafetySupport

  careDeniedHelp : Available careDenialWorld futureHelpSeeking
  careDeniedContest : Available careDenialWorld categoryContest
  careDeniedBenefit : Available careDenialWorld fairBenefitClaim
  careDeniedSovereignty : Available careDenialWorld sovereignCeremonialGovernance
  careDeniedSafety : Available careDenialWorld ordinarySafetySupport

  authorityHelp : Available authorityCaptureWorld futureHelpSeeking
  authorityCare : Available authorityCaptureWorld careAccess
  authorityBenefit : Available authorityCaptureWorld fairBenefitClaim
  authoritySovereignty : Available authorityCaptureWorld sovereignCeremonialGovernance
  authoritySafety : Available authorityCaptureWorld ordinarySafetySupport

  commercialHelp : Available commercialCaptureWorld futureHelpSeeking
  commercialCare : Available commercialCaptureWorld careAccess
  commercialContest : Available commercialCaptureWorld categoryContest
  commercialSovereignty : Available commercialCaptureWorld sovereignCeremonialGovernance
  commercialSafety : Available commercialCaptureWorld ordinarySafetySupport

  sovereigntyHelp : Available sovereigntyOverrideWorld futureHelpSeeking
  sovereigntyCare : Available sovereigntyOverrideWorld careAccess
  sovereigntyContest : Available sovereigntyOverrideWorld categoryContest
  sovereigntyBenefit : Available sovereigntyOverrideWorld fairBenefitClaim
  sovereigntySafety : Available sovereigntyOverrideWorld ordinarySafetySupport

reachability : Cone.SafeReachabilitySystem ErrorWorld GovernanceOption
reachability = Cone.safeReachabilitySystem Available

baselineIncludes :
  (world : ErrorWorld) →
  (option : GovernanceOption) →
  Available world option →
  Available baselineWorld option
baselineIncludes punitiveErrorWorld ordinarySafetySupport punitiveSafety = baselineSafety
baselineIncludes careDenialWorld futureHelpSeeking careDeniedHelp = baselineHelp
baselineIncludes careDenialWorld categoryContest careDeniedContest = baselineContest
baselineIncludes careDenialWorld fairBenefitClaim careDeniedBenefit = baselineBenefit
baselineIncludes careDenialWorld sovereignCeremonialGovernance careDeniedSovereignty = baselineSovereignty
baselineIncludes careDenialWorld ordinarySafetySupport careDeniedSafety = baselineSafety
baselineIncludes authorityCaptureWorld futureHelpSeeking authorityHelp = baselineHelp
baselineIncludes authorityCaptureWorld careAccess authorityCare = baselineCare
baselineIncludes authorityCaptureWorld fairBenefitClaim authorityBenefit = baselineBenefit
baselineIncludes authorityCaptureWorld sovereignCeremonialGovernance authoritySovereignty = baselineSovereignty
baselineIncludes authorityCaptureWorld ordinarySafetySupport authoritySafety = baselineSafety
baselineIncludes commercialCaptureWorld futureHelpSeeking commercialHelp = baselineHelp
baselineIncludes commercialCaptureWorld careAccess commercialCare = baselineCare
baselineIncludes commercialCaptureWorld categoryContest commercialContest = baselineContest
baselineIncludes commercialCaptureWorld sovereignCeremonialGovernance commercialSovereignty = baselineSovereignty
baselineIncludes commercialCaptureWorld ordinarySafetySupport commercialSafety = baselineSafety
baselineIncludes sovereigntyOverrideWorld futureHelpSeeking sovereigntyHelp = baselineHelp
baselineIncludes sovereigntyOverrideWorld careAccess sovereigntyCare = baselineCare
baselineIncludes sovereigntyOverrideWorld categoryContest sovereigntyContest = baselineContest
baselineIncludes sovereigntyOverrideWorld fairBenefitClaim sovereigntyBenefit = baselineBenefit
baselineIncludes sovereigntyOverrideWorld ordinarySafetySupport sovereigntySafety = baselineSafety

punitiveLosesHelp : Available punitiveErrorWorld futureHelpSeeking → ⊥
punitiveLosesHelp ()
careDenialLosesCare : Available careDenialWorld careAccess → ⊥
careDenialLosesCare ()
authorityCaptureLosesContest : Available authorityCaptureWorld categoryContest → ⊥
authorityCaptureLosesContest ()
commercialCaptureLosesBenefit : Available commercialCaptureWorld fairBenefitClaim → ⊥
commercialCaptureLosesBenefit ()
sovereigntyOverrideLosesGovernance :
  Available sovereigntyOverrideWorld sovereignCeremonialGovernance → ⊥
sovereigntyOverrideLosesGovernance ()

punitiveErrorContractsHelpSeeking :
  Cone.StrictSafeReachabilityContraction reachability baselineWorld punitiveErrorWorld
punitiveErrorContractsHelpSeeking =
  Cone.strictSafeReachabilityContraction
    (baselineIncludes punitiveErrorWorld)
    futureHelpSeeking baselineHelp punitiveLosesHelp

careDenialContractsCare :
  Cone.StrictSafeReachabilityContraction reachability baselineWorld careDenialWorld
careDenialContractsCare =
  Cone.strictSafeReachabilityContraction
    (baselineIncludes careDenialWorld)
    careAccess baselineCare careDenialLosesCare

authorityCaptureContractsContest :
  Cone.StrictSafeReachabilityContraction reachability baselineWorld authorityCaptureWorld
authorityCaptureContractsContest =
  Cone.strictSafeReachabilityContraction
    (baselineIncludes authorityCaptureWorld)
    categoryContest baselineContest authorityCaptureLosesContest

commercialCaptureContractsBenefitClaim :
  Cone.StrictSafeReachabilityContraction reachability baselineWorld commercialCaptureWorld
commercialCaptureContractsBenefitClaim =
  Cone.strictSafeReachabilityContraction
    (baselineIncludes commercialCaptureWorld)
    fairBenefitClaim baselineBenefit commercialCaptureLosesBenefit

sovereigntyOverrideContractsGovernance :
  Cone.StrictSafeReachabilityContraction reachability baselineWorld sovereigntyOverrideWorld
sovereigntyOverrideContractsGovernance =
  Cone.strictSafeReachabilityContraction
    (baselineIncludes sovereigntyOverrideWorld)
    sovereignCeremonialGovernance
    baselineSovereignty
    sovereigntyOverrideLosesGovernance

errorWorld : Burden.ClassificationErrorKind → ErrorWorld
errorWorld Burden.wrongfulPunitiveClassification = punitiveErrorWorld
errorWorld Burden.wrongfulCareDenial = careDenialWorld
errorWorld Burden.wrongfulAuthorityAttribution = authorityCaptureWorld
errorWorld Burden.wrongfulCommercialLegitimacy = commercialCaptureWorld
errorWorld Burden.wrongfulSovereigntyOverride = sovereigntyOverrideWorld

record ErrorAsymmetryOptionConeBoundary : Set where
  constructor errorAsymmetryOptionConeBoundary
  field
    distinctErrorsCanLoseDistinctOptions : Bool
    distinctErrorsCanLoseDistinctOptionsIsTrue :
      distinctErrorsCanLoseDistinctOptions ≡ true
    punitiveErrorCanLoseHelpSeeking : Bool
    punitiveErrorCanLoseHelpSeekingIsTrue : punitiveErrorCanLoseHelpSeeking ≡ true
    careDenialCanLoseCareAccess : Bool
    careDenialCanLoseCareAccessIsTrue : careDenialCanLoseCareAccess ≡ true
    authorityCaptureCanLoseCategoryContest : Bool
    authorityCaptureCanLoseCategoryContestIsTrue : authorityCaptureCanLoseCategoryContest ≡ true
    commercialCaptureCanLoseBenefitClaim : Bool
    commercialCaptureCanLoseBenefitClaimIsTrue : commercialCaptureCanLoseBenefitClaim ≡ true
    sovereigntyOverrideCanLoseCeremonialGovernance : Bool
    sovereigntyOverrideCanLoseCeremonialGovernanceIsTrue :
      sovereigntyOverrideCanLoseCeremonialGovernance ≡ true

canonicalErrorAsymmetryOptionConeBoundary : ErrorAsymmetryOptionConeBoundary
canonicalErrorAsymmetryOptionConeBoundary =
  errorAsymmetryOptionConeBoundary
    true refl true refl true refl true refl true refl true refl
