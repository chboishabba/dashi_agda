module DASHI.Law.SecurityBroadeningCrossPollinationValidation where

open import DASHI.Core.Prelude

import DASHI.Law.SecurityThreatSemanticBroadeningTopologyExact as Broadening
import DASHI.Law.SecurityBroadeningFascismAmalekMaboCrossPollinationExact as Cross

collectiveJumpCalibrationOwned :
  Broadening.collectiveJumpStatus Broadening.canonicalCollectiveBroadeningPath
  ≡ Broadening.collectiveJumpObserved
collectiveJumpCalibrationOwned = refl

onePersonThreatDoesNotJustifyWholeAssemblyThreat :
  Broadening.onePersonThreatJustifiesWholeAssemblyThreat
    Broadening.canonicalBroadeningBoundary ≡ false
onePersonThreatDoesNotJustifyWholeAssemblyThreat = refl

repeatedCopiesDoNotJustifyBroadening :
  Broadening.repeatedCopiesJustifyScopeBroadening
    Broadening.canonicalBroadeningBoundary ≡ false
repeatedCopiesDoNotJustifyBroadening = refl

broadeningDoesNotProveMotive :
  Broadening.semanticBroadeningProvesIdeologicalMotive
    Broadening.canonicalBroadeningBoundary ≡ false
broadeningDoesNotProveMotive = refl

modernAmalekRoleDoesNotProveCollectivePropagation :
  Cross.modernRoleBindingProvesCollectivePropagation
    Cross.canonicalAmalekBroadeningBoundary ≡ false
modernAmalekRoleDoesNotProveCollectivePropagation = refl

broaderCrowdLabelDoesNotExhaustCountry :
  Cross.broaderCrowdLabelExhaustsCountryAuthority
    Cross.canonicalMaboBroadeningBoundary ≡ false
broaderCrowdLabelDoesNotExhaustCountry = refl

broadeningFeedsCollectiveGuiltAuditOnly :
  Cross.broadeningMayFeedCollectiveGuiltAudit
    Cross.canonicalCrossPollinationBoundary ≡ true
broadeningFeedsCollectiveGuiltAuditOnly = refl
