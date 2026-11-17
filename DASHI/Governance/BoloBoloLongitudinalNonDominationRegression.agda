module DASHI.Governance.BoloBoloLongitudinalNonDominationRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloLongitudinalNonDominationExact as Joint

costWinDoesNotPayNonDomination :
  Joint.longRunCoordinationAdvantageAutomaticallyPaysNonDomination
    Joint.canonicalLongitudinalNonDominationBoundary ≡ false
costWinDoesNotPayNonDomination = refl

nonDominationDoesNotPayCostWin :
  Joint.nonDominationAutomaticallyPaysCoordinationAdvantage
    Joint.canonicalLongitudinalNonDominationBoundary ≡ false
nonDominationDoesNotPayCostWin = refl

sameTargetRequired :
  Joint.sameTargetBindingRequired
    Joint.canonicalLongitudinalNonDominationBoundary ≡ true
sameTargetRequired = refl

realizedControlAuditRequired :
  Joint.realizedControlAuditRequired
    Joint.canonicalLongitudinalNonDominationBoundary ≡ true
realizedControlAuditRequired = refl

labelsDoNotPay :
  Joint.horizontalOrAnarchistLabelPaysNonDomination
    Joint.canonicalLongitudinalNonDominationBoundary ≡ false
labelsDoNotPay = refl

politicalSuperiorityNotCreated :
  Joint.jointCoordinationAndNonDominationProvesOverallPoliticalSuperiority
    Joint.canonicalLongitudinalNonDominationBoundary ≡ false
politicalSuperiorityNotCreated = refl
