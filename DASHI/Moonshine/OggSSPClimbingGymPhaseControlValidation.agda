module DASHI.Moonshine.OggSSPClimbingGymPhaseControlValidation where

open import DASHI.Core.Prelude

import DASHI.Moonshine.OggSSPClimbingGymPhaseControlExact as Phase

------------------------------------------------------------------------
-- TDD regression contract for the phase-sensitive finite control.
------------------------------------------------------------------------

balancedAssignmentCountIs15504 : Phase.balancedAssignmentCount ≡ 15504
balancedAssignmentCountIs15504 = refl

energyLowerOrEqualCountIs3459 : Phase.energyLowerOrEqualCount ≡ 3459
energyLowerOrEqualCountIs3459 = refl

coherenceUpperOrEqualCountIs541 : Phase.coherenceUpperOrEqualCount ≡ 541
coherenceUpperOrEqualCountIs541 = refl

energyDiagnosticIsNotTailExtreme :
  Phase.energyStatisticMonsterSpecific
    Phase.canonicalClimbingGymPhaseControlBoundary
  ≡ false
energyDiagnosticIsNotTailExtreme = refl

coherenceTailRemainsExploratory :
  Phase.meanVectorCoherencePromotedConfirmatory
    Phase.canonicalClimbingGymPhaseControlBoundary
  ≡ false
coherenceTailRemainsExploratory = refl

multipleStatisticSelectionIsExplicit :
  Phase.multipleStatisticSelectionWarning
    Phase.canonicalClimbingGymPhaseControlBoundary
  ≡ true
multipleStatisticSelectionIsExplicit = refl
