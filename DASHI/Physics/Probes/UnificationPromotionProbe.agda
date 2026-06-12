module DASHI.Physics.Probes.UnificationPromotionProbe where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.MarginInvariantProgrammeFrontierReceipt as Frontier
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as NS
import DASHI.Physics.Closure.Paper0SharedMarginDependencyReceipt as Paper0
import DASHI.Physics.Closure.PublishableFullUnificationStackReceipt as Root
import DASHI.Physics.Closure.UnifiedMarginInvariantReceipt as Unified

record UnificationPromotionContract : Set where
  field
    paper0LaneSpecificAnalyticsProvided :
      Paper0.laneSpecificAnalyticsProvided
        (Root.paper0DependencyReceipt
          Root.canonicalPublishableFullUnificationStackReceipt)
      ≡ true

    nsMovingCutoffTheoremProved :
      NS.movingCutoffTheoremProvedHere
        (Root.nsReceipt Root.canonicalPublishableFullUnificationStackReceipt)
      ≡ true

    unifiedAnalyticInhabitantsProved :
      Unified.analyticInhabitantsProved
        (Root.unifiedReceipt Root.canonicalPublishableFullUnificationStackReceipt)
      ≡ true

    frontierThetaClosed :
      Frontier.thetaTailMarginLessThanOneProved
        (Root.frontierReceipt Root.canonicalPublishableFullUnificationStackReceipt)
      ≡ true

    fullUnificationClosureClaimed :
      Root.fullUnificationClosureClaimed
        Root.canonicalPublishableFullUnificationStackReceipt
      ≡ true

    clayPromotionClaimed :
      Root.clayPromotionClaimed
        Root.canonicalPublishableFullUnificationStackReceipt
      ≡ true

unificationPromotionProbe : UnificationPromotionContract
unificationPromotionProbe =
  record
    { paper0LaneSpecificAnalyticsProvided = refl
    ; nsMovingCutoffTheoremProved = refl
    ; unifiedAnalyticInhabitantsProved = refl
    ; frontierThetaClosed = refl
    ; fullUnificationClosureClaimed = refl
    ; clayPromotionClaimed = refl
    }
