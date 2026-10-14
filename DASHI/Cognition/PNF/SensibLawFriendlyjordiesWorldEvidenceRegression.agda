module DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact as World
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Base

cprsLegislativeOutcomePaid :
  World.cprsLegislativeOutcomePaid ≡ true
cprsLegislativeOutcomePaid = refl

cprsPartyCausalAttributionPaid :
  World.cprsPartyCausalAttributionPaid ≡ false
cprsPartyCausalAttributionPaid = refl

southAustraliaOperationalHighRenewablePaid :
  World.southAustraliaOperationalHighRenewablePaid ≡ true
southAustraliaOperationalHighRenewablePaid = refl

southAustraliaBatterySecurityRolePaid :
  World.southAustraliaBatterySecurityRolePaid ≡ true
southAustraliaBatterySecurityRolePaid = refl

southAustraliaGovernanceCausalInferencePaid :
  World.southAustraliaGovernanceCausalInferencePaid ≡ false
southAustraliaGovernanceCausalInferencePaid = refl

externalFactsCreateTransitionPremise :
  World.externalFactsCreateTransitionPremise ≡ false
externalFactsCreateTransitionPremise = refl

cprsCompilerRetainsReviewedCausalPremise :
  (admission :
    World.TransitionAdmission
      March.cprs2009
      World.cprsExternalWorldBundle) →
  Base.WorldTransitionEvidence.TransitionPremise
    (World.cprsWorldTransitionEvidenceFromAdmission admission)
  ≡ World.ReviewedCausalBridge.CausalPremise
      (World.TransitionAdmission.causalBridge admission)
cprsCompilerRetainsReviewedCausalPremise =
  World.cprsCompilerPreservesCausalPremise
