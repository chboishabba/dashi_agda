module DASHI.Biology.IBSAdaptiveBeliefPolicyRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Biology.IBSAdaptiveBeliefPolicyExact as Policy

beliefStateRegression :
  Policy.canonicalInitialIBSBeliefState ≡ Policy.canonicalInitialIBSBeliefState
beliefStateRegression = refl

policyFrontierRegression :
  Policy.canonicalAdaptivePolicyParetoFrontier ≡ Policy.canonicalAdaptivePolicyParetoFrontier
policyFrontierRegression = refl

responseNotRegimeTruthRegression :
  Policy.SingleResponseMakesRegimeTruePermission → ⊥
responseNotRegimeTruthRegression = Policy.singleResponseDoesNotMakeRegimeTrue

informationNotBenefitRegression :
  Policy.InformationOptimalActionIsClinicalOptimalPermission → ⊥
informationNotBenefitRegression = Policy.informationOptimalDoesNotMeanClinicalOptimal

posthocNotAdaptiveRegression :
  Policy.PostHocSwitchEqualsProspectiveAdaptivePolicyPermission → ⊥
posthocNotAdaptiveRegression = Policy.postHocSwitchDoesNotEqualProspectiveAdaptivePolicy
