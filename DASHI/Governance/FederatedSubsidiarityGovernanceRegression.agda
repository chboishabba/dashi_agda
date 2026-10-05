module DASHI.Governance.FederatedSubsidiarityGovernanceRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.FederatedSubsidiarityGovernanceExact as F

------------------------------------------------------------------------
-- Regression surface for the generic structural theorems.
------------------------------------------------------------------------

nonMemberLocalParticipationIsImpossible :
  ∀ {ℓ} {A C I : Set} →
  (g : F.FederatedGovernance A C I) →
  (s : F.SubsidiarityWitness g) →
  ∀ {a c i} →
  ¬ F.memberOf g a c →
  F.scopeOf g i ≡ F.localTo c →
  F.participates g a i →
  ⊥
nonMemberLocalParticipationIsImpossible =
  F.nonMemberCannotParticipateLocal

federatedLoadThreeFive :
  F.federatedLoad 3 5 ≡ 8
federatedLoadThreeFive = refl

federatedLoadThreeFiveUpperBound :
  F.federatedLoad 3 5 ≤ 3 + 5
federatedLoadThreeFiveUpperBound =
  F.federatedLoadUpperBound 3 5

oneTransitionIsReachable :
  ∀ {S : Set} →
  (ts : F.TransitionSystem S) →
  ∀ {x y} →
  F._↝_ ts x y →
  F.Reachable ts x y
oneTransitionIsReachable =
  F.reachableStep

formalModelDoesNotCreateLegitimacy :
  F.formalModelCreatesLegitimacy F.canonicalFederatedGovernanceBoundary ≡ false
formalModelDoesNotCreateLegitimacy = refl

decentralisationSuperiorityNotProved :
  F.decentralisationEmpiricallySuperior F.canonicalFederatedGovernanceBoundary ≡ false
decentralisationSuperiorityNotProved = refl

ecologicalViabilityNotInferredFromGovernanceForm :
  F.governanceFormImpliesEcologicalViability F.canonicalFederatedGovernanceBoundary ≡ false
ecologicalViabilityNotInferredFromGovernanceForm = refl
