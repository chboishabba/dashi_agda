{-# OPTIONS --safe #-}
module DASHI.Unified.TOECurrentMaxCutGovernanceFleetRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.TOECurrentMaxCutGovernanceFleetExact as Cut

gate4TargetRemains58 :
  Cut.targetFormalGapCount ≡ 58
gate4TargetRemains58 = Cut.targetFormalGapCountIs58

dischargedFleetFibresRemainExcluded :
  Cut.dischargedFleetFibresExcluded ≡ true
dischargedFleetFibresRemainExcluded = refl

fleetPriorityDoesNotCreateProof :
  Cut.fleetPriorityCreatesProof ≡ false
fleetPriorityDoesNotCreateProof = refl

candidateLegalSourceDoesNotCreateAuthority :
  Cut.candidateLegalSourceCreatesAuthority ≡ false
candidateLegalSourceDoesNotCreateAuthority = refl

legalAuthorityDoesNotCreateApplicability :
  Cut.legalAuthorityCreatesApplicability ≡ false
legalAuthorityDoesNotCreateApplicability = refl

formalGovernanceDoesNotCreatePoliticalLegitimacy :
  Cut.formalGovernanceCreatesPoliticalLegitimacy ≡ false
formalGovernanceDoesNotCreatePoliticalLegitimacy = refl

finiteRGDoesNotCreateContinuumPromotion :
  Cut.finiteRGCreatesContinuumPromotion ≡ false
finiteRGDoesNotCreateContinuumPromotion = refl

ibrahimSearchPriorityDoesNotCreateRecognition :
  Cut.ibrahimPriorityCreatesRecognition ≡ false
ibrahimSearchPriorityDoesNotCreateRecognition = refl

esdRemainsReadOnly :
  Cut.esdSurfaceEdited ≡ false
esdRemainsReadOnly = refl
