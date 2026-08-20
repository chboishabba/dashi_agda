module DASHI.Cognition.PNF.TypedEventuallyConsistentFibreSystemRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Cognition.PNF.TypedEventuallyConsistentFibreSystemExact

data TwoFibre : Set where
  leftFibre : TwoFibre
  rightFibre : TwoFibre

unitJoin : JoinLaws ⊤
unitJoin = record
  { merge = λ _ _ → tt
  ; mergeIdempotent = λ _ → refl
  ; mergeCommutative = λ _ _ → refl
  ; mergeAssociative = λ _ _ _ → refl
  }

commutingUnitDynamics : TypedFibreDynamics TwoFibre ⊤ ⊤
commutingUnitDynamics = record
  { advance = λ _ _ → tt
  ; interaction = λ _ _ → commuteMode
  ; joins = unitJoin
  ; braidResidual = λ _ _ _ → tt
  ; reconcileBraid = λ _ _ _ _ → tt
  ; independentCommutes = λ _ _ _ _ → refl
  ; joinReconciliationExact = λ _ _ _ ()
  }

unitBatch : CertifiedCommutingBatch ⊤ commutingUnitDynamics
unitBatch = record
  { member = λ _ _ → ⊤
  ; membersCommute = λ _ _ _ _ _ → refl
  }

batchReorderingRegression :
  advance commutingUnitDynamics leftFibre
    (advance commutingUnitDynamics rightFibre tt)
  ≡
  advance commutingUnitDynamics rightFibre
    (advance commutingUnitDynamics leftFibre tt)
batchReorderingRegression =
  certifiedBatchPairReorders
    commutingUnitDynamics
    unitBatch
    tt
    leftFibre
    rightFibre
    tt
    tt
    tt

unitConvergence : FairConvergenceCertificate ⊤ commutingUnitDynamics
unitConvergence = record
  { initial = tt
  ; target = tt
  ; evaluate = λ _ _ → tt
  ; Fair = λ _ → ⊤
  ; targetLocallyStable = λ _ → refl
  ; fairSchedulesConverge = λ _ _ → refl
  }

fairConvergenceRegression :
  evaluate unitConvergence (initial unitConvergence) tt ≡ target unitConvergence
fairConvergenceRegression =
  fairScheduleReachesFixedPoint commutingUnitDynamics unitConvergence tt tt
