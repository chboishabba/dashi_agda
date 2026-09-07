module DASHI.Core.TrajectoryRecoveryFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.TrajectoryResidueExact as Residue

------------------------------------------------------------------------
-- TRAJECTORY / RECOVERY FIBRE
--
-- Generic owner for systems where two states may share a recovered coarse
-- endpoint while differing in retained path residue, recovery state, reachable
-- future or incidence.  This extends the existing trajectory-residue theorem
-- without identifying any particular domain semantics.
------------------------------------------------------------------------

record TrajectoryRecoveryFibre : Set₁ where
  field
    State : Set
    CoarseEndpoint : Set
    RecoveryState : Set
    FutureCone : Set

    endpointOf : State → CoarseEndpoint
    residueOf : State → Residue.ResidueFlag
    recoveryOf : State → RecoveryState
    futureOf : State → FutureCone

    recoveryReading : String

open TrajectoryRecoveryFibre public

record SameEndpointDifferentRecovery
    (fibre : TrajectoryRecoveryFibre) : Set where
  field
    leftState rightState : State fibre
    sameEndpoint : endpointOf fibre leftState ≡ endpointOf fibre rightState
    recoveryDiffers :
      recoveryOf fibre leftState ≡ recoveryOf fibre rightState → ⊥

open SameEndpointDifferentRecovery public

recoveryNonFactorability :
  ∀ {fibre : TrajectoryRecoveryFibre} →
  SameEndpointDifferentRecovery fibre →
  NF.NonFactorabilityWitness
    (endpointOf fibre)
    (recoveryOf fibre)
recoveryNonFactorability witness =
  NF.nonFactorabilityWitness
    (leftState witness)
    (rightState witness)
    (sameEndpoint witness)
    (recoveryDiffers witness)

endpointOnlyRecoveryDecoderImpossible :
  ∀ {fibre : TrajectoryRecoveryFibre} →
  SameEndpointDifferentRecovery fibre →
  NF.FactorsThrough
    (endpointOf fibre)
    (recoveryOf fibre) →
  ⊥
endpointOnlyRecoveryDecoderImpossible witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (recoveryNonFactorability witness)

record SameEndpointDifferentFuture
    (fibre : TrajectoryRecoveryFibre) : Set where
  field
    futureLeft futureRight : State fibre
    futureSameEndpoint :
      endpointOf fibre futureLeft ≡ endpointOf fibre futureRight
    futureDiffers :
      futureOf fibre futureLeft ≡ futureOf fibre futureRight → ⊥

open SameEndpointDifferentFuture public

futureNonFactorability :
  ∀ {fibre : TrajectoryRecoveryFibre} →
  SameEndpointDifferentFuture fibre →
  NF.NonFactorabilityWitness
    (endpointOf fibre)
    (futureOf fibre)
futureNonFactorability witness =
  NF.nonFactorabilityWitness
    (futureLeft witness)
    (futureRight witness)
    (futureSameEndpoint witness)
    (futureDiffers witness)

record RecoveryRequiresIndependentWitness
    (fibre : TrajectoryRecoveryFibre) : Set₁ where
  field
    TargetRecovery : State fibre → Set
    targetRecovery : ∀ state → TargetRecovery state
    recoveryReceiptReference : String

open RecoveryRequiresIndependentWitness public

------------------------------------------------------------------------
-- Finite fixture: same restored endpoint, retained residue and different
-- recovery/future.
------------------------------------------------------------------------

data DemoState : Set where
  original restoredWithoutResidue restoredWithResidue : DemoState

data DemoEndpoint : Set where sameEndpoint : DemoEndpoint
data DemoRecovery : Set where recovered impaired : DemoRecovery
data DemoFuture : Set where broadFuture constrainedFuture : DemoFuture

demoFibre : TrajectoryRecoveryFibre
demoFibre = record
  { State = DemoState
  ; CoarseEndpoint = DemoEndpoint
  ; RecoveryState = DemoRecovery
  ; FutureCone = DemoFuture
  ; endpointOf = λ _ → sameEndpoint
  ; residueOf = λ
      { original → Residue.residueAbsent
      ; restoredWithoutResidue → Residue.residueAbsent
      ; restoredWithResidue → Residue.residuePresent
      }
  ; recoveryOf = λ
      { original → recovered
      ; restoredWithoutResidue → recovered
      ; restoredWithResidue → impaired
      }
  ; futureOf = λ
      { original → broadFuture
      ; restoredWithoutResidue → broadFuture
      ; restoredWithResidue → constrainedFuture
      }
  ; recoveryReading = "Equal restored coarse endpoints may retain path residue and differ in recovery state or future cone."
  }

demoRecoveryWitness : SameEndpointDifferentRecovery demoFibre
demoRecoveryWitness = record
  { leftState = restoredWithoutResidue
  ; rightState = restoredWithResidue
  ; sameEndpoint = refl
  ; recoveryDiffers = λ ()
  }

demoFutureWitness : SameEndpointDifferentFuture demoFibre
demoFutureWitness = record
  { futureLeft = restoredWithoutResidue
  ; futureRight = restoredWithResidue
  ; futureSameEndpoint = refl
  ; futureDiffers = λ ()
  }

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data RestoredEndpointImpliesRecoveredStatePermission : Set where

data RestoredEndpointImpliesResidueErasedPermission : Set where

data RecoveryImpliesHistoricalLossErasedPermission : Set where

restoredEndpointDoesNotAutoPromoteToRecoveredState :
  RestoredEndpointImpliesRecoveredStatePermission → ⊥
restoredEndpointDoesNotAutoPromoteToRecoveredState ()

restoredEndpointDoesNotAutoPromoteToResidueErased :
  RestoredEndpointImpliesResidueErasedPermission → ⊥
restoredEndpointDoesNotAutoPromoteToResidueErased ()

recoveryDoesNotAutoPromoteToHistoricalLossErased :
  RecoveryImpliesHistoricalLossErasedPermission → ⊥
recoveryDoesNotAutoPromoteToHistoricalLossErased ()
