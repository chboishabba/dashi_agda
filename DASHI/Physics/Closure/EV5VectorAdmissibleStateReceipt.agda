module DASHI.Physics.Closure.EV5VectorAdmissibleStateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; _*_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
import Data.Vec.Base as Vec

import DASHI.Combinatorics.FractranCOL as FractranCOL
import DASHI.Physics.Closure.NSToEV5ForwardSimulationReceipt as Forward
import DASHI.Physics.Closure.NSToEV5ProjectionFrontierReceipt as Frontier

------------------------------------------------------------------------
-- Vector-valued NS/EV5 admissible-state receipt.
--
-- This receipt records the finite EV5 vector admissibility surface needed by
-- the NS-facing closure programme.  It explicitly rejects scalar additive
-- Lyapunov promotion, keeps v7 as the dissipation witness lane, bounds v2 by
-- the viscosity-dependent cascade cutoff K*(nu), and splits the remaining
-- quotient/forward-simulation obligations into tail preservation and shell
-- boundedness.  It is a carrier receipt only: it does not prove an
-- NS-to-EV5 transfer theorem, continuum regularity, or any Clay
-- Navier-Stokes claim.

lane2 :
  FractranCOL.EV5 →
  Nat
lane2 ev =
  FractranCOL.get ev 0

lane7 :
  FractranCOL.EV5 →
  Nat
lane7 ev =
  FractranCOL.get ev 3

zeroEV5 :
  FractranCOL.EV5
zeroEV5 =
  Vec._∷_
    zero
    (Vec._∷_
      zero
      (Vec._∷_
        zero
        (Vec._∷_
          zero
          (Vec._∷_
            zero
            Vec.[]))))

data EV5VectorAdmissibilityStatus : Set where
  vectorCarrierAdmissible_scalarAdditiveLyapunovRejected_transferOpen :
    EV5VectorAdmissibilityStatus

data VectorAdmissibilityComponent : Set where
  ev5VectorState :
    VectorAdmissibilityComponent

  scalarAdditiveLyapunovRejected :
    VectorAdmissibilityComponent

  lane7DissipationNonIncreasingComponent :
    VectorAdmissibilityComponent

  lane2CascadeCutoffBoundedByKStarNu :
    VectorAdmissibilityComponent

  forwardSimulationTailPreservationObligation :
    VectorAdmissibilityComponent

  forwardSimulationShellBoundednessObligation :
    VectorAdmissibilityComponent

  quotientTailPreservationObligation :
    VectorAdmissibilityComponent

  quotientShellBoundednessObligation :
    VectorAdmissibilityComponent

canonicalVectorAdmissibilityComponents :
  List VectorAdmissibilityComponent
canonicalVectorAdmissibilityComponents =
  ev5VectorState
  ∷ scalarAdditiveLyapunovRejected
  ∷ lane7DissipationNonIncreasingComponent
  ∷ lane2CascadeCutoffBoundedByKStarNu
  ∷ forwardSimulationTailPreservationObligation
  ∷ forwardSimulationShellBoundednessObligation
  ∷ quotientTailPreservationObligation
  ∷ quotientShellBoundednessObligation
  ∷ []

data ScalarLyapunovPromotion : Set where

scalarLyapunovPromotionImpossibleHere :
  ScalarLyapunovPromotion →
  ⊥
scalarLyapunovPromotionImpossibleHere ()

record Lane7DissipationWitness
    (before after : FractranCOL.EV5) : Set where
  field
    lane7NonIncreasing :
      lane7 after ≤ lane7 before

open Lane7DissipationWitness public

canonicalLane7DissipationWitness :
  ∀ ev →
  Lane7DissipationWitness ev ev
canonicalLane7DissipationWitness ev =
  record
    { lane7NonIncreasing =
        ≤-refl
    }

record CascadeTerminationWitness
    (K*nu : Nat)
    (state : FractranCOL.EV5) : Set where
  field
    lane2BoundedByKStarNu :
      lane2 state ≤ K*nu

open CascadeTerminationWitness public

canonicalZeroCascadeTerminationWitness :
  ∀ K*nu →
  CascadeTerminationWitness K*nu zeroEV5
canonicalZeroCascadeTerminationWitness K*nu =
  record
    { lane2BoundedByKStarNu =
        z≤n
    }

record TailPreservationObligation (before after : FractranCOL.EV5) : Set where
  field
    tailLanePreservedOrDecreased :
      lane7 after ≤ lane7 before

open TailPreservationObligation public

record ShellBoundednessObligation
    (K*nu : Nat)
    (state : FractranCOL.EV5) : Set where
  field
    shellLaneBelowCutoff :
      lane2 state ≤ K*nu

open ShellBoundednessObligation public

canonicalTailPreservationObligation :
  ∀ ev →
  TailPreservationObligation ev ev
canonicalTailPreservationObligation ev =
  record
    { tailLanePreservedOrDecreased =
        ≤-refl
    }

canonicalZeroShellBoundednessObligation :
  ∀ K*nu →
  ShellBoundednessObligation K*nu zeroEV5
canonicalZeroShellBoundednessObligation K*nu =
  record
    { shellLaneBelowCutoff =
        z≤n
    }

quotientForwardObligations :
  ∀ K*nu before after →
  TailPreservationObligation before after →
  ShellBoundednessObligation K*nu after →
  Set
quotientForwardObligations K*nu before after tail shell =
  lane7 after ≤ lane7 before
  ×
  lane2 after ≤ K*nu

scalarLyapunovRejectionStatement :
  String
scalarLyapunovRejectionStatement =
  "Scalar additive Lyapunov promotion is rejected: admissibility is vector-valued over EV5 and uses separated lane witnesses, not one additive scalar energy including diagnostic lanes."

dissipationWitnessStatement :
  String
dissipationWitnessStatement =
  "Dissipation witness: lane7 is required to be non-increasing across the admissible EV5 transition surface."

cascadeTerminationStatement :
  String
cascadeTerminationStatement =
  "Cascade termination witness: lane2 shell depth is bounded by the viscosity-dependent cutoff K*(nu)."

splitObligationStatement :
  String
splitObligationStatement =
  "Forward-simulation and quotient obligations are split into tail preservation and shell boundedness; this receipt records the split obligations and does not close the NS transfer theorem."

record EV5VectorAdmissibleStateReceipt
    (nu K : Nat)
    (before after : FractranCOL.EV5) : Set₁ where
  field
    status :
      EV5VectorAdmissibilityStatus

    statusIsVectorCarrierOnly :
      status
      ≡
      vectorCarrierAdmissible_scalarAdditiveLyapunovRejected_transferOpen

    kStarNu :
      Nat

    kStarNuIsProduct :
      kStarNu ≡ K * nu

    vectorStateBefore :
      FractranCOL.EV5

    vectorStateBeforeIsParameter :
      vectorStateBefore ≡ before

    vectorStateAfter :
      FractranCOL.EV5

    vectorStateAfterIsParameter :
      vectorStateAfter ≡ after

    scalarAdditiveLyapunovAccepted :
      Bool

    scalarAdditiveLyapunovAcceptedIsFalse :
      scalarAdditiveLyapunovAccepted ≡ false

    scalarAdditiveLyapunovRejectedHere :
      Bool

    scalarAdditiveLyapunovRejectedHereIsTrue :
      scalarAdditiveLyapunovRejectedHere ≡ true

    lane7Dissipation :
      Lane7DissipationWitness before after

    lane7DissipationNonIncreasing :
      lane7 after ≤ lane7 before

    lane7DissipationMatchesWitness :
      lane7DissipationNonIncreasing
      ≡
      Lane7DissipationWitness.lane7NonIncreasing lane7Dissipation

    cascadeTermination :
      CascadeTerminationWitness kStarNu after

    lane2BoundedByKStarNu :
      lane2 after ≤ kStarNu

    lane2BoundMatchesWitness :
      lane2BoundedByKStarNu
      ≡
      CascadeTerminationWitness.lane2BoundedByKStarNu cascadeTermination

    forwardSimulationTailPreservation :
      TailPreservationObligation before after

    forwardSimulationShellBoundedness :
      ShellBoundednessObligation kStarNu after

    quotientTailPreservation :
      TailPreservationObligation before after

    quotientShellBoundedness :
      ShellBoundednessObligation kStarNu after

    forwardSimulationSplitObligations :
      quotientForwardObligations
        kStarNu
        before
        after
        forwardSimulationTailPreservation
        forwardSimulationShellBoundedness

    quotientSplitObligations :
      quotientForwardObligations
        kStarNu
        before
        after
        quotientTailPreservation
        quotientShellBoundedness

    frontierReceipt :
      Frontier.NSToEV5ProjectionFrontierReceipt

    frontierReceiptIsCanonical :
      frontierReceipt ≡ Frontier.canonicalNSToEV5ProjectionFrontierReceipt

    frontierForwardSimulationOpen :
      Frontier.forwardSimulationProvedHere frontierReceipt ≡ false

    frontierQuotientCorrectnessOpen :
      Frontier.quotientCorrectnessProvedHere frontierReceipt ≡ false

    frontierLyapunovPreservationOpen :
      Frontier.lyapunovPreservationAgainstKStarNuProvedHere
        frontierReceipt
      ≡
      false

    forwardReceipt :
      Forward.NSToEV5ForwardSimulationReceipt nu K

    forwardReceiptIsCanonical :
      forwardReceipt ≡ Forward.canonicalNSToEV5ForwardSimulationReceipt nu K

    forwardSimulationTheoremStillOpen :
      Forward.forwardSimulationTheoremProved forwardReceipt ≡ false

    quotientCorrectnessStillOpen :
      Forward.quotientCorrectnessProved forwardReceipt ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    components :
      List VectorAdmissibilityComponent

    componentsAreCanonical :
      components ≡ canonicalVectorAdmissibilityComponents

    scalarLyapunovBoundary :
      String

    scalarLyapunovBoundaryIsCanonical :
      scalarLyapunovBoundary ≡ scalarLyapunovRejectionStatement

    dissipationBoundary :
      String

    dissipationBoundaryIsCanonical :
      dissipationBoundary ≡ dissipationWitnessStatement

    cascadeBoundary :
      String

    cascadeBoundaryIsCanonical :
      cascadeBoundary ≡ cascadeTerminationStatement

    splitObligationBoundary :
      String

    splitObligationBoundaryIsCanonical :
      splitObligationBoundary ≡ splitObligationStatement

    scalarLyapunovPromotionFlags :
      List ScalarLyapunovPromotion

    scalarLyapunovPromotionFlagsAreEmpty :
      scalarLyapunovPromotionFlags ≡ []

open EV5VectorAdmissibleStateReceipt public

canonicalZeroEV5VectorAdmissibleStateReceipt :
  ∀ (nu K : Nat) →
  EV5VectorAdmissibleStateReceipt nu K zeroEV5 zeroEV5
canonicalZeroEV5VectorAdmissibleStateReceipt nu K =
  record
    { status =
        vectorCarrierAdmissible_scalarAdditiveLyapunovRejected_transferOpen
    ; statusIsVectorCarrierOnly =
        refl
    ; kStarNu =
        K * nu
    ; kStarNuIsProduct =
        refl
    ; vectorStateBefore =
        zeroEV5
    ; vectorStateBeforeIsParameter =
        refl
    ; vectorStateAfter =
        zeroEV5
    ; vectorStateAfterIsParameter =
        refl
    ; scalarAdditiveLyapunovAccepted =
        false
    ; scalarAdditiveLyapunovAcceptedIsFalse =
        refl
    ; scalarAdditiveLyapunovRejectedHere =
        true
    ; scalarAdditiveLyapunovRejectedHereIsTrue =
        refl
    ; lane7Dissipation =
        canonicalLane7DissipationWitness zeroEV5
    ; lane7DissipationNonIncreasing =
        z≤n
    ; lane7DissipationMatchesWitness =
        refl
    ; cascadeTermination =
        canonicalZeroCascadeTerminationWitness (K * nu)
    ; lane2BoundedByKStarNu =
        z≤n
    ; lane2BoundMatchesWitness =
        refl
    ; forwardSimulationTailPreservation =
        canonicalTailPreservationObligation zeroEV5
    ; forwardSimulationShellBoundedness =
        canonicalZeroShellBoundednessObligation (K * nu)
    ; quotientTailPreservation =
        canonicalTailPreservationObligation zeroEV5
    ; quotientShellBoundedness =
        canonicalZeroShellBoundednessObligation (K * nu)
    ; forwardSimulationSplitObligations =
        z≤n , z≤n
    ; quotientSplitObligations =
        z≤n , z≤n
    ; frontierReceipt =
        Frontier.canonicalNSToEV5ProjectionFrontierReceipt
    ; frontierReceiptIsCanonical =
        refl
    ; frontierForwardSimulationOpen =
        refl
    ; frontierQuotientCorrectnessOpen =
        refl
    ; frontierLyapunovPreservationOpen =
        refl
    ; forwardReceipt =
        Forward.canonicalNSToEV5ForwardSimulationReceipt nu K
    ; forwardReceiptIsCanonical =
        refl
    ; forwardSimulationTheoremStillOpen =
        refl
    ; quotientCorrectnessStillOpen =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; components =
        canonicalVectorAdmissibilityComponents
    ; componentsAreCanonical =
        refl
    ; scalarLyapunovBoundary =
        scalarLyapunovRejectionStatement
    ; scalarLyapunovBoundaryIsCanonical =
        refl
    ; dissipationBoundary =
        dissipationWitnessStatement
    ; dissipationBoundaryIsCanonical =
        refl
    ; cascadeBoundary =
        cascadeTerminationStatement
    ; cascadeBoundaryIsCanonical =
        refl
    ; splitObligationBoundary =
        splitObligationStatement
    ; splitObligationBoundaryIsCanonical =
        refl
    ; scalarLyapunovPromotionFlags =
        []
    ; scalarLyapunovPromotionFlagsAreEmpty =
        refl
    }

ev5VectorAdmissibleStateNoScalarLyapunovPromotion :
  ∀ (nu K : Nat) →
  scalarAdditiveLyapunovAccepted
    (canonicalZeroEV5VectorAdmissibleStateReceipt nu K)
  ≡
  false
ev5VectorAdmissibleStateNoScalarLyapunovPromotion nu K =
  refl

ev5VectorAdmissibleStateNoClayPromotion :
  ∀ (nu K : Nat) →
  clayNavierStokesPromoted
    (canonicalZeroEV5VectorAdmissibleStateReceipt nu K)
  ≡
  false
ev5VectorAdmissibleStateNoClayPromotion nu K =
  refl
