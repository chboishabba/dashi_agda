module DASHI.Physics.CFD.BoundedDefectSparseTwistOperator where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.CFD.SparseTwistLESOperator as Exact

------------------------------------------------------------------------
-- Bounded-defect replacement for the exact commuting square.
------------------------------------------------------------------------

record ErrorGeometry (State : Set) : Set₁ where
  field
    Within : Nat → State → State → Set
    within-refl : ∀ x → Within zero x x
    within-compose :
      ∀ {e f x y z} →
      Within e x y →
      Within f y z →
      Within (e + f) x z

open ErrorGeometry public

------------------------------------------------------------------------
-- Approximate learned proxy operator.
--
-- `oneStepDefect` is the concrete commutation-defect obligation.
-- `fullStepStable` is the Lipschitz/stability obligation needed to propagate
-- that defect.  Neither field is inferred from a runtime plot.
------------------------------------------------------------------------

record BoundedDefectProxyOperator
  (C : Exact.LosslessStructuralCodec)
  (G : ErrorGeometry (Exact.FullState C)) : Set₁ where
  field
    fullStep : Exact.FullState C → Exact.FullState C
    proxyStep : Exact.ProxyState C → Exact.ProxyState C

    oneStepError : Nat
    stabilityFactor : Nat

    oneStepDefect :
      ∀ p →
      Within G oneStepError
        (Exact.decode C (proxyStep p))
        (fullStep (Exact.decode C p))

    fullStepStable :
      ∀ {e x y} →
      Within G e x y →
      Within G (stabilityFactor * e) (fullStep x) (fullStep y)

open BoundedDefectProxyOperator public

------------------------------------------------------------------------
-- Recursive finite-horizon bound.
--
-- Bound(0) = 0
-- Bound(n+1) = epsilon + L * Bound(n)
------------------------------------------------------------------------

rolloutBound : Nat → Nat → Nat → Nat
rolloutBound epsilon L zero = zero
rolloutBound epsilon L (suc n) = epsilon + L * rolloutBound epsilon L n

bounded-proxy-rollout :
  ∀ (C : Exact.LosslessStructuralCodec)
    (G : ErrorGeometry (Exact.FullState C))
    (O : BoundedDefectProxyOperator C G)
    n p →
  Within G (rolloutBound (oneStepError O) (stabilityFactor O) n)
    (Exact.decode C (Exact.iterate n (proxyStep O) p))
    (Exact.iterate n (fullStep O) (Exact.decode C p))
bounded-proxy-rollout C G O zero p = within-refl G (Exact.decode C p)
bounded-proxy-rollout C G O (suc n) p =
  within-compose G
    (oneStepDefect O (Exact.iterate n (proxyStep O) p))
    (fullStepStable O (bounded-proxy-rollout C G O n p))

bounded-encoded-rollout :
  ∀ (C : Exact.LosslessStructuralCodec)
    (G : ErrorGeometry (Exact.FullState C))
    (O : BoundedDefectProxyOperator C G)
    n x →
  Within G (rolloutBound (oneStepError O) (stabilityFactor O) n)
    (Exact.decode C (Exact.iterate n (proxyStep O) (Exact.encode C x)))
    (Exact.iterate n (fullStep O) x)
bounded-encoded-rollout C G O n x
  rewrite Exact.decode-encode C x =
  bounded-proxy-rollout C G O n (Exact.encode C x)

------------------------------------------------------------------------
-- Runtime-facing atom receipt.
--
-- The Python vertical slice reports several inequivalent defect observables.
-- They are kept separate rather than collapsed into one uncalibrated scalar.
------------------------------------------------------------------------

record VortexAtomDefectSample : Set where
  constructor vortexAtomDefect
  field
    rolloutIndex : Nat
    atomCount : Nat
    relativeL2Milli : Nat
    correlationMilli : Nat
    circulationErrorMicro : Nat
    enstrophyErrorMicro : Nat
    signedSupportIoUMilli : Nat

open VortexAtomDefectSample public

record VortexAtomRuntimeReceipt : Setω where
  field
    extractorDeterministic : Bool
    signedAtomsCarried : Bool
    twistTransportImplemented : Bool
    periodicBoundaryExplicit : Bool
    genealogyRecorded : Bool
    mdlEventLedgerRecorded : Bool
    oneStepDefectRecorded : Bool
    finiteRolloutDefectRecorded : Bool

    cpuFloat64ReceiptAuthority : Bool
    truthNotUsedDuringProxyStep : Bool

    samples : List VortexAtomDefectSample
    statement : String
    boundary : String

open VortexAtomRuntimeReceipt public

canonicalVortexAtomRuntimeBoundary : String
canonicalVortexAtomRuntimeBoundary =
  "The vortex-atom probe is a deterministic CPU-float64 bounded-fidelity runtime surface. It does not prove a uniform atom frame bound, a continuum commuting square, asymptotic speedup, Navier--Stokes closure, regularity, or Clay authority."

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record BoundedDefectSparseTwistBoundary : Set where
  field
    exactCommutationReplacedByExplicitDefect : Bool
    finiteHorizonPropagationRequiresStability : Bool
    atomGeometryMustBeCarriedForVortexIdentity : Bool
    empiricalReceiptIsContinuumTheorem : Bool
    navierStokesClosureProved : Bool
    clayPromotionAvailable : Bool

canonicalBoundedDefectBoundary : BoundedDefectSparseTwistBoundary
canonicalBoundedDefectBoundary = record
  { exactCommutationReplacedByExplicitDefect = true
  ; finiteHorizonPropagationRequiresStability = true
  ; atomGeometryMustBeCarriedForVortexIdentity = true
  ; empiricalReceiptIsContinuumTheorem = false
  ; navierStokesClosureProved = false
  ; clayPromotionAvailable = false
  }
