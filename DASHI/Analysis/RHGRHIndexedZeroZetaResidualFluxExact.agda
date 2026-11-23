module DASHI.Analysis.RHGRHIndexedZeroZetaResidualFluxExact where

-- A conservative extension of the existing indexed mode carrier:
-- k can advance and a nonzero residual can be ADDED by a source-accounted
-- transition. Never collapse sign, zero observation or phase at a zero.
--
-- Exact finite mathematical donor: SmithFilsingerTimeIndexedTransferExact
-- uses separately accounted sources, losses and stored remainders. This
-- module merely reuses that accounting discipline, not its physical claims.
--
-- The original Alpoge TLiftK IsLift witness has NOT been constructed here.
-- Cyclotomic zeta_3 is not the analytic Riemann zeta(s).
-- Agda source written; kernel check and genuine Hecke source weld OPEN.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (trans; cong)
import DASHI.Analysis.RHGRHIndexedZeroZetaPhaseResidualWeldExact as P

private
  module Frame = P.IndexedZeroPhaseFrame

-- The index and residual are Nat for this exact, subtraction-free
-- accumulation model. Sign remains a separate, explicit field rather
-- than being reconstructed from a net cancellation.
FrameAt : Set
FrameAt = P.IndexedZeroPhaseFrame Nat Bool Nat

-- Source flux is NOT assumed zero. Mode and sign remain intact.
appendResidualFlux : Nat → FrameAt → FrameAt
appendResidualFlux delta (P.indexedZeroPhaseFrame k m s r z) =
  P.indexedZeroPhaseFrame (suc k) m s (r + delta) z

appendResidualFluxIndex :
  (delta : Nat) (f : FrameAt) →
  Frame.index (appendResidualFlux delta f) ≡ suc (Frame.index f)
appendResidualFluxIndex delta (P.indexedZeroPhaseFrame k m s r z) = refl

appendResidualFluxSign :
  (delta : Nat) (f : FrameAt) →
  Frame.sign (appendResidualFlux delta f) ≡ Frame.sign f
appendResidualFluxSign delta (P.indexedZeroPhaseFrame k m s r z) = refl

appendResidualFluxMode :
  (delta : Nat) (f : FrameAt) →
  Frame.mode (appendResidualFlux delta f) ≡ Frame.mode f
appendResidualFluxMode delta (P.indexedZeroPhaseFrame k m s r z) = refl

appendResidualFluxObservation :
  (delta : Nat) (f : FrameAt) →
  Frame.observedZero (appendResidualFlux delta f)
    ≡ Frame.observedZero f
appendResidualFluxObservation delta (P.indexedZeroPhaseFrame k m s r z) = refl

appendResidualFluxLedger :
  (delta : Nat) (f : FrameAt) →
  Frame.residual (appendResidualFlux delta f)
    ≡ Frame.residual f + delta
appendResidualFluxLedger delta (P.indexedZeroPhaseFrame k m s r z) = refl

-- TRUE 1-step commuting square with nonzero residual change:
-- the same delta is carried through phase conjugation.
appendResidualFluxReflects :
  (delta : Nat) (f : FrameAt) →
  appendResidualFlux delta (P.reflectFrame f)
    ≡ P.reflectFrame (appendResidualFlux delta f)
appendResidualFluxReflects delta (P.indexedZeroPhaseFrame k m s r z) = refl

-- The source residual, not just its final numerical value, is preserved
-- in the exact order of two additions. This theorem uses two explicit
-- source increments and no inferred inverse/dissipation.
twoFluxStepsLedger :
  (first second : Nat) (f : FrameAt) →
  Frame.residual
    (appendResidualFlux second (appendResidualFlux first f))
    ≡ (Frame.residual f + first) + second
twoFluxStepsLedger first second
  (P.indexedZeroPhaseFrame k m s r z) = refl

twoFluxStepsReflect :
  (first second : Nat) (f : FrameAt) →
  appendResidualFlux second
    (appendResidualFlux first (P.reflectFrame f))
    ≡
  P.reflectFrame
    (appendResidualFlux second (appendResidualFlux first f))
twoFluxStepsReflect first second f =
  trans
    (cong (appendResidualFlux second)
      (appendResidualFluxReflects first f))
    (appendResidualFluxReflects second (appendResidualFlux first f))

-- Concrete selected frame: ζ3-mode, observed zero, signed source and
-- residual 9 is not replaced by zero after the transfer.
sampleResidualGrows :
  Frame.residual
    (appendResidualFlux 4 P.balancedObservedZeroWithZeta)
    ≡ 13
sampleResidualGrows = refl

sampleStillZeta :
  Frame.mode (appendResidualFlux 4 P.balancedObservedZeroWithZeta)
    ≡ P.zetaMode
sampleStillZeta = refl

sampleStillObservedZero :
  Frame.observedZero
    (appendResidualFlux 4 P.balancedObservedZeroWithZeta)
    ≡ Frame.observedZero P.balancedObservedZeroWithZeta
sampleStillObservedZero = refl
