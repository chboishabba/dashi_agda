{-# OPTIONS --safe #-}
module DASHI.Arithmetic.TwinPrimeTernarySignedShellHistoryBidiExact where

-- Retain BOTH the signed shell value and balanced-ternary orientation.
-- The sign is an observation, never a replacement for the real value.
-- Reuses the original wave Trit and the original exact Nat-period BIDI.
-- Source-written; kernel typecheck pending.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Physics.WaveAlgorithmLift as Wave
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period

record TernarySignedShell : Set₁ where
  field
    Scalar : Set
    value : Nat → Scalar
    orientation : Nat → Wave.Trit
open TernarySignedShell public

signedShellState : (C : TernarySignedShell) → Nat →
  Scalar C × Wave.Trit
signedShellState C n = value C n , orientation C n

retainedSignedShellState : (C : TernarySignedShell) →
  Period.NatPeriod270 → Scalar C × Wave.Trit
retainedSignedShellState C =
  Bidi.liftNatConsumer (signedShellState C)

signedShellStateForward :
  (C : TernarySignedShell) (n : Nat) →
  retainedSignedShellState C (Period.encodeNatPeriod270 n)
    ≡ signedShellState C n
signedShellStateForward C = Bidi.liftConsumerSound (signedShellState C)

signedShellStateBackward :
  (C : TernarySignedShell) (code : Period.NatPeriod270) →
  signedShellState C (Period.decodeNatPeriod270 code)
    ≡ retainedSignedShellState C code
signedShellStateBackward C = Bidi.liftConsumerComplete (signedShellState C)

retainedOrientation :
  (C : TernarySignedShell) → Period.NatPeriod270 → Wave.Trit
retainedOrientation C code = proj₂ (retainedSignedShellState C code)

orientationForward :
  (C : TernarySignedShell) (n : Nat) →
  retainedOrientation C (Period.encodeNatPeriod270 n)
    ≡ orientation C n
orientationForward C n =
  cong proj₂ (signedShellStateForward C n)
