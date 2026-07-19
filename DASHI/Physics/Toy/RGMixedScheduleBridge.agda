module DASHI.Physics.Toy.RGMixedScheduleBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Properties as NatP using (≤-trans)

import DASHI.Physics.Toy.ScalarContinuum as SC
open import DASHI.Physics.Toy.RGUniversality

-- Spatial decimation at one shell boundary.
rgCoarse : ∀ n → RGState (Nat.suc n) → RGState n
rgCoarse n (mkRGState r i) = mkRGState r (SC.dropLast i)

-- The Wilsonian mixed step: decimate, then evolve the retained shell.
rgRenormalizeStep : ∀ n → RGState (Nat.suc n) → RGState n
rgRenormalizeStep n x = rgShellStep n (rgCoarse n x)

-- The competing schedule: evolve the fine shell, then decimate.
rgEvolveThenCoarse : ∀ n → RGState (Nat.suc n) → RGState n
rgEvolveThenCoarse n x = rgCoarse n (rgShellStep (Nat.suc n) x)

rgBasinLabel : ∀ {n} → RGState n → Agda.Builtin.Bool.Bool
rgBasinLabel = relevantMode

-- Strict state commutation is not claimed.  The relevant/macroscopic basin is
-- exactly schedule invariant because neither shell relaxation nor decimation
-- changes the relevant coordinate.
rgMixedScheduleBasinInvariant :
  ∀ n (x : RGState (Nat.suc n)) →
  rgBasinLabel (rgRenormalizeStep n x) ≡
  rgBasinLabel (rgEvolveThenCoarse n x)
rgMixedScheduleBasinInvariant n (mkRGState r i) = refl

-- The irrelevant defect contracts under the Wilsonian mixed step.
rgRenormalizeDefectContracts :
  ∀ n (x : RGState (Nat.suc n)) →
  SC.countNonZero (irrelevantMode (rgRenormalizeStep n x)) ≤
  SC.countNonZero (irrelevantMode x)
rgRenormalizeDefectContracts n (mkRGState r i) =
  NatP.≤-trans
    (SC.scalarDefectMonotone n {SC.dropLast i})
    (SC.countNonZero-dropLast i)

record RGMixedScheduleCertificate (n : Nat) : Set where
  field
    basin-invariant :
      ∀ x →
      rgBasinLabel (rgRenormalizeStep n x) ≡
      rgBasinLabel (rgEvolveThenCoarse n x)
    defect-contracts :
      ∀ x →
      SC.countNonZero (irrelevantMode (rgRenormalizeStep n x)) ≤
      SC.countNonZero (irrelevantMode x)

rgMixedScheduleCertificate : ∀ n → RGMixedScheduleCertificate n
rgMixedScheduleCertificate n = record
  { basin-invariant = rgMixedScheduleBasinInvariant n
  ; defect-contracts = rgRenormalizeDefectContracts n
  }
