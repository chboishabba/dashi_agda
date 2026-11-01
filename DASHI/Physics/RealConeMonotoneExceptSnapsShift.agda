module DASHI.Physics.RealConeMonotoneExceptSnapsShift where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)

open import DASHI.Physics.SnapSignature as SS
open import DASHI.Physics.SnapSignatureShiftInstance as SSI
open import DASHI.Physics.MaskedConeStructure as MCS
open import Data.Vec using (Vec)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP

-- Cone monotonicity except snaps, specialized to the shift operator.
record ConeMonotoneExceptSnapsShift {m k : Nat}
  (σ : Vec IMQ.Sign (m + k))
  (cfg : SSI.SnapSignatureShift {m} {k})
  : Set₁ where
  field
    monotoneExceptSnap : ∀ x →
      MCS.Timelike σ x →
      MCS.¬_ (SS.SnapSignature.step (SSI.signature cfg) x (TCP.Tᵣ {m} {k} x)
        × SS.SnapSignature.snapZero (SSI.signature cfg) x (TCP.Tᵣ {m} {k} x)
        × SS.SnapSignature.chi2Spike (SSI.signature cfg) x (TCP.Tᵣ {m} {k} x)
        × SS.SnapSignature.mdlDescent (SSI.signature cfg) x (TCP.Tᵣ {m} {k} x)) →
      MCS.Timelike σ (TCP.Tᵣ {m} {k} x) ⊎ MCS.Null σ (TCP.Tᵣ {m} {k} x)

  coneMono : SS.ConeMonotoneExceptSnaps {S = RTC.Carrier (m + k)}
  coneMono =
    record
      { InInterior = MCS.Timelike σ
      ; Boundary = MCS.Null σ
      ; T = TCP.Tᵣ {m} {k}
      ; Sig = SSI.signature cfg
      ; monotoneExceptSnap = monotoneExceptSnap
      }

open ConeMonotoneExceptSnapsShift public
