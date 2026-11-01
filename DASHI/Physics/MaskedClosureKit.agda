module DASHI.Physics.MaskedClosureKit where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec)
open import Data.Integer using (ℤ)

open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.RealClosureKitFiber as RKF
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM
open import DASHI.Physics.DimensionBoundAssumptions as DBA

------------------------------------------------------------------------
-- Masked quadratic invariants wired onto a RealClosureKitFiber instance.
--
-- This does not change the underlying closure kit; it augments it with:
--   - a mask on the core,
--   - the masked quadratic Qσ and bilinear B₂σ pulled back to the full state,
--   - a signature extracted from the mask,
--   - an orbit-profile seam (dimension bound target).

record RealClosureKitFiberMask : Set₁ where
  field
    m k : Nat
    base : RKF.RealClosureKitFiber

    -- Mask on the core (length m).
    mask : Vec IMQ.Sign m

    -- Core-only invariants, lifted to the full state via coarseOf.
    coreQσ : RTC.Carrier (m + k) → ℤ
    coreB2σ : RTC.Carrier (m + k) → RTC.Carrier (m + k) → ℤ

    -- Signature extracted from the mask.
    sig : Nat × Nat

    -- Orbit-profile seam (dimension-bound target).
    orbitProfile : DBA.ShellOrbitProfile m

open RealClosureKitFiberMask public

------------------------------------------------------------------------
-- Constructor: derive all fields from base + mask.

mkMaskKit :
  ∀ {m k : Nat} →
  RKF.RealClosureKitFiber →
  Vec IMQ.Sign m →
  DBA.ShellOrbitProfile m →
  RealClosureKitFiberMask
mkMaskKit {m} {k} base mask orbitProfile =
  record
    { m = m
    ; k = k
    ; base = base
    ; mask = mask
    ; coreQσ = λ x → IMQ.Qσ mask (TCP.coarseOf m k x)
    ; coreB2σ = λ x y → IMQ.B2σ mask (TCP.coarseOf m k x) (TCP.coarseOf m k y)
    ; sig = SFM.signature mask
    ; orbitProfile = orbitProfile
    }
