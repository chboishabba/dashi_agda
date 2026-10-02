module DASHI.Codec.TriadicPAdicCylinderExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as PAdic

------------------------------------------------------------------------
-- Executable instance of the existing CylinderSystem contract.
--
-- Residuals are infinite low-to-high trit streams.  A depth-k cylinder keeps
-- the first k low-order trits; refinement from k+1 to k drops only the newest
-- high-order trit.

ResidualStream : Set
ResidualStream = Nat → Trit.Trit

shift : ResidualStream → ResidualStream
shift stream n = stream (suc n)

projectStream : (k : Nat) → ResidualStream → PAdic.Kernel k
projectStream zero stream = PAdic.[]ᵥ
projectStream (suc k) stream =
  stream zero PAdic.∷ᵥ projectStream k (shift stream)

refineKernel :
  (k : Nat) → PAdic.Kernel (suc k) → PAdic.Kernel k
refineKernel zero (x PAdic.∷ᵥ PAdic.[]ᵥ) = PAdic.[]ᵥ
refineKernel (suc k) (x PAdic.∷ᵥ xs) =
  x PAdic.∷ᵥ refineKernel k xs

projectCompatible :
  (k : Nat) →
  (stream : ResidualStream) →
  refineKernel k (projectStream (suc k) stream)
  ≡ projectStream k stream
projectCompatible zero stream = refl
projectCompatible (suc k) stream
  rewrite projectCompatible k (shift stream) = refl

canonicalTriadicCylinderSystem : PAdic.CylinderSystem
canonicalTriadicCylinderSystem =
  record
    { Residual = ResidualStream
    ; Cylinder = PAdic.Kernel
    ; project = projectStream
    ; refine = refineKernel
    ; project-compatible = projectCompatible
    }

record TriadicCylinderBoundary : Set where
  constructor triadicCylinderBoundary
  field
    executableCylinderInstancePaid : Bool
    cylindersKeepLowOrderPrefix : Bool
    refinementCompatibilityPaid : Bool

canonicalTriadicCylinderBoundary : TriadicCylinderBoundary
canonicalTriadicCylinderBoundary =
  triadicCylinderBoundary true true true
