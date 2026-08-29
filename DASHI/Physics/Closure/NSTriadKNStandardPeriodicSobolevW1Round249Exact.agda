module DASHI.Physics.Closure.NSTriadKNStandardPeriodicSobolevW1Round249Exact where

------------------------------------------------------------------------
-- ROUND249 / STANDARD PERIODIC SOBOLEV + HOLDER AUTHORITY FOR W1
--
-- The repo-specific normalized-curl geometry is already closed by R246/R247.
-- R248 reduces W1 to three standard analytic inequalities on T^3:
--
--   ||H u x u||_2^2 <= ||H u||_6^2 ||u||_3^2,
--   ||u||_3^2       <= C_(1/2) A,
--   ||H u||_6^2     <= C_1 D.
--
-- This file gives those three theorems one source-bound authority surface and
-- compiles it directly into the exact R248 endpoint.  It deliberately does
-- not claim the Agda standard library itself proves periodic Sobolev theory;
-- an analytic model must supply this standard theorem package.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNMixedHelicitySobolevEndpointRound248Exact as R248

record StandardPeriodicW1Authority
    (Time : Set)
    (mixedMass criticalSize dissipationDensity : Nat → Time → ℚ)
    : Set₁ where
  field
    huL6Squared uL3Squared : Nat → Time → ℚ
    halfEmbeddingConstant oneEmbeddingConstant : ℚ

    mixedMassNN : (N : Nat) (t : Time) → 0ℚ ≤ mixedMass N t
    huL6SquaredNN : (N : Nat) (t : Time) → 0ℚ ≤ huL6Squared N t
    uL3SquaredNN : (N : Nat) (t : Time) → 0ℚ ≤ uL3Squared N t
    criticalSizeNN : (N : Nat) (t : Time) → 0ℚ ≤ criticalSize N t
    dissipationDensityNN : (N : Nat) (t : Time) → 0ℚ ≤ dissipationDensity N t
    halfEmbeddingConstantNN : 0ℚ ≤ halfEmbeddingConstant
    oneEmbeddingConstantNN : 0ℚ ≤ oneEmbeddingConstant

    holderSquared :
      (N : Nat) (t : Time) →
      mixedMass N t ≤ huL6Squared N t * uL3Squared N t

    halfSobolevSquared :
      (N : Nat) (t : Time) →
      uL3Squared N t ≤ halfEmbeddingConstant * criticalSize N t

    oneSobolevSquaredAfterR247Isometry :
      (N : Nat) (t : Time) →
      huL6Squared N t ≤ oneEmbeddingConstant * dissipationDensity N t

open StandardPeriodicW1Authority public

endpointAt :
  ∀ {Time mixedMass criticalSize dissipationDensity}
    (A : StandardPeriodicW1Authority Time mixedMass criticalSize dissipationDensity)
    (N : Nat) (t : Time) →
  R248.SobolevMixedHelicityEndpoint
endpointAt A N t = record
  { R248.mixedMass = mixedMass N t
  ; R248.huL6Squared = huL6Squared A N t
  ; R248.uL3Squared = uL3Squared A N t
  ; R248.criticalSize = criticalSize N t
  ; R248.dissipationDensity = dissipationDensity N t
  ; R248.halfEmbeddingConstant = halfEmbeddingConstant A
  ; R248.oneEmbeddingConstant = oneEmbeddingConstant A
  ; R248.mixedMassNN = mixedMassNN A N t
  ; R248.huL6SquaredNN = huL6SquaredNN A N t
  ; R248.uL3SquaredNN = uL3SquaredNN A N t
  ; R248.criticalSizeNN = criticalSizeNN A N t
  ; R248.dissipationDensityNN = dissipationDensityNN A N t
  ; R248.halfEmbeddingConstantNN = halfEmbeddingConstantNN A
  ; R248.oneEmbeddingConstantNN = oneEmbeddingConstantNN A
  ; R248.holderSquared = holderSquared A N t
  ; R248.halfSobolevSquared = halfSobolevSquared A N t
  ; R248.oneSobolevAfterNormalizedCurlIsometry =
      oneSobolevSquaredAfterR247Isometry A N t
  }

standardPeriodicW1PointwiseBound :
  ∀ {Time mixedMass criticalSize dissipationDensity}
    (A : StandardPeriodicW1Authority Time mixedMass criticalSize dissipationDensity)
    (N : Nat) (t : Time) →
  mixedMass N t
  ≤ (oneEmbeddingConstant A * halfEmbeddingConstant A)
      * criticalSize N t * dissipationDensity N t
standardPeriodicW1PointwiseBound A N t =
  R248.sobolevMixedHelicityPointwiseBound (endpointAt A N t)

round249R247NormalizedCurlGeometryReused : Bool
round249R247NormalizedCurlGeometryReused = true

round249StandardPeriodicW1AuthoritySurfaceClosed : Bool
round249StandardPeriodicW1AuthoritySurfaceClosed = true

round249W1PointwiseCompilerClosed : Bool
round249W1PointwiseCompilerClosed = true

round249ContinuumSobolevTheoremsKernelDerivedHere : Bool
round249ContinuumSobolevTheoremsKernelDerivedHere = false

round249PackageAClosed : Bool
round249PackageAClosed = false

round249ClayPromotion : Bool
round249ClayPromotion = false

round249StandardPeriodicW1AuthoritySurfaceClosedIsTrue :
  round249StandardPeriodicW1AuthoritySurfaceClosed ≡ true
round249StandardPeriodicW1AuthoritySurfaceClosedIsTrue = refl

round249W1PointwiseCompilerClosedIsTrue :
  round249W1PointwiseCompilerClosed ≡ true
round249W1PointwiseCompilerClosedIsTrue = refl

round249ContinuumSobolevTheoremsKernelDerivedHereIsFalse :
  round249ContinuumSobolevTheoremsKernelDerivedHere ≡ false
round249ContinuumSobolevTheoremsKernelDerivedHereIsFalse = refl

round249ClayPromotionIsFalse : round249ClayPromotion ≡ false
round249ClayPromotionIsFalse = refl
