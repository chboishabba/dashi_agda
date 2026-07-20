module DASHI.Algebra.FiniteQuaternionStrictCover where

import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8
open import DASHI.Unified.GRQuantumProofTerms
open import DASHI.Unified.GRQuantumStrictProofTerms

------------------------------------------------------------------------
-- Strict preimage-producing wrapper around the exact Q8 -> V4 cover.

exactPreimage :
  (rotation : Q8.V4Rotation) → Preimage Q8.rho rotation
exactPreimage rotation
  with Q8.rhoSurjective rotation
... | Q8.rotation-preimage element maps = preimage element maps

fiberAgrees :
  (rotation : Q8.V4Rotation) →
  Q8.rho (TwoElementFiber.first (Q8.rhoFiberIsTwoElement rotation))
  ≡ rotation
fiberAgrees rotation =
  TwoElementFiber.firstMaps (Q8.rhoFiberIsTwoElement rotation)

finiteQuaternionStrictSpinCover : StrictSpinDoubleCoverProof
finiteQuaternionStrictSpinCover =
  record
    { base = Q8.finiteQuaternionSpinCover
    ; exactSurjectivity = exactPreimage
    ; fiberProofAgreesWithSurjectivity = fiberAgrees
    }
