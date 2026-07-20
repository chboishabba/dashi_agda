module DASHI.Physics.Closure.FiniteRegionalSpectrumBoundary where

open import DASHI.Unified.GRQuantumProofTerms
import DASHI.Physics.Closure.FiniteRegionalSpectrum as UV

------------------------------------------------------------------------
-- Fail-closed theorem: the regulated finite surface cannot be promoted to the
-- full UV closure while its physical low-energy-match proposition is empty.

regulatedUVClosedImpossible :
  UVSpectralClosed UV.regulatedUVSurface → ⊥
regulatedUVClosedImpossible closed
  with UVSpectralClosed.lowEnergyLimitMatchesRequiredPhysicsProof closed
... | ()
