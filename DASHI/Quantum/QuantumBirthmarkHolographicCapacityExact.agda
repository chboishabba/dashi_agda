{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicCapacityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat using (_*_)

import DASHI.Algebra.Quantum.UVFiniteness as UV
import DASHI.Algebra.Quantum.UVFinitenessHolographyTests as HoloUV

------------------------------------------------------------------------
-- HOLOGRAPHIC AREA CAPACITY -> UV FINITENESS
--
-- This is an exact reuse theorem, not an analogy: the existing holography
-- owner already proves that a supplied effective Hilbert-dimension area bound
-- yields UV finiteness.  The result constrains capacity/mode count.  It does
-- not compute entropy, birthmark amplitude, residual information density, or
-- gravitational curvature.
------------------------------------------------------------------------

areaBoundImpliesUVFinite :
  (A : HoloUV.UVFinitenessAxioms) →
  (areaBound : HoloUV.AreaBound A) →
  UV.UVFinite
    (record
      { L = HoloUV.L A
      ; dimH = HoloUV.dimH A
      ; bound = λ l → HoloUV.eta A * HoloUV.area A l
      ; dimH≤bound = areaBound
      })
areaBoundImpliesUVFinite = HoloUV.UVFinitenessTheorem

record HolographicCapacityBoundary : Set where
  constructor holographicCapacityBoundary
  field
    suppliedAreaBoundImpliesUVFinite : Bool
    areaBoundConstrainsEffectiveHilbertDimension : Bool
    areaCapacityDoesNotDetermineBoundaryEntropy : Bool
    areaCapacityDoesNotDetermineBirthmarkValue : Bool
    areaCapacityDoesNotDetermineResidualInformationDensity : Bool
    areaCapacityDoesNotDetermineCurvature : Bool

canonicalHolographicCapacityBoundary : HolographicCapacityBoundary
canonicalHolographicCapacityBoundary =
  holographicCapacityBoundary true true true true true true

areaCapacityDoesNotDetermineBirthmarkValue : Bool
areaCapacityDoesNotDetermineBirthmarkValue = true

areaCapacityDoesNotDetermineResidualInformationDensity : Bool
areaCapacityDoesNotDetermineResidualInformationDensity = true
