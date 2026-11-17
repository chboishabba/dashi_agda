{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayBishopSU2QuaternionTraceWeldExact where

------------------------------------------------------------------------
-- YM.REAL: explicit Bishop-quaternion to Bishop 2x2 complex matrix map.
-- The real trace formula is definitionally exact and is a source-first
-- finite-matrix weld. Quaternion norm one, SU(2) determinant/unitarity,
-- matrix multiplication, compact Haar, and the source Wilson family
-- identity are NOT claimed by this module.
--
-- Reuses the existing Bishop setoid complex and finite trace owners.
-- Attribution: classical SU(2) quaternion representation, Bishop/Murray/
-- Csimma real carrier, original DASHI finite matrix owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Fin.Base as Fin
import Real as B
import RealProperties as BP
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Physics.YangMills.YMClayBishopSetoidFiniteAdjointTraceExact as Trace

record BishopQuaternion : Set where
  constructor quaternion
  field
    q0 q1 q2 q3 : B.ℝ
open BishopQuaternion public

-- U(q) = [q0+i q3,   q2+i q1]
--        [-q2+i q1,  q0-i q3].
quaternionMatrix : BishopQuaternion → Trace.BishopFiniteComplexMatrix 2
quaternionMatrix q Fin.zero Fin.zero =
  C.complex (q0 q) (q3 q)
quaternionMatrix q Fin.zero (Fin.suc Fin.zero) =
  C.complex (q2 q) (q1 q)
quaternionMatrix q (Fin.suc Fin.zero) Fin.zero =
  C.complex (B.- (q2 q)) (q1 q)
quaternionMatrix q (Fin.suc Fin.zero) (Fin.suc Fin.zero) =
  C.complex (q0 q) (B.- (q3 q))

-- Trace is a literal 2-element diagonal fold, not a fresh real axiom.
rawTraceIsDoubleCoordinatePlusZero :
  ∀ q →
  Trace.bishopRealMatrixTrace 2 (quaternionMatrix q)
    ≡ B._+_ (q0 q) (B._+_ (q0 q) B.0ℝ)
rawTraceIsDoubleCoordinatePlusZero q = refl

normalizedTraceIsDoubleCoordinatePlusZero :
  ∀ half q →
  Trace.bishopNormalizedRealTrace 2 half (quaternionMatrix q)
    ≡ B._*_ half (B._+_ (q0 q) (B._+_ (q0 q) B.0ℝ))
normalizedTraceIsDoubleCoordinatePlusZero half q = refl

-- Setoid formulation of the raw-trace normalization for ANY independently
-- proved Bishop half. The half-law is displayed explicitly as an argument:
-- no coercion of Bishop _≃_ to propositional _≡_ and no ad hoc division.
normalizedTraceIsQuaternionRealPart :
  (half : B.ℝ) →
  (halfCancelsDouble : ∀ x →
    B._≃_ (B._*_ half (B._+_ x (B._+_ x B.0ℝ))) x) →
  ∀ q →
  B._≃_
    (Trace.bishopNormalizedRealTrace 2 half (quaternionMatrix q))
    (q0 q)
normalizedTraceIsQuaternionRealPart half halfCancelsDouble q =
  halfCancelsDouble (q0 q)

-- An existing actual Bishop matrix trace theorem applies to the SAME
-- quaternion matrix; no separate adjoint law or new scalar postulate.
quaternionTraceAdjoint :
  ∀ q →
  B._≃_
    (Trace.bishopRealMatrixTrace 2
      (Trace.bishopComplexMatrixAdjoint (quaternionMatrix q)))
    (Trace.bishopRealMatrixTrace 2 (quaternionMatrix q))
quaternionTraceAdjoint q =
  Trace.bishopRealMatrixAdjointTrace 2 (quaternionMatrix q)
