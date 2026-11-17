{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayBishopSU2DeterminantExact where

-- YM.REAL: REAL Bishop-quaternion 2x2 matrix determinant polynomial.
-- This is SU(2) determinant for the explicit norm-one quaternion.
-- Not an assertion that an arbitrary Bishop-quaternion carrier is
-- already the selected compact original Wilson link group.
--
-- Source: classical quaternion SU(2) representation; Bishop/Murray/
-- Csimma setoid real; original DASHI BishopComplex/trace owners.
-- No legacy RealAnalysisAxioms, no new postulate.
--
-- REQUIREMENT: Agda 2.9 kernel --safe acceptance still pending.

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as B
import RealProperties as BP
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Physics.YangMills.YMClayBishopSU2QuaternionTraceWeldExact as Q

normSq : Q.BishopQuaternion → B.ℝ
normSq q =
  B._+_
    (B._*_ (Q.q0 q) (Q.q0 q))
    (B._+_
      (B._*_ (Q.q1 q) (Q.q1 q))
      (B._+_
        (B._*_ (Q.q2 q) (Q.q2 q))
        (B._*_ (Q.q3 q) (Q.q3 q))))

record UnitQuaternion : Set where
  constructor unitQuaternion
  field
    quaternion : Q.BishopQuaternion
    unitNorm : B._≃_ (normSq quaternion) B.1ℝ
open UnitQuaternion public

-- Fully specified diagonal/off-diagonal entries (the previous helper
-- used the four Fin 2 indices, not an ad hoc matrix).
-- Use the explicit coordinates to avoid inferred or implicit matrix index.
quaternionDeterminantExplicit : Q.BishopQuaternion → C.BishopComplex
quaternionDeterminantExplicit q =
  C._-C_
    (C._*C_
      (C.complex (Q.q0 q) (Q.q3 q))
      (C.complex (Q.q0 q) (B.- (Q.q3 q))))
    (C._*C_
      (C.complex (Q.q2 q) (Q.q1 q))
      (C.complex (B.- (Q.q2 q)) (Q.q1 q)))

determinantRealIsNorm :
  ∀ q →
  B._≃_ (C.re (quaternionDeterminantExplicit q)) (normSq q)
determinantRealIsNorm q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((a ⊗ a) ⊖ (d ⊗ (⊝ d)))
        ⊖ ((c ⊗ (⊝ c)) ⊖ (b ⊗ b)))
      ⊜
      ((a ⊗ a) ⊕ ((b ⊗ b) ⊕ ((c ⊗ c) ⊕ (d ⊗ d))))))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

determinantImaginaryZero :
  ∀ q →
  B._≃_ (C.im (quaternionDeterminantExplicit q)) B.0ℝ
determinantImaginaryZero q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((a ⊗ (⊝ d)) ⊕ (d ⊗ a))
        ⊖ ((c ⊗ b) ⊕ (b ⊗ (⊝ c))))
      ⊜ Κ 0ℚᵘ))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

unitQuaternionDeterminantOne :
  ∀ u →
  C._≈C_
    (quaternionDeterminantExplicit (quaternion u))
    C.oneC
unitQuaternionDeterminantOne u =
  C.complex-equivalent
    (BP.≃-trans
      (determinantRealIsNorm (quaternion u))
      (unitNorm u))
    (determinantImaginaryZero (quaternion u))
