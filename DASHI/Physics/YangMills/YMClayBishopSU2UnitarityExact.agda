{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayBishopSU2UnitarityExact where

-- YM.REAL finite source: U(q)† U(q)=I for Bishop norm-one quaternions.
-- Each scalar equality is reduced to a polynomial identity by the
-- *existing* Bishop real ring solver. Neither original link identity,
-- constructive Haar nor continuum YM is asserted.
-- Attribution: classical SU2/quaternions; Murray/Csimma/Bishop;
-- original DASHI BishopSetoidComplex + quaternion trace owners.

import Data.Fin.Base as Fin
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as B
import RealProperties as BP
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Physics.YangMills.YMClayBishopSU2QuaternionTraceWeldExact as Q
import DASHI.Physics.YangMills.YMClayBishopSU2DeterminantExact as D

gram : Q.BishopQuaternion → Fin.Fin 2 → Fin.Fin 2 → C.BishopComplex
gram q i j =
  C._+C_
    (C._*C_
      (C.conjugate (Q.quaternionMatrix q Fin.zero i))
      (Q.quaternionMatrix q Fin.zero j))
    (C._*C_
      (C.conjugate (Q.quaternionMatrix q (Fin.suc Fin.zero) i))
      (Q.quaternionMatrix q (Fin.suc Fin.zero) j))

gram00Real : ∀ q →
  B._≃_ (C.re (gram q Fin.zero Fin.zero)) (D.normSq q)
gram00Real q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((a ⊗ a) ⊖ ((⊝ d) ⊗ d)) ⊕ (((⊝ c) ⊗ (⊝ c)) ⊖ ((⊝ b) ⊗ b))) ⊜ ((a ⊗ a) ⊕ ((b ⊗ b) ⊕ ((c ⊗ c) ⊕ (d ⊗ d))))))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

gram00Imag : ∀ q →
  B._≃_ (C.im (gram q Fin.zero Fin.zero)) B.0ℝ
gram00Imag q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((a ⊗ d) ⊕ ((⊝ d) ⊗ a)) ⊕ (((⊝ c) ⊗ b) ⊕ ((⊝ b) ⊗ (⊝ c)))) ⊜ Κ 0ℚᵘ))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

gram01Real : ∀ q →
  B._≃_ (C.re (gram q Fin.zero (Fin.suc Fin.zero))) B.0ℝ
gram01Real q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((a ⊗ c) ⊖ ((⊝ d) ⊗ b)) ⊕ (((⊝ c) ⊗ a) ⊖ ((⊝ b) ⊗ (⊝ d)))) ⊜ Κ 0ℚᵘ))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

gram01Imag : ∀ q →
  B._≃_ (C.im (gram q Fin.zero (Fin.suc Fin.zero))) B.0ℝ
gram01Imag q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((a ⊗ b) ⊕ ((⊝ d) ⊗ c)) ⊕ (((⊝ c) ⊗ (⊝ d)) ⊕ ((⊝ b) ⊗ a))) ⊜ Κ 0ℚᵘ))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

gram10Real : ∀ q →
  B._≃_ (C.re (gram q (Fin.suc Fin.zero) Fin.zero)) B.0ℝ
gram10Real q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((c ⊗ a) ⊖ ((⊝ b) ⊗ d)) ⊕ ((a ⊗ (⊝ c)) ⊖ (d ⊗ b))) ⊜ Κ 0ℚᵘ))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

gram10Imag : ∀ q →
  B._≃_ (C.im (gram q (Fin.suc Fin.zero) Fin.zero)) B.0ℝ
gram10Imag q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((c ⊗ d) ⊕ ((⊝ b) ⊗ a)) ⊕ ((a ⊗ b) ⊕ (d ⊗ (⊝ c)))) ⊜ Κ 0ℚᵘ))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

gram11Real : ∀ q →
  B._≃_ (C.re (gram q (Fin.suc Fin.zero) (Fin.suc Fin.zero))) (D.normSq q)
gram11Real q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((c ⊗ c) ⊖ ((⊝ b) ⊗ b)) ⊕ ((a ⊗ a) ⊖ (d ⊗ (⊝ d)))) ⊜ ((a ⊗ a) ⊕ ((b ⊗ b) ⊕ ((c ⊗ c) ⊕ (d ⊗ d))))))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

gram11Imag : ∀ q →
  B._≃_ (C.im (gram q (Fin.suc Fin.zero) (Fin.suc Fin.zero))) B.0ℝ
gram11Imag q =
  let open BP.ℝ-Solver in
  solve 4
    (λ a b c d →
      ((((c ⊗ b) ⊕ ((⊝ b) ⊗ c)) ⊕ ((a ⊗ (⊝ d)) ⊕ (d ⊗ a))) ⊜ Κ 0ℚᵘ))
    BP.≃-refl (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)


-- This establishes entrywise unitarity for the SAME norm-one quaternion.
-- No propositional equality is inferred from Bishop setoid equivalence.
unitQuaternionGram00 : ∀ u →
  C._≈C_ (gram (D.quaternion u) Fin.zero Fin.zero) C.oneC
unitQuaternionGram00 u =
  C.complex-equivalent
    (BP.≃-trans
      (gram00Real (D.quaternion u))
      (D.unitNorm u))
    (gram00Imag (D.quaternion u))

unitQuaternionGram01 : ∀ u →
  C._≈C_
    (gram (D.quaternion u) Fin.zero (Fin.suc Fin.zero))
    C.zeroC
unitQuaternionGram01 u =
  C.complex-equivalent
    (gram01Real (D.quaternion u))
    (gram01Imag (D.quaternion u))

unitQuaternionGram10 : ∀ u →
  C._≈C_
    (gram (D.quaternion u) (Fin.suc Fin.zero) Fin.zero)
    C.zeroC
unitQuaternionGram10 u =
  C.complex-equivalent
    (gram10Real (D.quaternion u))
    (gram10Imag (D.quaternion u))

unitQuaternionGram11 : ∀ u →
  C._≈C_
    (gram (D.quaternion u) (Fin.suc Fin.zero) (Fin.suc Fin.zero))
    C.oneC
unitQuaternionGram11 u =
  C.complex-equivalent
    (BP.≃-trans
      (gram11Real (D.quaternion u))
      (D.unitNorm u))
    (gram11Imag (D.quaternion u))

-- The four entry lemmas above are the complete 2x2 matrix equality.
-- No additional generic matrix extensionality is needed in downstream
-- consumers; case distinction on Fin 2 reuses these exact owners.


unit2 : Fin.Fin 2 → Fin.Fin 2 → C.BishopComplex
unit2 Fin.zero Fin.zero = C.oneC
unit2 Fin.zero (Fin.suc Fin.zero) = C.zeroC
unit2 (Fin.suc Fin.zero) Fin.zero = C.zeroC
unit2 (Fin.suc Fin.zero) (Fin.suc Fin.zero) = C.oneC

bishopQuaternionUdaggerUIsIdentity :
  (u : D.UnitQuaternion) → ∀ i j →
  C._≈C_ (gram (D.quaternion u) i j) (unit2 i j)
bishopQuaternionUdaggerUIsIdentity u Fin.zero Fin.zero =
  unitQuaternionGram00 u
bishopQuaternionUdaggerUIsIdentity u Fin.zero (Fin.suc Fin.zero) =
  unitQuaternionGram01 u
bishopQuaternionUdaggerUIsIdentity u (Fin.suc Fin.zero) Fin.zero =
  unitQuaternionGram10 u
bishopQuaternionUdaggerUIsIdentity
  u (Fin.suc Fin.zero) (Fin.suc Fin.zero) =
  unitQuaternionGram11 u
