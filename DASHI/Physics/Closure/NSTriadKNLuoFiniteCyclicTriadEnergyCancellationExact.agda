module DASHI.Physics.Closure.NSTriadKNLuoFiniteCyclicTriadEnergyCancellationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Peter Constantin; Ciprian Foias.
-- Title: "Navier--Stokes Equations".
-- University of Chicago Press, 1988.
-- DOI: 10.7208/chicago/9780226115498.001.0001.
--
-- PURPOSE
-- Prove the literal finite triad cancellation that is often hidden under the
-- formal identity <(u dot grad)u,u>=0.  For one resonant triad
--
--   k + p + q = 0
--
-- with uk, up, uq transverse to their own wavevectors, the six symmetrised
-- convection transfers cancel after cyclic grouping.  This theorem does not
-- claim that each ordered pair vanishes separately and therefore preserves
-- the distinction between reality pairing and genuine cyclic cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; sym; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

minusOne : ℚ
minusOne = - 1ℚ

zeroVector : V.Vector3
zeroVector = V.v3 0ℚ 0ℚ 0ℚ

record ResonantDivergenceFreeTriad : Set where
  constructor resonant-divergence-free-triad
  field
    k p q : V.Vector3
    uk up uq : V.Vector3

    resonance : V.add (V.add k p) q ≡ zeroVector

    ukTransverse : V.dot k uk ≡ 0ℚ
    upTransverse : V.dot p up ≡ 0ℚ
    uqTransverse : V.dot q uq ≡ 0ℚ

open ResonantDivergenceFreeTriad public

resonanceX :
  (triad : ResonantDivergenceFreeTriad) →
  (V.x (k triad) + V.x (p triad)) + V.x (q triad) ≡ 0ℚ
resonanceX triad = cong V.x (resonance triad)

resonanceY :
  (triad : ResonantDivergenceFreeTriad) →
  (V.y (k triad) + V.y (p triad)) + V.y (q triad) ≡ 0ℚ
resonanceY triad = cong V.y (resonance triad)

resonanceZ :
  (triad : ResonantDivergenceFreeTriad) →
  (V.z (k triad) + V.z (p triad)) + V.z (q triad) ≡ 0ℚ
resonanceZ triad = cong V.z (resonance triad)

componentOpposite :
  (a b c : ℚ) →
  (a + b) + c ≡ 0ℚ →
  c + a ≡ - b
componentOpposite a b c sumZero =
  begin
    c + a
  ≡⟨ solve (a ∷ b ∷ c ∷ []) ⟩
    ((a + b) + c) - b
  ≡⟨ cong (λ total → total - b) sumZero ⟩
    0ℚ - b
  ≡⟨ solve (b ∷ []) ⟩
    - b
  ∎

componentOppositeScaled :
  (a b c : ℚ) →
  (a + b) + c ≡ 0ℚ →
  c + a ≡ minusOne * b
componentOppositeScaled a b c sumZero =
  trans
    (componentOpposite a b c sumZero)
    (solve (b ∷ []))

qPlusKEqualsNegativeP :
  (triad : ResonantDivergenceFreeTriad) →
  V.add (q triad) (k triad) ≡ V.scale minusOne (p triad)
qPlusKEqualsNegativeP triad
  with k triad | p triad | q triad
... | V.v3 kx ky kz | V.v3 px py pz | V.v3 qx qy qz =
  V.vectorExt
    (componentOppositeScaled kx px qx (resonanceX triad))
    (componentOppositeScaled ky py qy (resonanceY triad))
    (componentOppositeScaled kz pz qz (resonanceZ triad))

pPlusKEqualsNegativeQ :
  (triad : ResonantDivergenceFreeTriad) →
  V.add (p triad) (k triad) ≡ V.scale minusOne (q triad)
pPlusKEqualsNegativeQ triad
  with k triad | p triad | q triad
... | V.v3 kx ky kz | V.v3 px py pz | V.v3 qx qy qz =
  V.vectorExt
    (trans
      (solve (kx ∷ px ∷ []))
      (componentOppositeScaled px qx kx
        (trans (solve (kx ∷ px ∷ qx ∷ [])) (resonanceX triad))))
    (trans
      (solve (ky ∷ py ∷ []))
      (componentOppositeScaled py qy ky
        (trans (solve (ky ∷ py ∷ qy ∷ [])) (resonanceY triad))))
    (trans
      (solve (kz ∷ pz ∷ []))
      (componentOppositeScaled pz qz kz
        (trans (solve (kz ∷ pz ∷ qz ∷ [])) (resonanceZ triad))))

qPlusPEqualsNegativeK :
  (triad : ResonantDivergenceFreeTriad) →
  V.add (q triad) (p triad) ≡ V.scale minusOne (k triad)
qPlusPEqualsNegativeK triad
  with k triad | p triad | q triad
... | V.v3 kx ky kz | V.v3 px py pz | V.v3 qx qy qz =
  V.vectorExt
    (trans
      (solve (px ∷ qx ∷ []))
      (componentOppositeScaled qx kx px
        (trans (solve (kx ∷ px ∷ qx ∷ [])) (resonanceX triad))))
    (trans
      (solve (py ∷ qy ∷ []))
      (componentOppositeScaled qy ky py
        (trans (solve (ky ∷ py ∷ qy ∷ [])) (resonanceY triad))))
    (trans
      (solve (pz ∷ qz ∷ []))
      (componentOppositeScaled qz kz pz
        (trans (solve (kz ∷ pz ∷ qz ∷ [])) (resonanceZ triad))))

dotAddRight :
  (a b c : V.Vector3) →
  V.dot a (V.add b c) ≡ V.dot a b + V.dot a c
dotAddRight
    (V.v3 ax ay az)
    (V.v3 bx by bz)
    (V.v3 cx cy cz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ cx ∷ cy ∷ cz ∷ [])

upAgainstQPlusKZero :
  (triad : ResonantDivergenceFreeTriad) →
  V.dot (up triad) (q triad) + V.dot (up triad) (k triad) ≡ 0ℚ
upAgainstQPlusKZero triad =
  begin
    V.dot (up triad) (q triad) + V.dot (up triad) (k triad)
  ≡⟨ sym (dotAddRight (up triad) (q triad) (k triad)) ⟩
    V.dot (up triad) (V.add (q triad) (k triad))
  ≡⟨ cong (V.dot (up triad)) (qPlusKEqualsNegativeP triad) ⟩
    V.dot (up triad) (V.scale minusOne (p triad))
  ≡⟨ V.dotScaleRight (up triad) (p triad) minusOne ⟩
    minusOne * V.dot (up triad) (p triad)
  ≡⟨ cong
       (λ value → minusOne * value)
       (trans (V.dotCommutative (up triad) (p triad))
         (upTransverse triad)) ⟩
    minusOne * 0ℚ
  ≡⟨ solve [] ⟩
    0ℚ
  ∎

uqAgainstPPlusKZero :
  (triad : ResonantDivergenceFreeTriad) →
  V.dot (uq triad) (p triad) + V.dot (uq triad) (k triad) ≡ 0ℚ
uqAgainstPPlusKZero triad =
  begin
    V.dot (uq triad) (p triad) + V.dot (uq triad) (k triad)
  ≡⟨ sym (dotAddRight (uq triad) (p triad) (k triad)) ⟩
    V.dot (uq triad) (V.add (p triad) (k triad))
  ≡⟨ cong (V.dot (uq triad)) (pPlusKEqualsNegativeQ triad) ⟩
    V.dot (uq triad) (V.scale minusOne (q triad))
  ≡⟨ V.dotScaleRight (uq triad) (q triad) minusOne ⟩
    minusOne * V.dot (uq triad) (q triad)
  ≡⟨ cong
       (λ value → minusOne * value)
       (trans (V.dotCommutative (uq triad) (q triad))
         (uqTransverse triad)) ⟩
    minusOne * 0ℚ
  ≡⟨ solve [] ⟩
    0ℚ
  ∎

ukAgainstQPlusPZero :
  (triad : ResonantDivergenceFreeTriad) →
  V.dot (uk triad) (q triad) + V.dot (uk triad) (p triad) ≡ 0ℚ
ukAgainstQPlusPZero triad =
  begin
    V.dot (uk triad) (q triad) + V.dot (uk triad) (p triad)
  ≡⟨ sym (dotAddRight (uk triad) (q triad) (p triad)) ⟩
    V.dot (uk triad) (V.add (q triad) (p triad))
  ≡⟨ cong (V.dot (uk triad)) (qPlusPEqualsNegativeK triad) ⟩
    V.dot (uk triad) (V.scale minusOne (k triad))
  ≡⟨ V.dotScaleRight (uk triad) (k triad) minusOne ⟩
    minusOne * V.dot (uk triad) (k triad)
  ≡⟨ cong
       (λ value → minusOne * value)
       (trans (V.dotCommutative (uk triad) (k triad))
         (ukTransverse triad)) ⟩
    minusOne * 0ℚ
  ≡⟨ solve [] ⟩
    0ℚ
  ∎

cyclicTransfer : ResonantDivergenceFreeTriad → ℚ
cyclicTransfer triad =
    V.dot (up triad) (q triad) * V.dot (uk triad) (uq triad)
  + V.dot (uq triad) (p triad) * V.dot (uk triad) (up triad)
  + V.dot (uq triad) (k triad) * V.dot (uk triad) (up triad)
  + V.dot (uk triad) (q triad) * V.dot (up triad) (uq triad)
  + V.dot (uk triad) (p triad) * V.dot (up triad) (uq triad)
  + V.dot (up triad) (k triad) * V.dot (uk triad) (uq triad)

cyclicTransferGrouped :
  (triad : ResonantDivergenceFreeTriad) →
  cyclicTransfer triad
  ≡ V.dot (uk triad) (uq triad)
      * (V.dot (up triad) (q triad) + V.dot (up triad) (k triad))
    + V.dot (uk triad) (up triad)
      * (V.dot (uq triad) (p triad) + V.dot (uq triad) (k triad))
    + V.dot (up triad) (uq triad)
      * (V.dot (uk triad) (q triad) + V.dot (uk triad) (p triad))
cyclicTransferGrouped triad =
  solve
    ( V.dot (up triad) (q triad)
    ∷ V.dot (up triad) (k triad)
    ∷ V.dot (uq triad) (p triad)
    ∷ V.dot (uq triad) (k triad)
    ∷ V.dot (uk triad) (q triad)
    ∷ V.dot (uk triad) (p triad)
    ∷ V.dot (uk triad) (uq triad)
    ∷ V.dot (uk triad) (up triad)
    ∷ V.dot (up triad) (uq triad)
    ∷ []
    )

finiteCyclicTriadEnergyCancellation :
  (triad : ResonantDivergenceFreeTriad) →
  cyclicTransfer triad ≡ 0ℚ
finiteCyclicTriadEnergyCancellation triad
  rewrite cyclicTransferGrouped triad
        | upAgainstQPlusKZero triad
        | uqAgainstPPlusKZero triad
        | ukAgainstQPlusPZero triad =
  solve
    ( V.dot (uk triad) (uq triad)
    ∷ V.dot (uk triad) (up triad)
    ∷ V.dot (up triad) (uq triad)
    ∷ []
    )
