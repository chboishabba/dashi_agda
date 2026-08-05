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
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

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

upAgainstQPlusKZero :
  (triad : ResonantDivergenceFreeTriad) →
  V.dot (up triad) (q triad) + V.dot (up triad) (k triad) ≡ 0ℚ
upAgainstQPlusKZero triad
  with k triad | p triad | q triad | up triad
... | V.v3 kx ky kz | V.v3 px py pz | V.v3 qx qy qz
    | V.v3 ux uy uz
  rewrite resonanceX triad
        | resonanceY triad
        | resonanceZ triad
        | upTransverse triad =
  solve (kx ∷ ky ∷ kz ∷ px ∷ py ∷ pz ∷ ux ∷ uy ∷ uz ∷ [])

uqAgainstPPlusKZero :
  (triad : ResonantDivergenceFreeTriad) →
  V.dot (uq triad) (p triad) + V.dot (uq triad) (k triad) ≡ 0ℚ
uqAgainstPPlusKZero triad
  with k triad | p triad | q triad | uq triad
... | V.v3 kx ky kz | V.v3 px py pz | V.v3 qx qy qz
    | V.v3 ux uy uz
  rewrite resonanceX triad
        | resonanceY triad
        | resonanceZ triad
        | uqTransverse triad =
  solve (kx ∷ ky ∷ kz ∷ px ∷ py ∷ pz ∷ ux ∷ uy ∷ uz ∷ [])

ukAgainstQPlusPZero :
  (triad : ResonantDivergenceFreeTriad) →
  V.dot (uk triad) (q triad) + V.dot (uk triad) (p triad) ≡ 0ℚ
ukAgainstQPlusPZero triad
  with k triad | p triad | q triad | uk triad
... | V.v3 kx ky kz | V.v3 px py pz | V.v3 qx qy qz
    | V.v3 ux uy uz
  rewrite resonanceX triad
        | resonanceY triad
        | resonanceZ triad
        | ukTransverse triad =
  solve (kx ∷ ky ∷ kz ∷ px ∷ py ∷ pz ∷ ux ∷ uy ∷ uz ∷ [])

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
finiteCyclicTriadEnergyCancellation triad =
  begin
    cyclicTransfer triad
  ≡⟨ cyclicTransferGrouped triad ⟩
    V.dot (uk triad) (uq triad)
      * (V.dot (up triad) (q triad) + V.dot (up triad) (k triad))
    + V.dot (uk triad) (up triad)
      * (V.dot (uq triad) (p triad) + V.dot (uq triad) (k triad))
    + V.dot (up triad) (uq triad)
      * (V.dot (uk triad) (q triad) + V.dot (uk triad) (p triad))
  ≡⟨ congThree ⟩
    V.dot (uk triad) (uq triad) * 0ℚ
    + V.dot (uk triad) (up triad) * 0ℚ
    + V.dot (up triad) (uq triad) * 0ℚ
  ≡⟨ solve
       ( V.dot (uk triad) (uq triad)
       ∷ V.dot (uk triad) (up triad)
       ∷ V.dot (up triad) (uq triad)
       ∷ []
       ) ⟩
    0ℚ
  ∎
  where
  congThree :
    V.dot (uk triad) (uq triad)
      * (V.dot (up triad) (q triad) + V.dot (up triad) (k triad))
    + V.dot (uk triad) (up triad)
      * (V.dot (uq triad) (p triad) + V.dot (uq triad) (k triad))
    + V.dot (up triad) (uq triad)
      * (V.dot (uk triad) (q triad) + V.dot (uk triad) (p triad))
    ≡ V.dot (uk triad) (uq triad) * 0ℚ
      + V.dot (uk triad) (up triad) * 0ℚ
      + V.dot (up triad) (uq triad) * 0ℚ
  congThree
    rewrite upAgainstQPlusKZero triad
          | uqAgainstPPlusKZero triad
          | ukAgainstQPlusPZero triad = refl
