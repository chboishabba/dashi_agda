module DASHI.Crypto.MLKEMOppositeResidueParityDecompositionExact where

------------------------------------------------------------------------
-- FIPS-203 OPPOSITE-RESIDUE PARITY DECOMPOSITION
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Defensive discovery context
-- ---------------------------
-- The larger CBD2 block probe found that actual FIPS residue pairs (0,1) and
-- (2,3) behave differently from generic pairs in conditioned list geometry.
-- The structural reason is exact and simple:
--
--   gamma_1 = -gamma_0,   gamma_3 = -gamma_2  in F_3329.
--
-- Evaluating an eight-coefficient parity-block polynomial at a and -a splits
-- the observation into even- and odd-exponent sectors.  This module proves the
-- ring identity itself; the F_3329 instantiation and the measured candidate-
-- list geometry remain separate source/computational producers.
--
-- Blue-team interpretation: opposite-residue observations constitute a
-- structurally special joint leakage surface and therefore deserve explicit
-- implementation-level auditing.  This is not a whole-key recovery theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Maybe.Base using (nothing)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

record Poly8 {c ℓ : Level} (R : CommutativeRing c ℓ) : Set (c ⊔ ℓ) where
  open CommutativeRing R renaming (Carrier to F)
  constructor poly8
  field
    c0 c1 c2 c3 c4 c5 c6 c7 : F

open Poly8 public

module _ {c ℓ : Level} (R : CommutativeRing c ℓ) where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _+_ to _⊕_
      ; _*_ to _⊗_
      ; -_ to neg
      ; 0# to 0F
      )

  private
    solverRing : RingCore.AlmostCommutativeRing c ℓ
    solverRing = RingCore.fromCommutativeRing R (λ _ → nothing)

    module S = RingSolver solverRing

  square : F → F
  square a = a ⊗ a

  cube : F → F
  cube a = square a ⊗ a

  fourth : F → F
  fourth a = square a ⊗ square a

  fifth : F → F
  fifth a = fourth a ⊗ a

  sixth : F → F
  sixth a = fourth a ⊗ square a

  seventh : F → F
  seventh a = sixth a ⊗ a

  evenPart : F → Poly8 R → F
  evenPart a p =
    c0 p ⊕
    (c2 p ⊗ square a) ⊕
    (c4 p ⊗ fourth a) ⊕
    (c6 p ⊗ sixth a)

  oddPart : F → Poly8 R → F
  oddPart a p =
    (c1 p ⊗ a) ⊕
    (c3 p ⊗ cube a) ⊕
    (c5 p ⊗ fifth a) ⊕
    (c7 p ⊗ seventh a)

  evalPlus : F → Poly8 R → F
  evalPlus a p = evenPart a p ⊕ oddPart a p

  evalMinus : F → Poly8 R → F
  evalMinus a p = evenPart a p ⊕ neg (oddPart a p)

  twoTimes : F → F
  twoTimes x = x ⊕ x

  oppositeResidueSumSelectsEven :
    (a : F) → (p : Poly8 R) →
    evalPlus a p ⊕ evalMinus a p ≡ twoTimes (evenPart a p)
  oppositeResidueSumSelectsEven a p =
    S.solve 2
      (λ even odd →
        ((even S.⊕ odd) S.⊕ (even S.⊕ (S.⊖ odd)))
          S.⊜ (even S.⊕ even))
      refl
      (evenPart a p)
      (oddPart a p)

  oppositeResidueDifferenceSelectsOdd :
    (a : F) → (p : Poly8 R) →
    evalPlus a p ⊕ neg (evalMinus a p) ≡ twoTimes (oddPart a p)
  oppositeResidueDifferenceSelectsOdd a p =
    S.solve 2
      (λ even odd →
        ((even S.⊕ odd) S.⊕ (S.⊖ (even S.⊕ (S.⊖ odd))))
          S.⊜ (odd S.⊕ odd))
      refl
      (evenPart a p)
      (oddPart a p)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The exact FIPS instantiation still needs the concrete residue equalities in
-- F_3329, e.g. 17 + 3312 = 0 mod 3329 and 2761 + 568 = 0 mod 3329.
--
-- The computational discovery script
--   scripts/crypto_ntt_cbd_block_reconciliation_probe.py
-- studies what this parity-sector split does to conditioned CBD2 candidate
-- lists.  Its finite enumeration is used as a defensive leakage-resolution
-- audit and is deliberately not promoted here to theorem status without a
-- compact kernel proof.
------------------------------------------------------------------------
