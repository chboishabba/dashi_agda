module DASHI.Analysis.CollatzSyracuseAffineCorrectionCocycleExact where

------------------------------------------------------------------------
-- EXACT WORD CONCATENATION / AFFINE-CORRECTION COCYCLE
--
-- EXTERNAL CROSS-POLLINATION SOURCE
-- Michael Sharpe, `msharpe248/collatz`, commit
--   ec8174b567d5cab4960024782210b5f5db02bd3a
-- file `lean/Collatz/Shadow.lean`, theorem `Collatz.dcoef_add`.
--
-- ATTRIBUTION FIREWALL
-- The external Lean theorem identifies the useful cocycle pattern for its
-- correction `dcoef`.  The definitions and proof below are a DASHI Agda
-- reconstruction on the repository's independently existing
-- `BinaryWord` / `affineAdditiveTerm` carrier.  This module imports no proof
-- object from the external repository, and source provenance is not proof
-- transport.
--
-- For prefix u and suffix v the DASHI correction satisfies
--
--   A(u ++ v) = 3^(ones v) A(u) + 2^(length u) A(v).
--
-- This is the exact cross-scale law needed by variable-length word surgery,
-- 2-adic/3-adic shadow calculations, and prefix replacement.  No probability,
-- logarithm, or Collatz stopping claim enters here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine

------------------------------------------------------------------------
-- Prefix-preserving binary-word append.
------------------------------------------------------------------------

appendWord :
  {m n : Nat} →
  Binary.BinaryWord m →
  Binary.BinaryWord n →
  Binary.BinaryWord (m + n)
appendWord Binary.end suffix = suffix
appendWord (Binary.bit0 prefix) suffix =
  Binary.bit0 (appendWord prefix suffix)
appendWord (Binary.bit1 prefix) suffix =
  Binary.bit1 (appendWord prefix suffix)

parityCountAppend :
  {m n : Nat} →
  (prefix : Binary.BinaryWord m) →
  (suffix : Binary.BinaryWord n) →
  Affine.parityCount (appendWord prefix suffix)
  ≡ Affine.parityCount prefix + Affine.parityCount suffix
parityCountAppend Binary.end suffix = refl
parityCountAppend (Binary.bit0 prefix) suffix =
  parityCountAppend prefix suffix
parityCountAppend (Binary.bit1 prefix) suffix =
  cong suc (parityCountAppend prefix suffix)

------------------------------------------------------------------------
-- Power addition in the repository's executable `powNat` representation.
------------------------------------------------------------------------

powAdd :
  (base left right : Nat) →
  Affine.powNat base (left + right)
  ≡ Affine.powNat base left * Affine.powNat base right
powAdd base zero right =
  sym (NatP.*-identityˡ (Affine.powNat base right))
powAdd base (suc left) right =
  trans
    (cong (base *_) (powAdd base left right))
    (sym
      (NatP.*-assoc
        base
        (Affine.powNat base left)
        (Affine.powNat base right)))

------------------------------------------------------------------------
-- Pure semiring rearrangements used by the recursive proof.
------------------------------------------------------------------------

bit0CocycleAlgebra :
  (p a q b : Nat) →
  2 * (p * a + q * b)
  ≡ p * (2 * a) + (2 * q) * b
bit0CocycleAlgebra =
  solve 4
    (λ p a q b →
      con 2 :* ((p :* a) :+ (q :* b))
      :=
      (p :* (con 2 :* a)) :+ ((con 2 :* q) :* b))
    refl

bit1CocycleAlgebra :
  (p r a q b : Nat) →
  r * p + 2 * (p * a + q * b)
  ≡ p * (r + 2 * a) + (2 * q) * b
bit1CocycleAlgebra =
  solve 5
    (λ p r a q b →
      (r :* p) :+ (con 2 :* ((p :* a) :+ (q :* b)))
      :=
      (p :* (r :+ (con 2 :* a))) :+ ((con 2 :* q) :* b))
    refl

------------------------------------------------------------------------
-- THE COCYCLE.
------------------------------------------------------------------------

affineCorrectionCocycle :
  {m n : Nat} →
  (prefix : Binary.BinaryWord m) →
  (suffix : Binary.BinaryWord n) →
  Affine.affineAdditiveTerm (appendWord prefix suffix)
  ≡
  Affine.powNat 3 (Affine.parityCount suffix)
    * Affine.affineAdditiveTerm prefix
  + Affine.powNat 2 m
    * Affine.affineAdditiveTerm suffix
affineCorrectionCocycle Binary.end suffix =
  trans
    (sym (NatP.*-identityˡ (Affine.affineAdditiveTerm suffix)))
    (sym
      (NatP.+-identityˡ
        (Affine.powNat 2 zero * Affine.affineAdditiveTerm suffix)))
affineCorrectionCocycle {m = suc m} (Binary.bit0 prefix) suffix
  rewrite
    parityCountAppend prefix suffix
  | affineCorrectionCocycle prefix suffix
  =
  bit0CocycleAlgebra
    (Affine.powNat 3 (Affine.parityCount suffix))
    (Affine.affineAdditiveTerm prefix)
    (Affine.powNat 2 m)
    (Affine.affineAdditiveTerm suffix)
affineCorrectionCocycle {m = suc m} (Binary.bit1 prefix) suffix
  rewrite
    parityCountAppend prefix suffix
  | affineCorrectionCocycle prefix suffix
  | powAdd
      3
      (Affine.parityCount prefix)
      (Affine.parityCount suffix)
  =
  bit1CocycleAlgebra
    (Affine.powNat 3 (Affine.parityCount suffix))
    (Affine.powNat 3 (Affine.parityCount prefix))
    (Affine.affineAdditiveTerm prefix)
    (Affine.powNat 2 m)
    (Affine.affineAdditiveTerm suffix)

record AffineCorrectionCocycleBoundary : Set where
  constructor affineCorrectionCocycleBoundary
  field
    binaryWordAppendOwned : Nat
    parityCountAppendOwned : Nat
    exactCorrectionCocycleOwned : Nat
    externalLeanProofObjectImported : Nat
    stoppingPromotedFromCocycle : Nat

canonicalAffineCorrectionCocycleBoundary : AffineCorrectionCocycleBoundary
canonicalAffineCorrectionCocycleBoundary =
  affineCorrectionCocycleBoundary 1 1 1 0 0
