{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BoolGoldenExact where

------------------------------------------------------------------------
-- Shared literal Boolean comparison/conjunction, previously owned by
-- Karp21SparseEndpointCutCertificateExact and N21 consistency proofs.
-- Extract once so Cook's SAT witness and Max-Cut endpoint consistency
-- consume the SAME definitions without importing one another's graphs.
--
-- No postulates, metas, termination overrides, graph carrier, cost
-- oracle, or syntax-specific proxy.  Authoritative kernel status
-- requires an independent Agda --safe check.
--
-- Original logic: finite Boolean equality and conjunction.
-- DASHI proof owners: Karp21SparseEndpointCutCertificateExact,
-- Karp21SparseEndpointConsistencySoundExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

boolEqual : Bool → Bool → Bool
boolEqual true true = true
boolEqual false false = true
boolEqual true false = false
boolEqual false true = false

andBool : Bool → Bool → Bool
andBool true x = x
andBool false x = false

boolEqualSelf : (value : Bool) → boolEqual value value ≡ true
boolEqualSelf true = refl
boolEqualSelf false = refl

andLeftTrue :
  (a b : Bool) →
  andBool a b ≡ true → a ≡ true
andLeftTrue true b proof = refl
andLeftTrue false b ()

andRightTrue :
  (a b : Bool) →
  andBool a b ≡ true → b ≡ true
andRightTrue true b proof = proof
andRightTrue false b ()

boolEqualTrueImpliesEqual :
  (a b : Bool) →
  boolEqual a b ≡ true → a ≡ b
boolEqualTrueImpliesEqual true true proof = refl
boolEqualTrueImpliesEqual false false proof = refl
boolEqualTrueImpliesEqual true false ()
boolEqualTrueImpliesEqual false true ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()
