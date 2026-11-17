module DASHI.Analysis.CollatzSyracuseExactAffineTerminalExact where

------------------------------------------------------------------------
-- EXACT AFFINE TERMINAL SOURCE
--
-- The coarse correction theorem 3^m <= x is deliberately not used here.
-- The exact affine identity already owned by the repository is
--
--   2^m * S^m(x)
--     = 3^(s_m(x)) * x + A(parityWord m x).
--
-- Therefore literal strict descent at a chosen horizon is equivalent to the
-- exact integer scalar margin
--
--   3^(s_m(x)) * x + A(word) < 2^m * x.
--
-- This is the lossless arithmetic max-cut for the universal theorem.  It keeps
-- the additive correction term rather than replacing it by the coarse 3^m
-- envelope.  In particular it can represent small starts such as x = 3 at
-- their genuine strict-descent horizon.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_)
import Data.Nat.Properties as NatP
import Data.Product as Product
open Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseAffineDescentMarginExact as Margin
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Stop

------------------------------------------------------------------------
-- Descent <-> exact affine margin at the same literal horizon.
------------------------------------------------------------------------

strictDescentImpliesExactAffineMargin :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat (Syracuse.syracuseIterate m x) < Syracuse.toNat x →
  Margin.literalAffineNumerator m x
    < Affine.powNat 2 m * Syracuse.toNat x
strictDescentImpliesExactAffineMargin m x descent =
  let
    scaled :
      Affine.powNat 2 m
        * Syracuse.toNat (Syracuse.syracuseIterate m x)
      < Affine.powNat 2 m * Syracuse.toNat x
    scaled = NatP.*-monoʳ-< (Affine.powNat 2 m) descent
  in
  subst
    (λ numerator → numerator < Affine.powNat 2 m * Syracuse.toNat x)
    (Margin.affineNumeratorExact m x)
    scaled

exactAffineMarginImpliesStrictDescent :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  Margin.literalAffineNumerator m x
    < Affine.powNat 2 m * Syracuse.toNat x →
  Syracuse.toNat (Syracuse.syracuseIterate m x) < Syracuse.toNat x
exactAffineMarginImpliesStrictDescent = Margin.strictAffineMarginImpliesDescent

------------------------------------------------------------------------
-- Universal exact-margin source.
------------------------------------------------------------------------

record ExactAffineTerminalSource : Set₁ where
  field
    exactMargin :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      Σ Nat (λ m →
        Margin.literalAffineNumerator m x
          < Affine.powNat 2 m * Syracuse.toNat x)

open ExactAffineTerminalSource public

asLiteralStrictDescentSource :
  ExactAffineTerminalSource →
  Stop.LiteralStrictDescentSource
asLiteralStrictDescentSource source = record
  { descend = λ x nontrivial →
      let
        witness = exactMargin source x nontrivial
        m = Product.proj₁ witness
        margin = Product.proj₂ witness
      in
      m , exactAffineMarginImpliesStrictDescent m x margin
  }

fromLiteralStrictDescentSource :
  Stop.LiteralStrictDescentSource →
  ExactAffineTerminalSource
fromLiteralStrictDescentSource source = record
  { exactMargin = λ x nontrivial →
      let
        witness = Stop.descend source x nontrivial
        m = Product.proj₁ witness
        descent = Product.proj₂ witness
      in
      m , strictDescentImpliesExactAffineMargin m x descent
  }

universalStoppingFromExactAffineMargins :
  ExactAffineTerminalSource →
  (x : Syracuse.PositiveNat) →
  Stop.ReachesOne x
universalStoppingFromExactAffineMargins source =
  Stop.universalStoppingFromStrictDescent
    (asLiteralStrictDescentSource source)

record ExactAffineTerminalBoundary : Set where
  constructor exactAffineTerminalBoundary
  field
    exactIdentityReused : Nat
    descentToMarginOwned : Nat
    marginToDescentOwned : Nat
    universalSourceEquivalentToStrictDescent : Nat
    coarseThreePowThresholdRequired : Nat
    universalExactMarginProducerOwned : Nat

canonicalExactAffineTerminalBoundary : ExactAffineTerminalBoundary
canonicalExactAffineTerminalBoundary =
  exactAffineTerminalBoundary 1 1 1 1 0 0
