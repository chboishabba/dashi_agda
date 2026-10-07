module DASHI.NumberTheory.Collatz.SyracuseAffineDescentMarginExact where

------------------------------------------------------------------------
-- EXACT INTEGER DESCENT FROM THE AFFINE NUMERATOR MARGIN
--
-- This is the Collatz analogue of the repository's terminal-scalar-margin
-- pattern: no logarithm is needed to conclude descent once the literal affine
-- numerator is strictly below 2^m * x.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Data.Nat using (_<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseOneStepArithmeticExact as OneStep

literalAffineNumerator :
  (m : Nat) →
  Syracuse.PositiveNat →
  Nat
literalAffineNumerator m x =
  Affine.powNat 3
      (Affine.parityCount (Itinerary.parityWord m x))
    * Syracuse.toNat x
  + Affine.affineAdditiveTerm (Itinerary.parityWord m x)

affineNumeratorExact :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  Affine.powNat 2 m
    * Syracuse.toNat (Syracuse.syracuseIterate m x)
  ≡ literalAffineNumerator m x
affineNumeratorExact =
  Affine.syracuseAffineIterateExact OneStep.canonicalAffineIterateSource

strictAffineMarginImpliesDescent :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  literalAffineNumerator m x
    < Affine.powNat 2 m * Syracuse.toNat x →
  Syracuse.toNat (Syracuse.syracuseIterate m x) < Syracuse.toNat x
strictAffineMarginImpliesDescent m x margin =
  let
    scaledDescent :
      Affine.powNat 2 m
        * Syracuse.toNat (Syracuse.syracuseIterate m x)
      < Affine.powNat 2 m * Syracuse.toNat x
    scaledDescent =
      subst
        (λ numerator →
          numerator < Affine.powNat 2 m * Syracuse.toNat x)
        (sym (affineNumeratorExact m x))
        margin
  in
  NatP.*-cancelˡ-<
    (Affine.powNat 2 m)
    (Syracuse.toNat (Syracuse.syracuseIterate m x))
    (Syracuse.toNat x)
    scaledDescent

record AffineDescentBoundary : Set where
  constructor affineDescentBoundary
  field
    exactAffineIdentityOwned : Nat
    strictScalarMarginSuffices : Nat
    logarithmRequiredForDescentCompiler : Nat
    scalarMarginAutomaticallyProduced : Nat

canonicalAffineDescentBoundary : AffineDescentBoundary
canonicalAffineDescentBoundary = affineDescentBoundary 1 1 0 0
