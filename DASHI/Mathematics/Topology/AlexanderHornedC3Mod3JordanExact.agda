module DASHI.Mathematics.Topology.AlexanderHornedC3Mod3JordanExact where

------------------------------------------------------------------------
-- LITERAL MODULAR CONTRAST TO THE EXISTING CHAR-ZERO MASCHKE CUT
--
-- Existing actual owner: Core.FiniteC3OrbitStabilizerExact.
-- Existing actual rational C3 2-plane companion:
--   AlexanderHornedC3MaschkeR3Exact.
--
-- Construct the SAME A = [[0,-1],[1,-1]] on F3^2 with an
-- explicit 3-element field ADDITIVE carrier. This module
-- does not postulate field laws or rely on symbolic 'status'.
--
-- Exact finite proof:
--   A^3=I,
--   N=A-I is nonzero,
--   N^2=0,
--   (1,-1) is a nonzero fixed vector,
--   the C3 group multiplication law acts genuinely.
--
-- Together with the standard theorem that F3[C3] has a unique
-- simple 1D module (since x^3-1=(x-1)^3), nonzero N certifies
-- that this 2D representation is not semisimple. Direct
-- finite decompositions over F5 and F7 are checked in the
-- companion field-comparison script, while the rational
-- Maschke splitting is proved in the prior Agda module.
--
-- No physical spectral operator or Dirac zero mode is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; cong)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

data F3 : Set where
  f0 f1 f2 : F3

_+₃_ : F3 → F3 → F3
f0 +₃ x = x
f1 +₃ f0 = f1
f1 +₃ f1 = f2
f1 +₃ f2 = f0
f2 +₃ f0 = f2
f2 +₃ f1 = f0
f2 +₃ f2 = f1

neg₃ : F3 → F3
neg₃ f0 = f0
neg₃ f1 = f2
neg₃ f2 = f1

_-₃_ : F3 → F3 → F3
a -₃ b = a +₃ neg₃ b


------------------------------------------------------------------------
-- Literal field F3, with all core laws reduced to actual constructor
-- normal forms. This is a complete finite field, not just a symbolic
-- three-element group. These laws are generated exhaustively (3^n).
------------------------------------------------------------------------

_*₃_ : F3 → F3 → F3
f0 *₃ a = f0
f1 *₃ a = a
f2 *₃ f0 = f0
f2 *₃ f1 = f2
f2 *₃ f2 = f1

finiteFieldAddAssociative : ∀ a b c →
  (a +₃ b) +₃ c ≡ a +₃ (b +₃ c)
finiteFieldAddAssociative f0 f0 f0 = refl
finiteFieldAddAssociative f0 f0 f1 = refl
finiteFieldAddAssociative f0 f0 f2 = refl
finiteFieldAddAssociative f0 f1 f0 = refl
finiteFieldAddAssociative f0 f1 f1 = refl
finiteFieldAddAssociative f0 f1 f2 = refl
finiteFieldAddAssociative f0 f2 f0 = refl
finiteFieldAddAssociative f0 f2 f1 = refl
finiteFieldAddAssociative f0 f2 f2 = refl
finiteFieldAddAssociative f1 f0 f0 = refl
finiteFieldAddAssociative f1 f0 f1 = refl
finiteFieldAddAssociative f1 f0 f2 = refl
finiteFieldAddAssociative f1 f1 f0 = refl
finiteFieldAddAssociative f1 f1 f1 = refl
finiteFieldAddAssociative f1 f1 f2 = refl
finiteFieldAddAssociative f1 f2 f0 = refl
finiteFieldAddAssociative f1 f2 f1 = refl
finiteFieldAddAssociative f1 f2 f2 = refl
finiteFieldAddAssociative f2 f0 f0 = refl
finiteFieldAddAssociative f2 f0 f1 = refl
finiteFieldAddAssociative f2 f0 f2 = refl
finiteFieldAddAssociative f2 f1 f0 = refl
finiteFieldAddAssociative f2 f1 f1 = refl
finiteFieldAddAssociative f2 f1 f2 = refl
finiteFieldAddAssociative f2 f2 f0 = refl
finiteFieldAddAssociative f2 f2 f1 = refl
finiteFieldAddAssociative f2 f2 f2 = refl


finiteFieldAddCommutative : ∀ a b → a +₃ b ≡ b +₃ a
finiteFieldAddCommutative f0 f0 = refl
finiteFieldAddCommutative f0 f1 = refl
finiteFieldAddCommutative f0 f2 = refl
finiteFieldAddCommutative f1 f0 = refl
finiteFieldAddCommutative f1 f1 = refl
finiteFieldAddCommutative f1 f2 = refl
finiteFieldAddCommutative f2 f0 = refl
finiteFieldAddCommutative f2 f1 = refl
finiteFieldAddCommutative f2 f2 = refl


finiteFieldAddRightIdentity : ∀ a → a +₃ f0 ≡ a
finiteFieldAddRightIdentity f0 = refl
finiteFieldAddRightIdentity f1 = refl
finiteFieldAddRightIdentity f2 = refl


finiteFieldAddInverse : ∀ a → a +₃ neg₃ a ≡ f0
finiteFieldAddInverse f0 = refl
finiteFieldAddInverse f1 = refl
finiteFieldAddInverse f2 = refl


finiteFieldMulAssociative : ∀ a b c →
  (a *₃ b) *₃ c ≡ a *₃ (b *₃ c)
finiteFieldMulAssociative f0 f0 f0 = refl
finiteFieldMulAssociative f0 f0 f1 = refl
finiteFieldMulAssociative f0 f0 f2 = refl
finiteFieldMulAssociative f0 f1 f0 = refl
finiteFieldMulAssociative f0 f1 f1 = refl
finiteFieldMulAssociative f0 f1 f2 = refl
finiteFieldMulAssociative f0 f2 f0 = refl
finiteFieldMulAssociative f0 f2 f1 = refl
finiteFieldMulAssociative f0 f2 f2 = refl
finiteFieldMulAssociative f1 f0 f0 = refl
finiteFieldMulAssociative f1 f0 f1 = refl
finiteFieldMulAssociative f1 f0 f2 = refl
finiteFieldMulAssociative f1 f1 f0 = refl
finiteFieldMulAssociative f1 f1 f1 = refl
finiteFieldMulAssociative f1 f1 f2 = refl
finiteFieldMulAssociative f1 f2 f0 = refl
finiteFieldMulAssociative f1 f2 f1 = refl
finiteFieldMulAssociative f1 f2 f2 = refl
finiteFieldMulAssociative f2 f0 f0 = refl
finiteFieldMulAssociative f2 f0 f1 = refl
finiteFieldMulAssociative f2 f0 f2 = refl
finiteFieldMulAssociative f2 f1 f0 = refl
finiteFieldMulAssociative f2 f1 f1 = refl
finiteFieldMulAssociative f2 f1 f2 = refl
finiteFieldMulAssociative f2 f2 f0 = refl
finiteFieldMulAssociative f2 f2 f1 = refl
finiteFieldMulAssociative f2 f2 f2 = refl


finiteFieldMulCommutative : ∀ a b → a *₃ b ≡ b *₃ a
finiteFieldMulCommutative f0 f0 = refl
finiteFieldMulCommutative f0 f1 = refl
finiteFieldMulCommutative f0 f2 = refl
finiteFieldMulCommutative f1 f0 = refl
finiteFieldMulCommutative f1 f1 = refl
finiteFieldMulCommutative f1 f2 = refl
finiteFieldMulCommutative f2 f0 = refl
finiteFieldMulCommutative f2 f1 = refl
finiteFieldMulCommutative f2 f2 = refl


finiteFieldMulRightIdentity : ∀ a → a *₃ f1 ≡ a
finiteFieldMulRightIdentity f0 = refl
finiteFieldMulRightIdentity f1 = refl
finiteFieldMulRightIdentity f2 = refl


finiteFieldMulDistributive : ∀ a b c →
  a *₃ (b +₃ c) ≡ (a *₃ b) +₃ (a *₃ c)
finiteFieldMulDistributive f0 f0 f0 = refl
finiteFieldMulDistributive f0 f0 f1 = refl
finiteFieldMulDistributive f0 f0 f2 = refl
finiteFieldMulDistributive f0 f1 f0 = refl
finiteFieldMulDistributive f0 f1 f1 = refl
finiteFieldMulDistributive f0 f1 f2 = refl
finiteFieldMulDistributive f0 f2 f0 = refl
finiteFieldMulDistributive f0 f2 f1 = refl
finiteFieldMulDistributive f0 f2 f2 = refl
finiteFieldMulDistributive f1 f0 f0 = refl
finiteFieldMulDistributive f1 f0 f1 = refl
finiteFieldMulDistributive f1 f0 f2 = refl
finiteFieldMulDistributive f1 f1 f0 = refl
finiteFieldMulDistributive f1 f1 f1 = refl
finiteFieldMulDistributive f1 f1 f2 = refl
finiteFieldMulDistributive f1 f2 f0 = refl
finiteFieldMulDistributive f1 f2 f1 = refl
finiteFieldMulDistributive f1 f2 f2 = refl
finiteFieldMulDistributive f2 f0 f0 = refl
finiteFieldMulDistributive f2 f0 f1 = refl
finiteFieldMulDistributive f2 f0 f2 = refl
finiteFieldMulDistributive f2 f1 f0 = refl
finiteFieldMulDistributive f2 f1 f1 = refl
finiteFieldMulDistributive f2 f1 f2 = refl
finiteFieldMulDistributive f2 f2 f0 = refl
finiteFieldMulDistributive f2 f2 f1 = refl
finiteFieldMulDistributive f2 f2 f2 = refl


finiteFieldInverseOne : f1 *₃ f1 ≡ f1
finiteFieldInverseOne = refl

finiteFieldInverseTwo : f2 *₃ f2 ≡ f1
finiteFieldInverseTwo = refl

record V2 : Set where
  constructor v2
  field
    x y : F3
open V2 public

zero : V2
zero = v2 f0 f0

add : V2 → V2 → V2
add (v2 a b) (v2 c d) = v2 (a +₃ c) (b +₃ d)

sub : V2 → V2 → V2
sub (v2 a b) (v2 c d) = v2 (a -₃ c) (b -₃ d)

-- This is the ACTUAL cyclotomic companion map reduced modulo 3.
A : V2 → V2
A (v2 a b) = v2 (neg₃ b) (a -₃ b)

N : V2 → V2
N v = sub (A v) v


------------------------------------------------------------------------
-- Actual field-LINEAR representation, not merely a set C3 action.
-- Source A(v) = (-y,x-y) over F3 is additive and homogeneous.
-- All 3^4 pairs and all 3^3 scalar-vector cases reduce to refl.
------------------------------------------------------------------------

scalar : F3 → V2 → V2
scalar c (v2 a b) = v2 (c *₃ a) (c *₃ b)

Aadditive : ∀ v w → A (add v w) ≡ add (A v) (A w)
Aadditive (v2 f0 f0) (v2 f0 f0) = refl
Aadditive (v2 f0 f0) (v2 f0 f1) = refl
Aadditive (v2 f0 f0) (v2 f0 f2) = refl
Aadditive (v2 f0 f0) (v2 f1 f0) = refl
Aadditive (v2 f0 f0) (v2 f1 f1) = refl
Aadditive (v2 f0 f0) (v2 f1 f2) = refl
Aadditive (v2 f0 f0) (v2 f2 f0) = refl
Aadditive (v2 f0 f0) (v2 f2 f1) = refl
Aadditive (v2 f0 f0) (v2 f2 f2) = refl
Aadditive (v2 f0 f1) (v2 f0 f0) = refl
Aadditive (v2 f0 f1) (v2 f0 f1) = refl
Aadditive (v2 f0 f1) (v2 f0 f2) = refl
Aadditive (v2 f0 f1) (v2 f1 f0) = refl
Aadditive (v2 f0 f1) (v2 f1 f1) = refl
Aadditive (v2 f0 f1) (v2 f1 f2) = refl
Aadditive (v2 f0 f1) (v2 f2 f0) = refl
Aadditive (v2 f0 f1) (v2 f2 f1) = refl
Aadditive (v2 f0 f1) (v2 f2 f2) = refl
Aadditive (v2 f0 f2) (v2 f0 f0) = refl
Aadditive (v2 f0 f2) (v2 f0 f1) = refl
Aadditive (v2 f0 f2) (v2 f0 f2) = refl
Aadditive (v2 f0 f2) (v2 f1 f0) = refl
Aadditive (v2 f0 f2) (v2 f1 f1) = refl
Aadditive (v2 f0 f2) (v2 f1 f2) = refl
Aadditive (v2 f0 f2) (v2 f2 f0) = refl
Aadditive (v2 f0 f2) (v2 f2 f1) = refl
Aadditive (v2 f0 f2) (v2 f2 f2) = refl
Aadditive (v2 f1 f0) (v2 f0 f0) = refl
Aadditive (v2 f1 f0) (v2 f0 f1) = refl
Aadditive (v2 f1 f0) (v2 f0 f2) = refl
Aadditive (v2 f1 f0) (v2 f1 f0) = refl
Aadditive (v2 f1 f0) (v2 f1 f1) = refl
Aadditive (v2 f1 f0) (v2 f1 f2) = refl
Aadditive (v2 f1 f0) (v2 f2 f0) = refl
Aadditive (v2 f1 f0) (v2 f2 f1) = refl
Aadditive (v2 f1 f0) (v2 f2 f2) = refl
Aadditive (v2 f1 f1) (v2 f0 f0) = refl
Aadditive (v2 f1 f1) (v2 f0 f1) = refl
Aadditive (v2 f1 f1) (v2 f0 f2) = refl
Aadditive (v2 f1 f1) (v2 f1 f0) = refl
Aadditive (v2 f1 f1) (v2 f1 f1) = refl
Aadditive (v2 f1 f1) (v2 f1 f2) = refl
Aadditive (v2 f1 f1) (v2 f2 f0) = refl
Aadditive (v2 f1 f1) (v2 f2 f1) = refl
Aadditive (v2 f1 f1) (v2 f2 f2) = refl
Aadditive (v2 f1 f2) (v2 f0 f0) = refl
Aadditive (v2 f1 f2) (v2 f0 f1) = refl
Aadditive (v2 f1 f2) (v2 f0 f2) = refl
Aadditive (v2 f1 f2) (v2 f1 f0) = refl
Aadditive (v2 f1 f2) (v2 f1 f1) = refl
Aadditive (v2 f1 f2) (v2 f1 f2) = refl
Aadditive (v2 f1 f2) (v2 f2 f0) = refl
Aadditive (v2 f1 f2) (v2 f2 f1) = refl
Aadditive (v2 f1 f2) (v2 f2 f2) = refl
Aadditive (v2 f2 f0) (v2 f0 f0) = refl
Aadditive (v2 f2 f0) (v2 f0 f1) = refl
Aadditive (v2 f2 f0) (v2 f0 f2) = refl
Aadditive (v2 f2 f0) (v2 f1 f0) = refl
Aadditive (v2 f2 f0) (v2 f1 f1) = refl
Aadditive (v2 f2 f0) (v2 f1 f2) = refl
Aadditive (v2 f2 f0) (v2 f2 f0) = refl
Aadditive (v2 f2 f0) (v2 f2 f1) = refl
Aadditive (v2 f2 f0) (v2 f2 f2) = refl
Aadditive (v2 f2 f1) (v2 f0 f0) = refl
Aadditive (v2 f2 f1) (v2 f0 f1) = refl
Aadditive (v2 f2 f1) (v2 f0 f2) = refl
Aadditive (v2 f2 f1) (v2 f1 f0) = refl
Aadditive (v2 f2 f1) (v2 f1 f1) = refl
Aadditive (v2 f2 f1) (v2 f1 f2) = refl
Aadditive (v2 f2 f1) (v2 f2 f0) = refl
Aadditive (v2 f2 f1) (v2 f2 f1) = refl
Aadditive (v2 f2 f1) (v2 f2 f2) = refl
Aadditive (v2 f2 f2) (v2 f0 f0) = refl
Aadditive (v2 f2 f2) (v2 f0 f1) = refl
Aadditive (v2 f2 f2) (v2 f0 f2) = refl
Aadditive (v2 f2 f2) (v2 f1 f0) = refl
Aadditive (v2 f2 f2) (v2 f1 f1) = refl
Aadditive (v2 f2 f2) (v2 f1 f2) = refl
Aadditive (v2 f2 f2) (v2 f2 f0) = refl
Aadditive (v2 f2 f2) (v2 f2 f1) = refl
Aadditive (v2 f2 f2) (v2 f2 f2) = refl

Ahomogeneous : ∀ t v → A (scalar t v) ≡ scalar t (A v)
Ahomogeneous f0 (v2 f0 f0) = refl
Ahomogeneous f0 (v2 f0 f1) = refl
Ahomogeneous f0 (v2 f0 f2) = refl
Ahomogeneous f0 (v2 f1 f0) = refl
Ahomogeneous f0 (v2 f1 f1) = refl
Ahomogeneous f0 (v2 f1 f2) = refl
Ahomogeneous f0 (v2 f2 f0) = refl
Ahomogeneous f0 (v2 f2 f1) = refl
Ahomogeneous f0 (v2 f2 f2) = refl
Ahomogeneous f1 (v2 f0 f0) = refl
Ahomogeneous f1 (v2 f0 f1) = refl
Ahomogeneous f1 (v2 f0 f2) = refl
Ahomogeneous f1 (v2 f1 f0) = refl
Ahomogeneous f1 (v2 f1 f1) = refl
Ahomogeneous f1 (v2 f1 f2) = refl
Ahomogeneous f1 (v2 f2 f0) = refl
Ahomogeneous f1 (v2 f2 f1) = refl
Ahomogeneous f1 (v2 f2 f2) = refl
Ahomogeneous f2 (v2 f0 f0) = refl
Ahomogeneous f2 (v2 f0 f1) = refl
Ahomogeneous f2 (v2 f0 f2) = refl
Ahomogeneous f2 (v2 f1 f0) = refl
Ahomogeneous f2 (v2 f1 f1) = refl
Ahomogeneous f2 (v2 f1 f2) = refl
Ahomogeneous f2 (v2 f2 f0) = refl
Ahomogeneous f2 (v2 f2 f1) = refl
Ahomogeneous f2 (v2 f2 f2) = refl

-- All nine finite cases are definitionally decidable.
cubeIsIdentity : ∀ v → A (A (A v)) ≡ v
cubeIsIdentity (v2 f0 f0) = refl
cubeIsIdentity (v2 f0 f1) = refl
cubeIsIdentity (v2 f0 f2) = refl
cubeIsIdentity (v2 f1 f0) = refl
cubeIsIdentity (v2 f1 f1) = refl
cubeIsIdentity (v2 f1 f2) = refl
cubeIsIdentity (v2 f2 f0) = refl
cubeIsIdentity (v2 f2 f1) = refl
cubeIsIdentity (v2 f2 f2) = refl

nilpotentSquareZero : ∀ v → N (N v) ≡ zero
nilpotentSquareZero (v2 f0 f0) = refl
nilpotentSquareZero (v2 f0 f1) = refl
nilpotentSquareZero (v2 f0 f2) = refl
nilpotentSquareZero (v2 f1 f0) = refl
nilpotentSquareZero (v2 f1 f1) = refl
nilpotentSquareZero (v2 f1 f2) = refl
nilpotentSquareZero (v2 f2 f0) = refl
nilpotentSquareZero (v2 f2 f1) = refl
nilpotentSquareZero (v2 f2 f2) = refl

nilpotentIsNonzero : N (v2 f1 f0) ≡ zero → ⊥
nilpotentIsNonzero ()

fixedGenerator : V2
fixedGenerator = v2 f1 f2

fixedGeneratorIsNonzero : fixedGenerator ≡ zero → ⊥
fixedGeneratorIsNonzero ()

fixedGeneratorReallyFixed : A fixedGenerator ≡ fixedGenerator
fixedGeneratorReallyFixed = refl

-- A genuine C3 representation on precisely this finite vector carrier.
act : C3.C3 → V2 → V2
act C3.c0 v = v
act C3.c1 v = A v
act C3.c2 v = A (A v)

actIdentity : ∀ v → act C3.c0 v ≡ v
actIdentity v = refl

actComposition : ∀ a b v →
  act (C3._∙_ a b) v ≡ act a (act b v)
actComposition C3.c0 b v = refl
actComposition C3.c1 C3.c0 v = refl
actComposition C3.c1 C3.c1 v = refl
actComposition C3.c1 C3.c2 v = sym (cubeIsIdentity v)
actComposition C3.c2 C3.c0 v = refl
actComposition C3.c2 C3.c1 v = sym (cubeIsIdentity v)
actComposition C3.c2 C3.c2 v = sym (cubeIsIdentity (A v))

-- The nontrivial difference is intrinsic to the SAME rational
-- companion operator reduced modulo 3; no dimension-count
-- coincidence, homology torsion, or Dirac/Monster promotion.
