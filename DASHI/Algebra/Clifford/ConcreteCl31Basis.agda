module DASHI.Algebra.Clifford.ConcreteCl31Basis where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Concrete 16-blade basis for Cl(3,1).
--
-- Convention:
--   e0² = -1
--   e1² = e2² = e3² = +1
--
-- This module replaces the unit-carrier placeholder at the basis level. It
-- gives a genuinely nontrivial finite carrier and an exact left action of the
-- four Clifford generators on all sixteen blades. Linear extension to full
-- multivectors and the universal-property adapter remain separate layers.

data Sign : Set where
  plus minus : Sign

negSign : Sign → Sign
negSign plus = minus
negSign minus = plus

data Generator : Set where
  e0 e1 e2 e3 : Generator

data Blade : Set where
  one : Blade
  b0 b1 b2 b3 : Blade
  b01 b02 b03 b12 b13 b23 : Blade
  b012 b013 b023 b123 : Blade
  b0123 : Blade

SignedBlade : Set
SignedBlade = Sign × Blade

negSigned : SignedBlade → SignedBlade
negSigned (s , b) = negSign s , b

bladeOf : Generator → Blade
bladeOf e0 = b0
bladeOf e1 = b1
bladeOf e2 = b2
bladeOf e3 = b3

metricSign : Generator → Sign
metricSign e0 = minus
metricSign e1 = plus
metricSign e2 = plus
metricSign e3 = plus

------------------------------------------------------------------------
-- Exact left multiplication by generators.

genMul : Generator → Blade → SignedBlade

genMul e0 one = plus , b0
genMul e0 b0 = minus , one
genMul e0 b1 = plus , b01
genMul e0 b2 = plus , b02
genMul e0 b3 = plus , b03
genMul e0 b01 = minus , b1
genMul e0 b02 = minus , b2
genMul e0 b03 = minus , b3
genMul e0 b12 = plus , b012
genMul e0 b13 = plus , b013
genMul e0 b23 = plus , b023
genMul e0 b012 = minus , b12
genMul e0 b013 = minus , b13
genMul e0 b023 = minus , b23
genMul e0 b123 = plus , b0123
genMul e0 b0123 = minus , b123

genMul e1 one = plus , b1
genMul e1 b0 = minus , b01
genMul e1 b1 = plus , one
genMul e1 b2 = plus , b12
genMul e1 b3 = plus , b13
genMul e1 b01 = minus , b0
genMul e1 b02 = minus , b012
genMul e1 b03 = minus , b013
genMul e1 b12 = plus , b2
genMul e1 b13 = plus , b3
genMul e1 b23 = plus , b123
genMul e1 b012 = minus , b02
genMul e1 b013 = minus , b03
genMul e1 b023 = minus , b0123
genMul e1 b123 = plus , b23
genMul e1 b0123 = minus , b023

genMul e2 one = plus , b2
genMul e2 b0 = minus , b02
genMul e2 b1 = minus , b12
genMul e2 b2 = plus , one
genMul e2 b3 = plus , b23
genMul e2 b01 = plus , b012
genMul e2 b02 = minus , b0
genMul e2 b03 = minus , b023
genMul e2 b12 = minus , b1
genMul e2 b13 = minus , b123
genMul e2 b23 = plus , b3
genMul e2 b012 = plus , b01
genMul e2 b013 = plus , b0123
genMul e2 b023 = minus , b03
genMul e2 b123 = minus , b13
genMul e2 b0123 = plus , b013

genMul e3 one = plus , b3
genMul e3 b0 = minus , b03
genMul e3 b1 = minus , b13
genMul e3 b2 = minus , b23
genMul e3 b3 = plus , one
genMul e3 b01 = plus , b013
genMul e3 b02 = plus , b023
genMul e3 b03 = minus , b0
genMul e3 b12 = plus , b123
genMul e3 b13 = minus , b1
genMul e3 b23 = minus , b2
genMul e3 b012 = minus , b0123
genMul e3 b013 = plus , b01
genMul e3 b023 = plus , b02
genMul e3 b123 = plus , b12
genMul e3 b0123 = minus , b012

------------------------------------------------------------------------
-- Generator relations.

generatorSquare :
  ∀ g → genMul g (bladeOf g) ≡ (metricSign g , one)
generatorSquare e0 = refl
generatorSquare e1 = refl
generatorSquare e2 = refl
generatorSquare e3 = refl

-- Explicit ordered inequality witness, avoiding a decision-procedure layer.
data Apart : Generator → Generator → Set where
  a01 : Apart e0 e1
  a02 : Apart e0 e2
  a03 : Apart e0 e3
  a10 : Apart e1 e0
  a12 : Apart e1 e2
  a13 : Apart e1 e3
  a20 : Apart e2 e0
  a21 : Apart e2 e1
  a23 : Apart e2 e3
  a30 : Apart e3 e0
  a31 : Apart e3 e1
  a32 : Apart e3 e2

generatorAnticommutes :
  ∀ {g h} →
  Apart g h →
  genMul g (bladeOf h) ≡ negSigned (genMul h (bladeOf g))
generatorAnticommutes a01 = refl
generatorAnticommutes a02 = refl
generatorAnticommutes a03 = refl
generatorAnticommutes a10 = refl
generatorAnticommutes a12 = refl
generatorAnticommutes a13 = refl
generatorAnticommutes a20 = refl
generatorAnticommutes a21 = refl
generatorAnticommutes a23 = refl
generatorAnticommutes a30 = refl
generatorAnticommutes a31 = refl
generatorAnticommutes a32 = refl

bladeCount : Nat
bladeCount = 16

record ConcreteCl31Basis : Set where
  field
    Basis : Set
    basisCount : Nat
    GeneratorCarrier : Set
    generatorBlade : GeneratorCarrier → Basis
    generatorMetric : GeneratorCarrier → Sign
    leftGeneratorMultiply : GeneratorCarrier → Basis → SignedBlade
    squaresToMetric :
      ∀ g →
      leftGeneratorMultiply g (generatorBlade g)
      ≡ (generatorMetric g , one)
    distinctGeneratorsAnticommute :
      ∀ {g h} →
      Apart g h →
      leftGeneratorMultiply g (generatorBlade h)
      ≡ negSigned (leftGeneratorMultiply h (generatorBlade g))

open ConcreteCl31Basis public

canonicalConcreteCl31Basis : ConcreteCl31Basis
canonicalConcreteCl31Basis =
  record
    { Basis = Blade
    ; basisCount = bladeCount
    ; GeneratorCarrier = Generator
    ; generatorBlade = bladeOf
    ; generatorMetric = metricSign
    ; leftGeneratorMultiply = genMul
    ; squaresToMetric = generatorSquare
    ; distinctGeneratorsAnticommute = generatorAnticommutes
    }

------------------------------------------------------------------------
-- Honest next boundary.

record ConcreteCl31LinearExtensionBoundary : Set₁ where
  field
    Scalar : Set
    Multivector : Set
    embedBlade : Blade → Multivector
    extendSignedBlade : SignedBlade → Multivector
    multiply : Multivector → Multivector → Multivector
    basisActionAgrees : Set
    multiplicationAssociative : Set
    scalarEmbeddingCentral : Set
    universalProperty : Set
