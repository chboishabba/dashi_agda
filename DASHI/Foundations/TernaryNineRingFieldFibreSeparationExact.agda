module DASHI.Foundations.TernaryNineRingFieldFibreSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Rudolf Lidl and Harald Niederreiter,
-- "Finite Fields", Encyclopedia of Mathematics and its Applications 20,
-- Cambridge University Press, 2nd ed., 1997.
-- DOI: 10.1017/CBO9780511525926.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- ARISTOTLE / HARMONIC CONTEXT
--
-- The supplied Tesla369/Frobenius development places Z/9-style digital-root
-- arithmetic beside characteristic-three Frobenius phenomena.  This module
-- makes the distinction concrete: cyclic C9 and quadratic F9 both have nine
-- states and maps to a ternary core, but they are not the same algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase9
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Separation

F3 : Set
F3 = Base.TriTruth

f3Zero : F3
f3Zero = Base.tri-low

f3One : F3
f3One = Base.tri-mid

f3Two : F3
f3Two = Base.tri-high

f3Add : F3 → F3 → F3
f3Add = Base.triXor

f3Neg : F3 → F3
f3Neg Base.tri-low = Base.tri-low
f3Neg Base.tri-mid = Base.tri-high
f3Neg Base.tri-high = Base.tri-mid

f3Sub : F3 → F3 → F3
f3Sub x y = f3Add x (f3Neg y)

f3Mul : F3 → F3 → F3
f3Mul Base.tri-low y = Base.tri-low
f3Mul Base.tri-mid y = y
f3Mul Base.tri-high Base.tri-low = Base.tri-low
f3Mul Base.tri-high Base.tri-mid = Base.tri-high
f3Mul Base.tri-high Base.tri-high = Base.tri-mid

f3Inv : F3 → F3
f3Inv Base.tri-low = Base.tri-low
f3Inv Base.tri-mid = Base.tri-mid
f3Inv Base.tri-high = Base.tri-high

quadraticNoRoot0 : f3Add (f3Mul Base.tri-low Base.tri-low) f3One ≡ f3Zero → ⊥
quadraticNoRoot0 ()

quadraticNoRoot1 : f3Add (f3Mul Base.tri-mid Base.tri-mid) f3One ≡ f3Zero → ⊥
quadraticNoRoot1 ()

quadraticNoRoot2 : f3Add (f3Mul Base.tri-high Base.tri-high) f3One ≡ f3Zero → ⊥
quadraticNoRoot2 ()

------------------------------------------------------------------------
-- F9 = F3[alpha]/(alpha^2+1), realized on the existing 3 x 3 carrier.
------------------------------------------------------------------------

F9 : Set
F9 = Phase9.PhaseQuotient9

f9Zero : F9
f9Zero = f3Zero , f3Zero

f9One : F9
f9One = f3One , f3Zero

f9Add : F9 → F9 → F9
f9Add (a , b) (c , d) = f3Add a c , f3Add b d

f9Mul : F9 → F9 → F9
f9Mul (a , b) (c , d) =
  f3Sub (f3Mul a c) (f3Mul b d) ,
  f3Add (f3Mul a d) (f3Mul b c)

f9Conjugate : F9 → F9
f9Conjugate (a , b) = a , f3Neg b

f9Cube : F9 → F9
f9Cube x = f9Mul (f9Mul x x) x

f9CubeIsFrobenius : (x : F9) → f9Cube x ≡ f9Conjugate x
f9CubeIsFrobenius (Base.tri-low , Base.tri-low) = refl
f9CubeIsFrobenius (Base.tri-low , Base.tri-mid) = refl
f9CubeIsFrobenius (Base.tri-low , Base.tri-high) = refl
f9CubeIsFrobenius (Base.tri-mid , Base.tri-low) = refl
f9CubeIsFrobenius (Base.tri-mid , Base.tri-mid) = refl
f9CubeIsFrobenius (Base.tri-mid , Base.tri-high) = refl
f9CubeIsFrobenius (Base.tri-high , Base.tri-low) = refl
f9CubeIsFrobenius (Base.tri-high , Base.tri-mid) = refl
f9CubeIsFrobenius (Base.tri-high , Base.tri-high) = refl

f9FrobeniusTwo : (x : F9) → f9Conjugate (f9Conjugate x) ≡ x
f9FrobeniusTwo (Base.tri-low , Base.tri-low) = refl
f9FrobeniusTwo (Base.tri-low , Base.tri-mid) = refl
f9FrobeniusTwo (Base.tri-low , Base.tri-high) = refl
f9FrobeniusTwo (Base.tri-mid , Base.tri-low) = refl
f9FrobeniusTwo (Base.tri-mid , Base.tri-mid) = refl
f9FrobeniusTwo (Base.tri-mid , Base.tri-high) = refl
f9FrobeniusTwo (Base.tri-high , Base.tri-low) = refl
f9FrobeniusTwo (Base.tri-high , Base.tri-mid) = refl
f9FrobeniusTwo (Base.tri-high , Base.tri-high) = refl

f9Norm : F9 → F3
f9Norm (a , b) = f3Add (f3Mul a a) (f3Mul b b)

f9Inverse : F9 → F9
f9Inverse (a , b) =
  f3Mul a (f3Inv (f9Norm (a , b))) ,
  f3Mul (f3Neg b) (f3Inv (f9Norm (a , b)))

NonzeroF9 : F9 → Set
NonzeroF9 x = x ≡ f9Zero → ⊥

f9RightInverseNonzero :
  (x : F9) → NonzeroF9 x → f9Mul x (f9Inverse x) ≡ f9One
f9RightInverseNonzero (Base.tri-low , Base.tri-low) nonzero with nonzero refl
... | ()
f9RightInverseNonzero (Base.tri-low , Base.tri-mid) nonzero = refl
f9RightInverseNonzero (Base.tri-low , Base.tri-high) nonzero = refl
f9RightInverseNonzero (Base.tri-mid , Base.tri-low) nonzero = refl
f9RightInverseNonzero (Base.tri-mid , Base.tri-mid) nonzero = refl
f9RightInverseNonzero (Base.tri-mid , Base.tri-high) nonzero = refl
f9RightInverseNonzero (Base.tri-high , Base.tri-low) nonzero = refl
f9RightInverseNonzero (Base.tri-high , Base.tri-mid) nonzero = refl
f9RightInverseNonzero (Base.tri-high , Base.tri-high) nonzero = refl

------------------------------------------------------------------------
-- Frobenius fixed field and trace-derived retraction F9 -> F3.
------------------------------------------------------------------------

f3Embed : F3 → F9
f3Embed a = a , f3Zero

f3Project : F9 → F3
f3Project = proj₁

projectEmbed : (a : F3) → f3Project (f3Embed a) ≡ a
projectEmbed Base.tri-low = refl
projectEmbed Base.tri-mid = refl
projectEmbed Base.tri-high = refl

embedFixedByFrobenius :
  (a : F3) → f9Conjugate (f3Embed a) ≡ f3Embed a
embedFixedByFrobenius Base.tri-low = refl
embedFixedByFrobenius Base.tri-mid = refl
embedFixedByFrobenius Base.tri-high = refl

data FrobeniusFixed : F9 → Set where
  baseFixed : (a : F3) → FrobeniusFixed (f3Embed a)

frobeniusFixedClassification :
  (x : F9) → f9Conjugate x ≡ x → FrobeniusFixed x
frobeniusFixedClassification (Base.tri-low , Base.tri-low) equality = baseFixed Base.tri-low
frobeniusFixedClassification (Base.tri-low , Base.tri-mid) ()
frobeniusFixedClassification (Base.tri-low , Base.tri-high) ()
frobeniusFixedClassification (Base.tri-mid , Base.tri-low) equality = baseFixed Base.tri-mid
frobeniusFixedClassification (Base.tri-mid , Base.tri-mid) ()
frobeniusFixedClassification (Base.tri-mid , Base.tri-high) ()
frobeniusFixedClassification (Base.tri-high , Base.tri-low) equality = baseFixed Base.tri-high
frobeniusFixedClassification (Base.tri-high , Base.tri-mid) ()
frobeniusFixedClassification (Base.tri-high , Base.tri-high) ()

f9Trace : F9 → F9
f9Trace x = f9Add x (f9Conjugate x)

traceLandsInBase : (x : F9) → proj₂ (f9Trace x) ≡ f3Zero
traceLandsInBase (Base.tri-low , Base.tri-low) = refl
traceLandsInBase (Base.tri-low , Base.tri-mid) = refl
traceLandsInBase (Base.tri-low , Base.tri-high) = refl
traceLandsInBase (Base.tri-mid , Base.tri-low) = refl
traceLandsInBase (Base.tri-mid , Base.tri-mid) = refl
traceLandsInBase (Base.tri-mid , Base.tri-high) = refl
traceLandsInBase (Base.tri-high , Base.tri-low) = refl
traceLandsInBase (Base.tri-high , Base.tri-mid) = refl
traceLandsInBase (Base.tri-high , Base.tri-high) = refl

frobeniusTraceRetract : F9 → F3
frobeniusTraceRetract x = f3Mul f3Two (proj₁ (f9Trace x))

traceRetractIsFirstCoordinate :
  (x : F9) → frobeniusTraceRetract x ≡ f3Project x
traceRetractIsFirstCoordinate (Base.tri-low , Base.tri-low) = refl
traceRetractIsFirstCoordinate (Base.tri-low , Base.tri-mid) = refl
traceRetractIsFirstCoordinate (Base.tri-low , Base.tri-high) = refl
traceRetractIsFirstCoordinate (Base.tri-mid , Base.tri-low) = refl
traceRetractIsFirstCoordinate (Base.tri-mid , Base.tri-mid) = refl
traceRetractIsFirstCoordinate (Base.tri-mid , Base.tri-high) = refl
traceRetractIsFirstCoordinate (Base.tri-high , Base.tri-low) = refl
traceRetractIsFirstCoordinate (Base.tri-high , Base.tri-mid) = refl
traceRetractIsFirstCoordinate (Base.tri-high , Base.tri-high) = refl

traceRetractAfterEmbed :
  (a : F3) → frobeniusTraceRetract (f3Embed a) ≡ a
traceRetractAfterEmbed Base.tri-low = refl
traceRetractAfterEmbed Base.tri-mid = refl
traceRetractAfterEmbed Base.tri-high = refl

------------------------------------------------------------------------
-- The cyclic nine has a different 9 -> 3 projection.
------------------------------------------------------------------------

nonaryMod3 : Base.NonaryTruth → F3
nonaryMod3 Base.non-0 = Base.tri-low
nonaryMod3 Base.non-1 = Base.tri-mid
nonaryMod3 Base.non-2 = Base.tri-high
nonaryMod3 Base.non-3 = Base.tri-low
nonaryMod3 Base.non-4 = Base.tri-mid
nonaryMod3 Base.non-5 = Base.tri-high
nonaryMod3 Base.non-6 = Base.tri-low
nonaryMod3 Base.non-7 = Base.tri-mid
nonaryMod3 Base.non-8 = Base.tri-high

nonaryZeroFibre3 :
  nonaryMod3 Base.non-0 ≡ nonaryMod3 Base.non-3
  × nonaryMod3 Base.non-3 ≡ nonaryMod3 Base.non-6
nonaryZeroFibre3 = refl , refl

nonaryOneFibre3 :
  nonaryMod3 Base.non-1 ≡ nonaryMod3 Base.non-4
  × nonaryMod3 Base.non-4 ≡ nonaryMod3 Base.non-7
nonaryOneFibre3 = refl , refl

nonaryTwoFibre3 :
  nonaryMod3 Base.non-2 ≡ nonaryMod3 Base.non-5
  × nonaryMod3 Base.non-5 ≡ nonaryMod3 Base.non-8
nonaryTwoFibre3 = refl , refl

noAdditiveGroupIdentificationWithC9 :
  Separation.Q9NonaryGroupIsomorphism → ⊥
noAdditiveGroupIdentificationWithC9 = Separation.q9NonaryGroupIsomorphismImpossible

record TernaryNineFibreBoundary : Set where
  field
    cyclicNineToThreeProjectionConstructed : Bool
    quadraticNineToThreeRetractionConstructed : Bool
    frobeniusCubeComputed : Bool
    frobeniusFixedFieldClassified : Bool
    nonzeroMultiplicativeInversesConstructed : Bool
    cyclicAndFieldNineIdentified : Bool

canonicalTernaryNineFibreBoundary : TernaryNineFibreBoundary
canonicalTernaryNineFibreBoundary =
  record
    { cyclicNineToThreeProjectionConstructed = true
    ; quadraticNineToThreeRetractionConstructed = true
    ; frobeniusCubeComputed = true
    ; frobeniusFixedFieldClassified = true
    ; nonzeroMultiplicativeInversesConstructed = true
    ; cyclicAndFieldNineIdentified = false
    }
