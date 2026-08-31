module DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact where

------------------------------------------------------------------------
-- FINITE SCHRODINGER FUNCTION MODULE ON X6 = F3^6
--
-- This owner turns the generator-level Weyl model into an actual function
-- carrier V = X6 -> Q(zeta_3), with pointwise additive/scalar structure and
-- literal translation/modulation actions.  It deliberately does not yet
-- assert irreducibility: invariant-subspace projection and nonzero scalar
-- inversion remain separate theorem obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergPermutationExact as Perm

------------------------------------------------------------------------
-- 1. Exact additive/scalar structure on Q(zeta_3).
------------------------------------------------------------------------

addC3 : C3.Cyclotomic3 → C3.Cyclotomic3 → C3.Cyclotomic3
addC3 (C3.cyclotomic3 a b) (C3.cyclotomic3 c d) =
  C3.cyclotomic3 (a + c) (b + d)

scaleC3 : ℚ → C3.Cyclotomic3 → C3.Cyclotomic3
scaleC3 r (C3.cyclotomic3 a b) = C3.cyclotomic3 (r * a) (r * b)

negC3 : C3.Cyclotomic3 → C3.Cyclotomic3
negC3 (C3.cyclotomic3 a b) = C3.cyclotomic3 (0ℚ - a) (0ℚ - b)

phase : Trit → C3.Cyclotomic3
phase zer = C3.one
phase pos = C3.zeta
phase neg = C3.zetaSquared

------------------------------------------------------------------------
-- 2. Function carrier and pointwise module operations.
------------------------------------------------------------------------

SchrodingerFunction : Set
SchrodingerFunction = H.X6 → C3.Cyclotomic3

zeroFunction : SchrodingerFunction
zeroFunction x = C3.zero

addFunction : SchrodingerFunction → SchrodingerFunction → SchrodingerFunction
addFunction f g x = addC3 (f x) (g x)

scaleFunction : ℚ → SchrodingerFunction → SchrodingerFunction
scaleFunction r f x = scaleC3 r (f x)

cyclotomicScaleFunction :
  C3.Cyclotomic3 → SchrodingerFunction → SchrodingerFunction
cyclotomicScaleFunction a f x = C3.multiply a (f x)

------------------------------------------------------------------------
-- 3. Literal translation and modulation actions.
------------------------------------------------------------------------

translationAction : H.Axis6 → SchrodingerFunction → SchrodingerFunction
translationAction axis f x = f (H.translateInverse axis x)

modulationAction : H.Axis6 → SchrodingerFunction → SchrodingerFunction
modulationAction axis f x =
  C3.multiply (phase (H.modulationExponent axis x)) (f x)

translationActionInverse :
  (axis : H.Axis6) → (f : SchrodingerFunction) → (x : H.X6) →
  translationAction axis (translationAction axis f) (H.translate axis (H.translate axis x))
  ≡ f x
translationActionInverse axis f x
  rewrite Perm.translateInverseAfterTranslate axis (H.translate axis x)
        | Perm.translateInverseAfterTranslate axis x = refl

------------------------------------------------------------------------
-- 4. Delta-line carrier.
------------------------------------------------------------------------

tritEqual : Trit → Trit → Bool
tritEqual neg neg = true
tritEqual neg zer = false
tritEqual neg pos = false
tritEqual zer neg = false
tritEqual zer zer = true
tritEqual zer pos = false
tritEqual pos neg = false
tritEqual pos zer = false
tritEqual pos pos = true

_and_ : Bool → Bool → Bool
false and b = false
true and b = b

x6Equal : H.X6 → H.X6 → Bool
x6Equal (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5) =
  tritEqual a0 b0 and
  (tritEqual a1 b1 and
  (tritEqual a2 b2 and
  (tritEqual a3 b3 and
  (tritEqual a4 b4 and tritEqual a5 b5))))

delta : H.X6 → SchrodingerFunction
delta selected x with x6Equal selected x
... | true = C3.one
... | false = C3.zero

------------------------------------------------------------------------
-- 5. Invariant-subspace interface.  This is a Q(zeta_3)-linear subspace,
-- not merely a rational subspace.  Arbitrary coordinate selectors are still
-- absent; later Fourier projector ownership must derive them from modulation.
------------------------------------------------------------------------

record HeisenbergInvariantSubspace (Member : SchrodingerFunction → Set) : Set where
  constructor heisenbergInvariantSubspace
  field
    containsZero : Member zeroFunction
    closedUnderAddition :
      (f g : SchrodingerFunction) → Member f → Member g → Member (addFunction f g)
    closedUnderRationalScaling :
      (r : ℚ) → (f : SchrodingerFunction) → Member f → Member (scaleFunction r f)
    closedUnderCyclotomicScaling :
      (a : C3.Cyclotomic3) → (f : SchrodingerFunction) → Member f →
      Member (cyclotomicScaleFunction a f)
    closedUnderTranslation :
      (axis : H.Axis6) → (f : SchrodingerFunction) → Member f →
      Member (translationAction axis f)
    closedUnderModulation :
      (axis : H.Axis6) → (f : SchrodingerFunction) → Member f →
      Member (modulationAction axis f)
open HeisenbergInvariantSubspace public

record SchrodingerFunctionModuleBoundary : Set where
  constructor schrodingerFunctionModuleBoundary
  field
    exactFunctionCarrierConstructed : Bool
    cyclotomicLinearSubspaceInterfaceConstructed : Bool
    translationActionConstructed : Bool
    modulationActionConstructed : Bool
    modulationFourierProjectorsConstructedHere : Bool
    nonzeroCyclotomicScalarInversionConstructedHere : Bool
    schrodingerIrreducibilityProvedHere : Bool
open SchrodingerFunctionModuleBoundary public

canonicalSchrodingerFunctionModuleBoundary : SchrodingerFunctionModuleBoundary
canonicalSchrodingerFunctionModuleBoundary =
  schrodingerFunctionModuleBoundary true true true true false false false
