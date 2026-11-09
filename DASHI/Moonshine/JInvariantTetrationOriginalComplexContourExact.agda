module DASHI.Moonshine.JInvariantTetrationOriginalComplexContourExact where

-- Exact same-source contour transport on the existing constructed
-- complex carrier. This is conditional on F(z+1)=exp(F(z)).
-- It does not assume or construct Kneser's entire analytic extension.

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex

private
  variable A B : Set

cong : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record OriginalComplexTetrationChart : Set₁ where
  field
    complexPackage : Complex.ConstructedComplexPackage
  private
    R = Real.real (Complex.realPackage complexPackage)
  field
    Height : Set
    advance : Height → Height
    tetration : Height → Complex.ComplexPair R
    originalTetrationEquation :
      (z : Height) →
      tetration (advance z) ≡
      Complex.expC (Complex.complexExponential complexPackage)
        (tetration z)

open OriginalComplexTetrationChart public

private
  module Local (C : OriginalComplexTetrationChart) where
    private
      P = complexPackage C
      R = Real.real (Complex.realPackage P)
      CE = Complex.complexExponential P

    modulusSquaredAt : Height C → Real.Real R
    modulusSquaredAt z = Complex.normSqC (tetration C z)

    nextModulusSquared :
      (z : Height C) →
      modulusSquaredAt (advance C z) ≡
      Complex.normSqC (Complex.expC CE (tetration C z))
    nextModulusSquared z =
      cong Complex.normSqC (originalTetrationEquation C z)

    modulusLevel : Real.Real R → Height C → Set
    modulusLevel radius z = modulusSquaredAt z ≡ radius

    nextModulusLevel :
      (radius : Real.Real R) → (z : Height C) →
      modulusLevel radius (advance C z) ≡
      (Complex.normSqC (Complex.expC CE (tetration C z)) ≡ radius)
    nextModulusLevel radius z
      rewrite nextModulusSquared z = refl

    nextModulusFromCartesian :
      (z : Height C) →
      modulusSquaredAt (advance C z) ≡
      Complex.normSqC
        (Complex.complex
          (Real._*_ R
             (Real.exp (Real.exponential (Complex.realPackage P))
               (Complex.re (tetration C z)))
             (Complex.cos CE (Complex.im (tetration C z))))
          (Real._*_ R
             (Real.exp (Real.exponential (Complex.realPackage P))
               (Complex.re (tetration C z)))
             (Complex.sin CE (Complex.im (tetration C z)))))
    nextModulusFromCartesian z
      rewrite originalTetrationEquation C z
            | Complex.expCartesian CE
                (Complex.re (tetration C z))
                (Complex.im (tetration C z)) = refl

    -- Argument contours are branch-indexed. The original complex package
    -- provides exp but not a globally single-valued argument.
    record OriginalPhaseChart : Set₁ where
      field
        Phase : Set
        phase : Complex.ComplexPair R → Phase

    nextPhase :
      (O : OriginalPhaseChart) → (z : Height C) →
      OriginalPhaseChart.phase O (tetration C (advance C z)) ≡
      OriginalPhaseChart.phase O (Complex.expC CE (tetration C z))
    nextPhase O z =
      cong (OriginalPhaseChart.phase O) (originalTetrationEquation C z)

open Local public
