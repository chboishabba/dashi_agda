module DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact where

------------------------------------------------------------------------
-- PREFERRED BISHOP EISENSTEIN MODULARITY COMPILER ON Z^2 \ {0}
--
-- This repairs two representation details at once:
--
--   * the index carrier is the actual punctured lattice used by G_k;
--   * normalization is explicit.  A raw lattice G_4/G_6 value is not silently
--     identified with the normalized q-series E_4/E_6.
--
-- Once a concrete punctured absolute sum supplies the standard reindex/factor
-- laws, the existing SL2(Z) bijection gives raw modularity.  Any normalization
-- commuting with the weight action inherits that modularity.  Therefore the
-- eventual Fourier theorem only has to identify q-series E4/E6 with the
-- EXPLICITLY NORMALIZED lattice values.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_)

import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as Kernel
import DASHI.Moonshine.JInvariantPuncturedLatticeReindexExact as Punctured
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

complexTrans :
  ∀ {x y z : Complex.BishopComplex} →
  Complex._≈C_ x y →
  Complex._≈C_ y z →
  Complex._≈C_ x z
complexTrans (xr , xi) (yr , yi) =
  BishopP.≃-trans xr yr , BishopP.≃-trans xi yi

complexSym :
  ∀ {x y : Complex.BishopComplex} →
  Complex._≈C_ x y →
  Complex._≈C_ y x
complexSym (xr , xi) =
  BishopP.≃-symm xr , BishopP.≃-symm xi

record BishopPuncturedLatticeEisensteinModel : Set₁ where
  field
    Parameter : Set
    actParameter : Lattice.SL2Z → Parameter → Parameter
    denominator :
      Lattice.SL2Z → Parameter → Complex.BishopComplex

    summand :
      Nat →
      Kernel.NonzeroLatticePoint →
      Parameter →
      Complex.BishopComplex

    puncturedSum :
      (Kernel.NonzeroLatticePoint → Complex.BishopComplex) →
      Complex.BishopComplex

    pointwiseCongruence :
      ∀ {f h : Kernel.NonzeroLatticePoint → Complex.BishopComplex} →
      ((index : Kernel.NonzeroLatticePoint) →
        Complex._≈C_ (f index) (h index)) →
      Complex._≈C_ (puncturedSum f) (puncturedSum h)

    reindexInvariant :
      (g : Lattice.SL2Z) →
      (f : Kernel.NonzeroLatticePoint → Complex.BishopComplex) →
      Complex._≈C_
        (puncturedSum
          (λ index → f (Punctured.forwardPunctured g index)))
        (puncturedSum f)

    factorOut :
      (factor : Complex.BishopComplex) →
      (f : Kernel.NonzeroLatticePoint → Complex.BishopComplex) →
      Complex._≈C_
        (puncturedSum
          (λ index → Algebra._*C_ factor (f index)))
        (Algebra._*C_ factor (puncturedSum f))

    summandTransformation :
      (weight : Nat) →
      (g : Lattice.SL2Z) →
      (parameter : Parameter) →
      (index : Kernel.NonzeroLatticePoint) →
      Complex._≈C_
        (summand weight index (actParameter g parameter))
        (Algebra._*C_
          (Algebra.powC (denominator g parameter) weight)
          (summand weight
            (Punctured.forwardPunctured g index)
            parameter))

open BishopPuncturedLatticeEisensteinModel public

rawPuncturedEisenstein :
  (M : BishopPuncturedLatticeEisensteinModel) →
  Nat → Parameter M → Complex.BishopComplex
rawPuncturedEisenstein M weight parameter =
  puncturedSum M
    (λ index → summand M weight index parameter)

rawPuncturedEisensteinTransformation :
  (M : BishopPuncturedLatticeEisensteinModel) →
  (weight : Nat) →
  (g : Lattice.SL2Z) →
  (parameter : Parameter M) →
  Complex._≈C_
    (rawPuncturedEisenstein M weight
      (actParameter M g parameter))
    (Algebra._*C_
      (Algebra.powC (denominator M g parameter) weight)
      (rawPuncturedEisenstein M weight parameter))
rawPuncturedEisensteinTransformation M weight g parameter =
  complexTrans
    (pointwiseCongruence M
      (summandTransformation M weight g parameter))
    (complexTrans
      (factorOut M
        (Algebra.powC (denominator M g parameter) weight)
        (λ index →
          summand M weight
            (Punctured.forwardPunctured g index)
            parameter))
      (reindexInvariant M g
        (λ index → summand M weight index parameter)))

------------------------------------------------------------------------
-- Explicit normalization.  This is where the eventual constants relating
-- raw G4/G6 to normalized E4/E6 belong.
------------------------------------------------------------------------

record WeightCompatibleNormalization
    (M : BishopPuncturedLatticeEisensteinModel)
    (weight : Nat) : Set₁ where
  field
    normalize : Complex.BishopComplex → Complex.BishopComplex

    normalizeCongruent :
      ∀ {left right} →
      Complex._≈C_ left right →
      Complex._≈C_ (normalize left) (normalize right)

    normalizeWeightAction :
      (g : Lattice.SL2Z) →
      (parameter : Parameter M) →
      (value : Complex.BishopComplex) →
      Complex._≈C_
        (normalize
          (Algebra._*C_
            (Algebra.powC (denominator M g parameter) weight)
            value))
        (Algebra._*C_
          (Algebra.powC (denominator M g parameter) weight)
          (normalize value))

open WeightCompatibleNormalization public

normalizedPuncturedEisenstein :
  (M : BishopPuncturedLatticeEisensteinModel) →
  ∀ {weight} →
  WeightCompatibleNormalization M weight →
  Parameter M →
  Complex.BishopComplex
normalizedPuncturedEisenstein M normalization parameter =
  normalize normalization
    (rawPuncturedEisenstein M _ parameter)

normalizedPuncturedEisensteinTransformation :
  (M : BishopPuncturedLatticeEisensteinModel) →
  ∀ {weight} →
  (normalization : WeightCompatibleNormalization M weight) →
  (g : Lattice.SL2Z) →
  (parameter : Parameter M) →
  Complex._≈C_
    (normalizedPuncturedEisenstein M normalization
      (actParameter M g parameter))
    (Algebra._*C_
      (Algebra.powC (denominator M g parameter) weight)
      (normalizedPuncturedEisenstein M normalization parameter))
normalizedPuncturedEisensteinTransformation
    M {weight} normalization g parameter =
  complexTrans
    (normalizeCongruent normalization
      (rawPuncturedEisensteinTransformation
        M weight g parameter))
    (normalizeWeightAction normalization g parameter
      (rawPuncturedEisenstein M weight parameter))

record BishopQSeriesPuncturedLatticeSameObject
    (M : BishopPuncturedLatticeEisensteinModel)
    (normalize4 : WeightCompatibleNormalization M 4)
    (normalize6 : WeightCompatibleNormalization M 6)
    (qE4 qE6 : Parameter M → Complex.BishopComplex) : Set₁ where
  field
    e4SameObject :
      (parameter : Parameter M) →
      Complex._≈C_
        (qE4 parameter)
        (normalizedPuncturedEisenstein M normalize4 parameter)

    e6SameObject :
      (parameter : Parameter M) →
      Complex._≈C_
        (qE6 parameter)
        (normalizedPuncturedEisenstein M normalize6 parameter)

open BishopQSeriesPuncturedLatticeSameObject public

qSeriesE4Modularity :
  (M : BishopPuncturedLatticeEisensteinModel) →
  (normalize4 : WeightCompatibleNormalization M 4) →
  (normalize6 : WeightCompatibleNormalization M 6) →
  (qE4 qE6 : Parameter M → Complex.BishopComplex) →
  (same :
    BishopQSeriesPuncturedLatticeSameObject
      M normalize4 normalize6 qE4 qE6) →
  (g : Lattice.SL2Z) →
  (parameter : Parameter M) →
  Complex._≈C_
    (qE4 (actParameter M g parameter))
    (Algebra._*C_
      (Algebra.powC (denominator M g parameter) 4)
      (qE4 parameter))
qSeriesE4Modularity M normalize4 normalize6 qE4 qE6 same g parameter =
  complexTrans
    (e4SameObject same (actParameter M g parameter))
    (complexTrans
      (normalizedPuncturedEisensteinTransformation
        M normalize4 g parameter)
      (Algebra.mulCCongruent
        (Complex.≈C-refl
          (Algebra.powC (denominator M g parameter) 4))
        (complexSym (e4SameObject same parameter))))

qSeriesE6Modularity :
  (M : BishopPuncturedLatticeEisensteinModel) →
  (normalize4 : WeightCompatibleNormalization M 4) →
  (normalize6 : WeightCompatibleNormalization M 6) →
  (qE4 qE6 : Parameter M → Complex.BishopComplex) →
  (same :
    BishopQSeriesPuncturedLatticeSameObject
      M normalize4 normalize6 qE4 qE6) →
  (g : Lattice.SL2Z) →
  (parameter : Parameter M) →
  Complex._≈C_
    (qE6 (actParameter M g parameter))
    (Algebra._*C_
      (Algebra.powC (denominator M g parameter) 6)
      (qE6 parameter))
qSeriesE6Modularity M normalize4 normalize6 qE4 qE6 same g parameter =
  complexTrans
    (e6SameObject same (actParameter M g parameter))
    (complexTrans
      (normalizedPuncturedEisensteinTransformation
        M normalize6 g parameter)
      (Algebra.mulCCongruent
        (Complex.≈C-refl
          (Algebra.powC (denominator M g parameter) 6))
        (complexSym (e6SameObject same parameter))))

record PreferredPuncturedEisensteinFrontier : Set where
  field
    puncturedSL2ZReindexingExact : Bool
    rawPuncturedModularityCompilerExact : Bool
    normalizationExplicit : Bool
    normalizedModularityCompilerExact : Bool
    qSeriesModularityFromNormalizedSameObjectExact : Bool
    concretePuncturedAbsoluteSumPaidHere : Bool
    concreteG4G6NormalizationConstantsPaidHere : Bool
    qSeriesEqualsNormalizedLatticePaidHere : Bool

canonicalPreferredPuncturedEisensteinFrontier :
  PreferredPuncturedEisensteinFrontier
canonicalPreferredPuncturedEisensteinFrontier = record
  { puncturedSL2ZReindexingExact = true
  ; rawPuncturedModularityCompilerExact = true
  ; normalizationExplicit = true
  ; normalizedModularityCompilerExact = true
  ; qSeriesModularityFromNormalizedSameObjectExact = true
  ; concretePuncturedAbsoluteSumPaidHere = false
  ; concreteG4G6NormalizationConstantsPaidHere = false
  ; qSeriesEqualsNormalizedLatticePaidHere = false
  }
