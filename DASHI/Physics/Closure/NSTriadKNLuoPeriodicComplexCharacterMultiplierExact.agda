module DASHI.Physics.Closure.NSTriadKNLuoPeriodicComplexCharacterMultiplierExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Specialize the complex linear-integral theorem to the repository's literal
-- Z^3 Fourier modes.  Once a periodic complex character satisfies
--
--   chi_{k+l}(y) = chi_k(y) chi_l(y),   chi_0(y)=1,
--
-- the weighted-increment multiplier identity is derived for every pair of
-- integer modes.  Kernel mass one then replaces the zero transform by the
-- literal complex unit.  The whole multiplier identity is not an input.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoComplexLinearIntegralWeightedIncrementExact as Integral

record PeriodicComplexCharacterData
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    TorusPoint : Set
    integral : Integral.ComplexLinearIntegral F TorusPoint

    kernelWeight : TorusPoint → C3.Complex F
    character : Z3.FourierMode → TorusPoint → C3.Complex F

    characterAdd :
      (left right : Z3.FourierMode) →
      (point : TorusPoint) →
      character (Z3.addMode left right) point
      ≡ C3.complexMultiply
          (character left point)
          (character right point)

    characterZero :
      (point : TorusPoint) →
      character Z3.zeroMode point ≡ C3.complexOne F

open PeriodicComplexCharacterData public

asIntegralCharacterSystem :
  ∀ {r} {F : C3.RealField r} →
  PeriodicComplexCharacterData F →
  Integral.ComplexIntegralCharacterSystem F
asIntegralCharacterSystem data = record
  { Sample = TorusPoint data
  ; Mode = Z3.FourierMode
  ; integral = integral data
  ; zeroMode = Z3.zeroMode
  ; addMode = Z3.addMode
  ; kernelWeight = kernelWeight data
  ; character = character data
  ; characterProduct = characterAdd data
  ; zeroCharacter = characterZero data
  }

periodicKernelTransform :
  ∀ {r} {F : C3.RealField r} →
  PeriodicComplexCharacterData F →
  Z3.FourierMode → C3.Complex F
periodicKernelTransform data =
  Integral.complexIntegralKernelTransformAt
    (asIntegralCharacterSystem data)

periodicKernelMass :
  ∀ {r} {F : C3.RealField r} →
  PeriodicComplexCharacterData F → C3.Complex F
periodicKernelMass data =
  Integral.complexIntegralKernelTransform
    (asIntegralCharacterSystem data)

periodicWeightedIncrement :
  ∀ {r} {F : C3.RealField r} →
  PeriodicComplexCharacterData F →
  Z3.FourierMode → Z3.FourierMode → C3.Complex F
periodicWeightedIncrement data =
  Integral.complexIntegralWeightedIncrement
    (asIntegralCharacterSystem data)

periodicWeightedIncrementMultiplierIdentity :
  ∀ {r} {F : C3.RealField r}
    (data : PeriodicComplexCharacterData F)
    (left right : Z3.FourierMode) →
  periodicWeightedIncrement data left right
  ≡ C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (periodicKernelTransform data (Z3.addMode left right))
          (periodicKernelTransform data left))
        (periodicKernelTransform data right))
      (periodicKernelTransform data Z3.zeroMode)
periodicWeightedIncrementMultiplierIdentity data left right =
  Integral.complexLinearIntegralWeightedIncrementIdentity
    (asIntegralCharacterSystem data)
    left
    right

periodicZeroTransformEqualsKernelMass :
  ∀ {r} {F : C3.RealField r}
    (data : PeriodicComplexCharacterData F) →
  periodicKernelTransform data Z3.zeroMode
  ≡ periodicKernelMass data
periodicZeroTransformEqualsKernelMass data =
  Integral.complexIntegralZeroTransformEqualsKernelMass
    (asIntegralCharacterSystem data)

periodicNormalizedWeightedIncrementMultiplierIdentity :
  ∀ {r} {F : C3.RealField r}
    (data : PeriodicComplexCharacterData F) →
  periodicKernelMass data ≡ C3.complexOne F →
  (left right : Z3.FourierMode) →
  periodicWeightedIncrement data left right
  ≡ C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (periodicKernelTransform data (Z3.addMode left right))
          (periodicKernelTransform data left))
        (periodicKernelTransform data right))
      (C3.complexOne F)
periodicNormalizedWeightedIncrementMultiplierIdentity
  data normalizedMass left right =
  trans
    (periodicWeightedIncrementMultiplierIdentity data left right)
    (cong
      (λ zeroTransform →
        C3.complexAdd
          (C3.complexSubtract
            (C3.complexSubtract
              (periodicKernelTransform data (Z3.addMode left right))
              (periodicKernelTransform data left))
            (periodicKernelTransform data right))
          zeroTransform)
      (trans
        (periodicZeroTransformEqualsKernelMass data)
        normalizedMass))

periodicComplexMultiplierAlgebraClosed : Bool
periodicComplexMultiplierAlgebraClosed = true

periodicNormalizedMultiplierAlgebraClosed : Bool
periodicNormalizedMultiplierAlgebraClosed = true

periodicComplexMultiplierAlgebraClosedIsTrue :
  periodicComplexMultiplierAlgebraClosed ≡ true
periodicComplexMultiplierAlgebraClosedIsTrue = refl

periodicNormalizedMultiplierAlgebraClosedIsTrue :
  periodicNormalizedMultiplierAlgebraClosed ≡ true
periodicNormalizedMultiplierAlgebraClosedIsTrue = refl
