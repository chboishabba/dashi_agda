module DASHI.Physics.Closure.NSTriadKNLuoTorusFourierDifferentiationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphaël Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Prove the coefficient algebra behind
--
--   Fourier(∂_j f)(k) = i k_j Fourier(f)(k),
--   Fourier(Δ f)(k)   = -|k|² Fourier(f)(k).
--
-- Frequencies are values in the repository real-field carrier.  The theorem
-- is independent of convergence because a trigonometric polynomial has finite
-- support.  A concrete integer embedding supplies the physical k_j values.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; trans; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring

data Axis : Set where
  axisX axisY axisZ : Axis

record FrequencyTriple
    {r : Level}
    (F : C3.RealField r) : Set r where
  constructor frequency-triple
  field
    frequencyX frequencyY frequencyZ : C3.Carrier F

open FrequencyTriple public

axisFrequency :
  ∀ {r} {F : C3.RealField r} →
  Axis → FrequencyTriple F → C3.Carrier F
axisFrequency axisX frequencies = frequencyX frequencies
axisFrequency axisY frequencies = frequencyY frequencies
axisFrequency axisZ frequencies = frequencyZ frequencies

derivativeMultiplier :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex F
derivativeMultiplier {F = F} frequency =
  C3.complex (C3.zero F) frequency

axisSecondMultiplier :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex F
axisSecondMultiplier {F = F} frequency =
  C3.complex
    (C3.negate F (C3.multiply F frequency frequency))
    (C3.zero F)

frequencyNormSquared :
  ∀ {r} {F : C3.RealField r} →
  FrequencyTriple F → C3.Carrier F
frequencyNormSquared {F = F} frequencies =
  C3.add F
    (C3.multiply F (frequencyX frequencies) (frequencyX frequencies))
    (C3.add F
      (C3.multiply F (frequencyY frequencies) (frequencyY frequencies))
      (C3.multiply F (frequencyZ frequencies) (frequencyZ frequencies)))

laplacianMultiplier :
  ∀ {r} {F : C3.RealField r} →
  FrequencyTriple F → C3.Complex F
laplacianMultiplier {F = F} frequencies =
  C3.complex
    (C3.negate F (frequencyNormSquared frequencies))
    (C3.zero F)

derivativeMultiplierSquare :
  ∀ {r} {F : C3.RealField r}
    (frequency : C3.Carrier F) →
  C3.complexMultiply
    (derivativeMultiplier frequency)
    (derivativeMultiplier frequency)
  ≡ axisSecondMultiplier frequency
derivativeMultiplierSquare {F = F} frequency =
  Algebra.complexExt
    (P.R.solve 1
      (λ value →
        P.multiplyReal
          (P.R.Κ (C3.zero F)) value
          (P.R.Κ (C3.zero F)) value
        P.R.⊜
        (P.R.⊝ (value P.R.⊗ value)))
      refl frequency)
    (P.R.solve 1
      (λ value →
        P.multiplyImaginary
          (P.R.Κ (C3.zero F)) value
          (P.R.Κ (C3.zero F)) value
        P.R.⊜ P.R.Κ (C3.zero F))
      refl frequency)
  where
    module P = Algebra.Polynomial F

secondDerivativeCoefficient :
  ∀ {r} {F : C3.RealField r}
    (frequency : C3.Carrier F)
    (coefficient : C3.Complex F) →
  C3.complexMultiply
    (derivativeMultiplier frequency)
    (C3.complexMultiply
      (derivativeMultiplier frequency)
      coefficient)
  ≡ C3.complexMultiply
      (axisSecondMultiplier frequency)
      coefficient
secondDerivativeCoefficient frequency coefficient =
  trans
    (sym
      (Algebra.complexMultiplyAssociative
        (derivativeMultiplier frequency)
        (derivativeMultiplier frequency)
        coefficient))
    (cong
      (λ multiplier → C3.complexMultiply multiplier coefficient)
      (derivativeMultiplierSquare frequency))

axisSecondMultipliersSum :
  ∀ {r} {F : C3.RealField r}
    (frequencies : FrequencyTriple F) →
  C3.complexAdd
    (axisSecondMultiplier (frequencyX frequencies))
    (C3.complexAdd
      (axisSecondMultiplier (frequencyY frequencies))
      (axisSecondMultiplier (frequencyZ frequencies)))
  ≡ laplacianMultiplier frequencies
axisSecondMultipliersSum {F = F} frequencies =
  Algebra.complexExt
    (P.R.solve 3
      (λ x y z →
        (P.R.⊝ (x P.R.⊗ x))
          P.R.⊕
        ((P.R.⊝ (y P.R.⊗ y))
          P.R.⊕ (P.R.⊝ (z P.R.⊗ z)))
        P.R.⊜
        P.R.⊝
          ((x P.R.⊗ x)
            P.R.⊕ ((y P.R.⊗ y) P.R.⊕ (z P.R.⊗ z))))
      refl
      (frequencyX frequencies)
      (frequencyY frequencies)
      (frequencyZ frequencies))
    (trans
      (cong
        (C3.add F (C3.zero F))
        (C3.addZeroLeft F (C3.zero F)))
      (C3.addZeroLeft F (C3.zero F)))
  where
    module P = Algebra.Polynomial F

laplacianCoefficientIdentity :
  ∀ {r} {F : C3.RealField r}
    (frequencies : FrequencyTriple F)
    (coefficient : C3.Complex F) →
  C3.complexAdd
    (C3.complexMultiply
      (derivativeMultiplier (frequencyX frequencies))
      (C3.complexMultiply
        (derivativeMultiplier (frequencyX frequencies))
        coefficient))
    (C3.complexAdd
      (C3.complexMultiply
        (derivativeMultiplier (frequencyY frequencies))
        (C3.complexMultiply
          (derivativeMultiplier (frequencyY frequencies))
          coefficient))
      (C3.complexMultiply
        (derivativeMultiplier (frequencyZ frequencies))
        (C3.complexMultiply
          (derivativeMultiplier (frequencyZ frequencies))
          coefficient)))
  ≡ C3.complexMultiply
      (laplacianMultiplier frequencies)
      coefficient
laplacianCoefficientIdentity frequencies coefficient =
  trans
    (cong₂ C3.complexAdd
      (secondDerivativeCoefficient
        (frequencyX frequencies) coefficient)
      (cong₂ C3.complexAdd
        (secondDerivativeCoefficient
          (frequencyY frequencies) coefficient)
        (secondDerivativeCoefficient
          (frequencyZ frequencies) coefficient)))
    (trans
      (cong
        (C3.complexAdd
          (C3.complexMultiply
            (axisSecondMultiplier (frequencyX frequencies))
            coefficient))
        (sym
          (Ring.complexDistributeRight
            (axisSecondMultiplier (frequencyY frequencies))
            (axisSecondMultiplier (frequencyZ frequencies))
            coefficient)))
      (trans
        (sym
          (Ring.complexDistributeRight
            (axisSecondMultiplier (frequencyX frequencies))
            (C3.complexAdd
              (axisSecondMultiplier (frequencyY frequencies))
              (axisSecondMultiplier (frequencyZ frequencies)))
            coefficient))
        (cong
          (λ multiplier → C3.complexMultiply multiplier coefficient)
          (axisSecondMultipliersSum frequencies))))
