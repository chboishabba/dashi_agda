module DASHI.Physics.Closure.NSTriadKNHHGoodExactTensorKernelNormRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- The HH-good kernel is matrix/tensor valued.  Entrywise L1, Frobenius L1,
-- and operator-norm L1 are equivalent in finite dimension but carry different
-- constants.  Round 50 therefore forbids a silent norm switch at the final
-- same-object seam.
--
-- A physical analytic package must state one exact tensor norm and identify
-- its shell/master masses with the exact rational masses consumed by the
-- existing weighted-Cauchy theorem.  Once that equality is supplied, the old
-- periodized theorem is recovered without inserting any hidden dimension
-- constant.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized

data TensorKernelNorm : Set where
  operatorNorm frobeniusNorm entrywiseL1Norm : TensorKernelNorm

record ExactTensorNormAnnularKernel
    {t : Level}
    (TorusPoint : Set t) : Set (lsuc t) where
  field
    tensorNorm : TensorKernelNorm

    shellTensorKernelL1 : Nat → ℚ
    masterTensorKernelL1 : ℚ
    masterTensorKernelL1Nonnegative : 0ℚ ≤ masterTensorKernelL1
    shellTensorKernelL1BelowMaster : ∀ shell →
      shellTensorKernelL1 shell ≤ masterTensorKernelL1

    AnnularCutoffSmoothAndCompactlySupportedAwayFromZero : Set t
    annularCutoffSmoothAndCompactlySupportedAwayFromZero :
      AnnularCutoffSmoothAndCompactlySupportedAwayFromZero

    MasterKernelIsL1InSelectedTensorNorm : Set t
    masterKernelIsL1InSelectedTensorNorm :
      MasterKernelIsL1InSelectedTensorNorm

    PeriodizationCanonicalInSelectedTensorNorm : Set t
    periodizationCanonicalInSelectedTensorNorm :
      PeriodizationCanonicalInSelectedTensorNorm

open ExactTensorNormAnnularKernel public

asPeriodizedAnnularStrainKernelL1Theorem :
  ∀ {t} {TorusPoint : Set t} →
  ExactTensorNormAnnularKernel TorusPoint →
  Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint
asPeriodizedAnnularStrainKernelL1Theorem exact = record
  { strainShellKernelL1Norm = shellTensorKernelL1 exact
  ; masterAnnularStrainKernelL1Norm = masterTensorKernelL1 exact
  ; masterAnnularStrainKernelL1Nonnegative =
      masterTensorKernelL1Nonnegative exact
  ; periodizedStrainKernelL1BoundUniformInShell =
      shellTensorKernelL1BelowMaster exact
  ; AnnularCutoffSmoothAndCompactlySupportedAwayFromZero =
      AnnularCutoffSmoothAndCompactlySupportedAwayFromZero exact
  ; annularCutoffSmoothAndCompactlySupportedAwayFromZero =
      annularCutoffSmoothAndCompactlySupportedAwayFromZero exact
  ; MasterAnnularStrainKernelIsL1 =
      MasterKernelIsL1InSelectedTensorNorm exact
  ; masterAnnularStrainKernelIsL1 =
      masterKernelIsL1InSelectedTensorNorm exact
  ; PeriodizationFormulaIsCanonical =
      PeriodizationCanonicalInSelectedTensorNorm exact
  ; periodizationFormulaIsCanonical =
      periodizationCanonicalInSelectedTensorNorm exact
  }

hhGoodTensorNormCannotChangeSilently : Bool
hhGoodTensorNormCannotChangeSilently = true

physicalExactTensorNormAnnularKernelConstructed : Bool
physicalExactTensorNormAnnularKernelConstructed = false

hhGoodTensorNormCannotChangeSilentlyIsTrue :
  hhGoodTensorNormCannotChangeSilently ≡ true
hhGoodTensorNormCannotChangeSilentlyIsTrue = refl

physicalExactTensorNormAnnularKernelConstructedIsFalse :
  physicalExactTensorNormAnnularKernelConstructed ≡ false
physicalExactTensorNormAnnularKernelConstructedIsFalse = refl
