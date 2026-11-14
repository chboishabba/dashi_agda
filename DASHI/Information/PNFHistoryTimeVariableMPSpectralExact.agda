module DASHI.Information.PNFHistoryTimeVariableMPSpectralExact where

-- Variable-dimensional history/time-indexed MP spectral candidate.
-- Every observation instant selects p(h,t), n(h,t), a *source-centred*
-- covariance, and a calibrated MP aspect tied to those precise counts.
-- Balanced ternary is a typed address/fibre, not a free covariance value.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFHistoryTimeVariableDimensionExact as Native
import DASHI.Information.PNFSpectralGeometry as PNF
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Interop.PNFSpectralNumericABICore as ABI

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

record VariableTimeEigenmodes
  (K : Ring.ExactOrderedCommutativeRing)
  {depth : Nat}
  (F : Native.HistoryTimeVariableDimensionFibre K depth) : Set₁ where
  field
    Mode : Set
    eigenvectorAt :
      (h : Native.History F) → (t : Native.Time F) →
      Mode → Fin (Native.pAt F h t) → SOf K
    eigenvalueAt :
      Native.History F → Native.Time F → Mode → SOf K
    eigenEquationAt :
      (h : Native.History F) → (t : Native.Time F) →
      (mode : Mode) → (i : Fin (Native.pAt F h t)) →
      Ring.sumFin (Ring.orderedScalar K)
        (λ j → Scalar._*_ (Ring.orderedScalar K)
          (Native.variableCovarianceAt K F h t i j)
          (eigenvectorAt h t mode j))
      ≡ Scalar._*_ (Ring.orderedScalar K)
          (eigenvalueAt h t mode)
          (eigenvectorAt h t mode i)

open VariableTimeEigenmodes public

record VariableTimeMPCalibration
  (K : Ring.ExactOrderedCommutativeRing)
  (𝕄 : PNF.ScalarStructure)
  {depth : Nat}
  (F : Native.HistoryTimeVariableDimensionFibre K depth)
  (E : VariableTimeEigenmodes K F) : Set₁ where
  field
    encodeScalar : SOf K → PNF.ScalarStructure.Scalar 𝕄
    encodeZero :
      encodeScalar (Scalar.zero (Ring.orderedScalar K))
      ≡ PNF.ScalarStructure.0# 𝕄
    encodeOne :
      encodeScalar (Scalar.one (Ring.orderedScalar K))
      ≡ PNF.ScalarStructure.1# 𝕄
    encodePlus :
      (x y : SOf K) →
      encodeScalar (Scalar._+_ (Ring.orderedScalar K) x y)
      ≡ PNF.ScalarStructure._+_ 𝕄
          (encodeScalar x) (encodeScalar y)
    encodeTimes :
      (x y : SOf K) →
      encodeScalar (Scalar._*_ (Ring.orderedScalar K) x y)
      ≡ PNF.ScalarStructure._*_ 𝕄
          (encodeScalar x) (encodeScalar y)

    natScalar : Nat → PNF.ScalarStructure.Scalar 𝕄
    natZero : natScalar zero ≡ PNF.ScalarStructure.0# 𝕄
    natSuc :
      (m : Nat) →
      natScalar (suc m) ≡
      PNF.ScalarStructure._+_ 𝕄
        (PNF.ScalarStructure.1# 𝕄) (natScalar m)

    calibrationAt :
      Native.History F → Native.Time F →
      MP.MPFiniteCalibration 𝕄
    aspectFromSameWindow :
      (h : Native.History F) → (t : Native.Time F) →
      PNF.ScalarStructure._*_ 𝕄
        (MP.MPFiniteCalibration.aspectRatio (calibrationAt h t))
        (natScalar (suc (Native.kAt F h t)))
      ≡ natScalar (Native.pAt F h t)
    sqrtAspectCorrect :
      (h : Native.History F) → (t : Native.Time F) →
      PNF.ScalarStructure._*_ 𝕄
        (MP.MPFiniteCalibration.sqrtAspect (calibrationAt h t))
        (MP.MPFiniteCalibration.sqrtAspect (calibrationAt h t))
      ≡ MP.MPFiniteCalibration.aspectRatio (calibrationAt h t)
    variancePositive :
      (h : Native.History F) → (t : Native.Time F) →
      PNF.ScalarStructure._<_ 𝕄
        (PNF.ScalarStructure.0# 𝕄)
        (MP.MPFiniteCalibration.variance (calibrationAt h t))
    classifierAt :
      (h : Native.History F) → (t : Native.Time F) →
      PNF.NoiseClassifier 𝕄
        (MP.calibratedMPBand 𝕄 (calibrationAt h t))

open VariableTimeMPCalibration public

classifyVariableModeAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  (𝕄 : PNF.ScalarStructure) →
  {depth : Nat} →
  (F : Native.HistoryTimeVariableDimensionFibre K depth) →
  (E : VariableTimeEigenmodes K F) →
  (C : VariableTimeMPCalibration K 𝕄 F E) →
  (h : Native.History F) → (t : Native.Time F) →
  Mode E → PNF.SpectralClass
classifyVariableModeAt K 𝕄 F E C h t m =
  PNF.NoiseClassifier.classify (classifierAt C h t)
    (encodeScalar C (eigenvalueAt E h t m))

variableModeAboveMPIsOnlyCandidate :
  (K : Ring.ExactOrderedCommutativeRing) →
  (𝕄 : PNF.ScalarStructure) →
  {depth : Nat} →
  (F : Native.HistoryTimeVariableDimensionFibre K depth) →
  (E : VariableTimeEigenmodes K F) →
  (C : VariableTimeMPCalibration K 𝕄 F E) →
  (h : Native.History F) → (t : Native.Time F) →
  (m : Mode E) →
  PNF.ScalarStructure._<_ 𝕄
    (MP.MPFiniteCalibration.upperEdge (calibrationAt C h t))
    (encodeScalar C (eigenvalueAt E h t m)) →
  classifyVariableModeAt K 𝕄 F E C h t m ≡ PNF.candidateSignal
variableModeAboveMPIsOnlyCandidate K 𝕄 F E C h t m above =
  PNF.NoiseClassifier.above-null-band
    (classifierAt C h t) above

variableModeCannotPromoteNumericABI :
  (K : Ring.ExactOrderedCommutativeRing) →
  (𝕄 : PNF.ScalarStructure) →
  {depth : Nat} →
  (F : Native.HistoryTimeVariableDimensionFibre K depth) →
  (E : VariableTimeEigenmodes K F) →
  (C : VariableTimeMPCalibration K 𝕄 F E) →
  (h : Native.History F) → (t : Native.Time F) →
  (m : Mode E) →
  ABI.PNFSpectralNumericABIPromotion → ⊥
variableModeCannotPromoteNumericABI K 𝕄 F E C h t m =
  ABI.pnfSpectralNumericABIPromotionImpossible
