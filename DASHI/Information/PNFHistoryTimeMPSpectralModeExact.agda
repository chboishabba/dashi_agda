module DASHI.Information.PNFHistoryTimeMPSpectralModeExact where

-- Genuine eigenmode *on the same selected history/time covariance*.
-- The numeric MP edge is a separately specified null model, and
-- pointwise classification does not create semantic or trading authority.
--
-- This is intentionally time-indexed and balanced-ternary/fibre native:
-- it consumes the source-owned situated PNF window, NOT an anonymous
-- static eigenvalue list or a parallel 369 ontology.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact as Native
import DASHI.Information.PNFSpectralGeometry as PNF
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Interop.PNFSpectralNumericABICore as ABI

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

-- An eigenvector is linked to the *actual* covariance at (history,time)
-- by a pointwise matrix action equality. This is not a 'Set' receipt.
record HistoryTimeCovarianceEigenmodes
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) : Set₁ where
  field
    Mode : Set
    eigenvectorAt :
      Native.History F → Native.Time F → Mode → Fin p → SOf K
    eigenvalueAt :
      Native.History F → Native.Time F → Mode → SOf K
    eigenEquationAt :
      (h : Native.History F) → (t : Native.Time F) →
      (mode : Mode) → (i : Fin p) →
      Ring.sumFin (Ring.orderedScalar K)
        (λ j → Scalar._*_ (Ring.orderedScalar K)
          (Native.covarianceAt K F h t i j)
          (eigenvectorAt h t mode j))
      ≡
      Scalar._*_ (Ring.orderedScalar K)
        (eigenvalueAt h t mode)
        (eigenvectorAt h t mode i)

open HistoryTimeCovarianceEigenmodes public

-- The two scalar owners need an explicit map, because a finite exact
-- ordered ring does not automatically equal an analytic MP real carrier.
record HistoryTimeMPModeClassifier
  (K : Ring.ExactOrderedCommutativeRing)
  (𝕄 : PNF.ScalarStructure)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p)
  (E : HistoryTimeCovarianceEigenmodes K F) : Set₁ where
  field
    toMPCarrier : SOf K → PNF.ScalarStructure.Scalar 𝕄
    -- A numeric recoding must be independently certified as an exact
    -- scalar homomorphism; otherwise an arbitrary digit map could make
    -- the numeric 'eigenvalue' unrelated to the source eigen equation.
    preservesZero :
      toMPCarrier (Scalar.zero (Ring.orderedScalar K))
      ≡ PNF.ScalarStructure.0# 𝕄
    preservesOne :
      toMPCarrier (Scalar.one (Ring.orderedScalar K))
      ≡ PNF.ScalarStructure.1# 𝕄
    preservesAddition :
      (a b : SOf K) →
      toMPCarrier (Scalar._+_ (Ring.orderedScalar K) a b)
      ≡ PNF.ScalarStructure._+_ 𝕄 (toMPCarrier a) (toMPCarrier b)
    preservesMultiplication :
      (a b : SOf K) →
      toMPCarrier (Scalar._*_ (Ring.orderedScalar K) a b)
      ≡ PNF.ScalarStructure._*_ 𝕄 (toMPCarrier a) (toMPCarrier b)
    -- Counts are from this same selected finite observation window.
    -- The finite calibration MUST pay gamma = p / (n-1), rather than
    -- accepting any positive looking MP edge.
    countScalar : Nat → PNF.ScalarStructure.Scalar 𝕄
    countZero :
      countScalar zero ≡ PNF.ScalarStructure.0# 𝕄
    countSuccessor :
      (n : Nat) →
      countScalar (suc n) ≡
      PNF.ScalarStructure._+_ 𝕄
        (PNF.ScalarStructure.1# 𝕄) (countScalar n)
    calibrationAt :
      Native.History F → Native.Time F →
      MP.MPFiniteCalibration 𝕄
    aspectRatioIsSelectedSampleCount :
      (h : Native.History F) → (t : Native.Time F) →
      PNF.ScalarStructure._*_ 𝕄
        (MP.MPFiniteCalibration.aspectRatio (calibrationAt h t))
        (countScalar (suc k))
      ≡ countScalar p
    calibratedSquareRootIsAspect :
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

open HistoryTimeMPModeClassifier public

classifyModeAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  (𝕄 : PNF.ScalarStructure) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (E : HistoryTimeCovarianceEigenmodes K F) →
  (C : HistoryTimeMPModeClassifier K 𝕄 F E) →
  (h : Native.History F) → (t : Native.Time F) →
  Mode E → PNF.SpectralClass
classifyModeAt K 𝕄 F E C h t mode =
  PNF.NoiseClassifier.classify (classifierAt C h t)
    (toMPCarrier C (eigenvalueAt E h t mode))

aboveMPEdgeCandidateAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  (𝕄 : PNF.ScalarStructure) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (E : HistoryTimeCovarianceEigenmodes K F) →
  (C : HistoryTimeMPModeClassifier K 𝕄 F E) →
  (h : Native.History F) → (t : Native.Time F) →
  (mode : Mode E) →
  PNF.ScalarStructure._<_ 𝕄
    (MP.MPFiniteCalibration.upperEdge (calibrationAt C h t))
    (toMPCarrier C (eigenvalueAt E h t mode)) →
  classifyModeAt K 𝕄 F E C h t mode ≡ PNF.candidateSignal
aboveMPEdgeCandidateAt K 𝕄 F E C h t mode above =
  PNF.NoiseClassifier.above-null-band
    (classifierAt C h t) above

candidateCannotPromoteNativeNumericABI :
  (K : Ring.ExactOrderedCommutativeRing) →
  (𝕄 : PNF.ScalarStructure) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (E : HistoryTimeCovarianceEigenmodes K F) →
  (C : HistoryTimeMPModeClassifier K 𝕄 F E) →
  (h : Native.History F) → (t : Native.Time F) →
  (mode : Mode E) →
  ABI.PNFSpectralNumericABIPromotion → ⊥
candidateCannotPromoteNativeNumericABI K 𝕄 F E C h t mode =
  ABI.pnfSpectralNumericABIPromotionImpossible
