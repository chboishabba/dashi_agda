module DASHI.Unified.HyperfabricSignedZeroWaveGeometryCutExact where

-- Reuse canonical owners. Finite mathematical bridge ONLY: no physical,
-- string, Einstein, continuum, or Clay same-object result.
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SignedZeroTernaryOrientationExact as Signed
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.BalancedTernaryFourierModeExact as Wave
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Algebra.TriadicDepthOneCharacters as Characters

-- The path-grid voxel and periodic Fourier site are independent. An actual
-- same-operator map must be proved, not silently installed via equal counts.
record FiniteHyperfabricChart : Set where
  constructor finiteHyperfabricChart
  field
    voxel : Cube.Ternary27Point
    signedNeutralOrientation : Signed.SignedNeutralPhase3
    waveMode : Wave.Mode3x3
    periodicWavePoint : Torus.Torus3x3
open FiniteHyperfabricChart public

rotateInternalOrientation : FiniteHyperfabricChart → FiniteHyperfabricChart
rotateInternalOrientation chart =
  finiteHyperfabricChart
    (voxel chart)
    (Signed.rotateSignedNeutral (signedNeutralOrientation chart))
    (waveMode chart)
    (periodicWavePoint chart)

rotationInvisibleToScalar :
  (chart : FiniteHyperfabricChart) →
  Signed.neutralScalar (signedNeutralOrientation (rotateInternalOrientation chart))
    ≡ Signed.neutralScalar (signedNeutralOrientation chart)
rotationInvisibleToScalar chart =
  Signed.allSignedNeutralPhasesShareScalar
    (Signed.rotateSignedNeutral (signedNeutralOrientation chart))
    (signedNeutralOrientation chart)

signedEndsDistinct : Signed.minusZeroPhase ≡ Signed.plusZeroPhase → ⊥
signedEndsDistinct ()

-- A globally faithful inverse to the scalar zero projection is impossible.
scalarZeroProjectionNotInjective :
  ((x y : Signed.SignedNeutralPhase3) →
   Signed.neutralScalar x ≡ Signed.neutralScalar y → x ≡ y) → ⊥
scalarZeroProjectionNotInjective inverse =
  signedEndsDistinct (inverse Signed.minusZeroPhase Signed.plusZeroPhase refl)

-- Reuse the exact finite-group character-translation theorem.
periodicWaveTranslation :
  (mode point : Wave.Mode3x3) →
  Wave.firstCharacter mode (Torus.translateFirst point)
  ≡ Characters.multiplyPhase
      (Wave.firstCharacter mode point)
      (Wave.firstEigenphase mode)
periodicWaveTranslation = Wave.firstTranslationEigen

-- The booleans are claim-state controls, NOT physics witnesses.
record HyperfabricPhysicalPromotionBoundary : Set where
  field
    finiteCharacterImpliesPhysicalWave : Bool
    characterNonPromotion : finiteCharacterImpliesPhysicalWave ≡ false

    signedZeroImpliesHilbertAmplitude : Bool
    amplitudeNonPromotion : signedZeroImpliesHilbertAmplitude ≡ false

    finiteVoxelImpliesLorentzianSpacetime : Bool
    geometryNonPromotion : finiteVoxelImpliesLorentzianSpacetime ≡ false

    latticeEmbeddingImpliesPhysicalString : Bool
    stringNonPromotion : latticeEmbeddingImpliesPhysicalString ≡ false

    sharedCarrierImpliesClayResolution : Bool
    clayNonPromotion : sharedCarrierImpliesClayResolution ≡ false

canonicalHyperfabricPhysicalPromotionBoundary :
  HyperfabricPhysicalPromotionBoundary
canonicalHyperfabricPhysicalPromotionBoundary = record
  { finiteCharacterImpliesPhysicalWave = false
  ; characterNonPromotion = refl
  ; signedZeroImpliesHilbertAmplitude = false
  ; amplitudeNonPromotion = refl
  ; finiteVoxelImpliesLorentzianSpacetime = false
  ; geometryNonPromotion = refl
  ; latticeEmbeddingImpliesPhysicalString = false
  ; stringNonPromotion = refl
  ; sharedCarrierImpliesClayResolution = false
  ; clayNonPromotion = refl
  }
