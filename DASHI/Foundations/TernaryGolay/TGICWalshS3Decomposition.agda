module DASHI.Foundations.TernaryGolay.TGICWalshS3Decomposition where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; 0ℚ)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance

------------------------------------------------------------------------
-- Exact extraction of the eight local values and Walsh coefficients from
-- DigitalEuan/UBP_Repo, core_studio_v4.0/core/tgic_v3.py, RuneCube369.
--
-- Values are represented as c + yCoeff * Y, so the extraction does not confuse
-- the rational implementation constant Y_50 with the exact irrational target.
------------------------------------------------------------------------

record AffineY : Set where
  constructor affineY
  field
    constant : ℚ
    yCoefficient : ℚ

open AffineY public

evaluate : AffineY → ℚ → ℚ
evaluate value y = constant value + yCoefficient value * y

data LocalBitState : Set where
  state000 state001 state010 state011 : LocalBitState
  state100 state101 state110 state111 : LocalBitState

localKernel : LocalBitState → AffineY
localKernel state000 = affineY 0ℚ 0ℚ
localKernel state001 = affineY (20 / 3) 0ℚ
localKernel state010 = affineY (20 / 3) (1 / 2)
localKernel state011 = affineY (35 / 3) (1 / 2)
localKernel state100 = affineY 0ℚ (1 / 2)
localKernel state101 = affineY (697 / 60) (1 / 2)
localKernel state110 = affineY (50 / 3) 0ℚ
localKernel state111 = affineY (997 / 60) 0ℚ

data WalshMask : Set where
  emptyMask xMask yMask zMask : WalshMask
  xyMask xzMask yzMask xyzMask : WalshMask

-- Coefficients use the convention
--   K(x,y,z) = sum_S Khat(S) (-1)^(sum_{i in S} bit_i).
walshCoefficient : WalshMask → AffineY
walshCoefficient emptyMask = affineY (699 / 80) (1 / 4)
walshCoefficient xMask = affineY (0ℚ - (199 / 80)) 0ℚ
walshCoefficient yMask = affineY (0ℚ - (25 / 6)) 0ℚ
walshCoefficient zMask = affineY (0ℚ - (697 / 240)) 0ℚ
walshCoefficient xyMask = affineY (5 / 4) (0ℚ - (1 / 4))
walshCoefficient xzMask = affineY (0ℚ - (1 / 80)) 0ℚ
walshCoefficient yzMask = affineY (0ℚ - (5 / 3)) 0ℚ
walshCoefficient xyzMask = affineY (5 / 4) 0ℚ

-- Canonical S3 average of the three pairwise Walsh coordinates.
symmetrisedPairwiseCoefficient : AffineY
symmetrisedPairwiseCoefficient =
  affineY (0ℚ - (103 / 720)) (0ℚ - (1 / 12))

-- Exact anisotropic residuals after subtracting the pairwise S3 average.
xyPairwiseBias : AffineY
xyPairwiseBias = affineY (1003 / 720) (0ℚ - (1 / 6))

xzPairwiseBias : AffineY
xzPairwiseBias = affineY (47 / 360) (1 / 12)

yzPairwiseBias : AffineY
yzPairwiseBias = affineY (0ℚ - (1097 / 720)) (1 / 12)

pairwiseBiasYCoefficientsSumToZero :
  yCoefficient xyPairwiseBias
  + yCoefficient xzPairwiseBias
  + yCoefficient yzPairwiseBias
  ≡ 0ℚ
pairwiseBiasYCoefficientsSumToZero = refl

pairwiseBiasConstantsSumToZero :
  constant xyPairwiseBias
  + constant xzPairwiseBias
  + constant yzPairwiseBias
  ≡ 0ℚ
pairwiseBiasConstantsSumToZero = refl

record TGICWalshExtractionStatus : Set where
  constructor tgicWalshExtractionStatus
  field
    sourceRepositoryURL : String
    sourceAuthor : String
    sourcePath : String
    eightLocalStatesExhaustive : Bool
    eightLocalStatesExhaustiveIsTrue : eightLocalStatesExhaustive ≡ true
    coefficientsExactOverRationalY : Bool
    coefficientsExactOverRationalYIsTrue :
      coefficientsExactOverRationalY ≡ true
    originalKernelS3Invariant : Bool
    originalKernelS3InvariantIsFalse : originalKernelS3Invariant ≡ false
    anisotropicResidualExhibited : Bool
    anisotropicResidualExhibitedIsTrue :
      anisotropicResidualExhibited ≡ true
    physicalEnergyAuthority : Bool
    physicalEnergyAuthorityIsFalse : physicalEnergyAuthority ≡ false
    reading : String

open TGICWalshExtractionStatus public

canonicalTGICWalshExtractionStatus : TGICWalshExtractionStatus
canonicalTGICWalshExtractionStatus =
  tgicWalshExtractionStatus
    Provenance.ubpRepositoryURL
    Provenance.ubpAuthorName
    "core_studio_v4.0/core/tgic_v3.py"
    true refl
    true refl
    false refl
    true refl
    false refl
    "the AND/XOR/OR presentation has an exact nonzero standard S3 residual; symmetrisation removes presentation bias but does not create physical authority"

tgicWalshGenericReceipt : GenericReceipt.GenericReceipt
tgicWalshGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "TGIC local Walsh and S3 decomposition"
    "DASHI.Foundations.TernaryGolay.TGICWalshS3Decomposition"
    "walshCoefficient"
    "the eight local kernel values, eight Walsh coefficients, S3 pairwise average, and exact anisotropic residuals are extracted from the attributed TGIC implementation"
    "the extraction is an internal model theorem and supplies no physical energy, gravity, resonance, or emergence theorem"
    "agda -i . DASHI/Foundations/TernaryGolay/TGICWalshS3Decomposition.agda"

tgicWalshGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim tgicWalshGenericReceipt ≡ false
tgicWalshGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse tgicWalshGenericReceipt
