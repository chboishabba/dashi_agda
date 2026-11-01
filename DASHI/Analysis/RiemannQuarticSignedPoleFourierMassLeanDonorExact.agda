module DASHI.Analysis.RiemannQuarticSignedPoleFourierMassLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH QUARTIC SIGNED-POLE FOURIER-MASS / CONSTANT-DENSITY DONOR
--
-- Companion Lean branch:
--
--   chboishabba/dashi_lean4
--   agent/rh-marked-cluster-target-reflection
--
-- This owner records the new same-object distinction that is absent from the
-- older G2 constant-density-cancellation route.
--
-- For the selected quartic signed-pole witness W:
--
--   Psi_t(t) = 0
--
-- because the dual cosine transform has zero zeroth moment, while the
-- physical profile origin survives:
--
--   P_W(0)
--     = 4 G_R(0) OriginDet_W,
--
--   G_R(0) = 1/(R M0) > 0,
--
--   OriginDet_W < 0,
--
-- hence
--
--   P_W(0) < 0.
--
-- The companion Lean Fourier-mass weld proves, at source level,
--
--   integral C_W(q) dq
--     = 2 pi P_W(0)
--     = 8 pi/(R M0) OriginDet_W,
--
-- and after the exact physical scaling r=t/16,
--
--   integral Psi_t(x) dx
--     = 128 pi/(t R M0) OriginDet_W < 0.
--
-- Therefore the constant-density channel is NOT killed in this quartic
-- witness family.  It is instead the explicit scalar
--
--   mu(t) integral Psi_t
--     = 128 pi mu(t)/(t R M0) OriginDet_W.
--
-- If mu(t)>0, subtracting this channel in the canonical Far-minus-mu scalar
-- creates a strictly positive adverse contribution.  The genuine remaining
-- theorem must therefore control the COUPLED discrete far-zero source,
-- this center-density mode, and the density-variation channel.
--
-- Attribution firewall:
--
-- * this Agda module is a receipt/frontier owner for Lean source;
-- * it does not independently reconstruct real Fourier inversion;
-- * no Lean exact-head kernel receipt is claimed here;
-- * no semantic identification of 3^4-1 with either analytic origin is made;
-- * RH remains unproved.
------------------------------------------------------------------------

record QuarticSignedPoleFourierMassReceipt : Set where
  constructor quartic-signed-pole-fourier-mass-receipt
  field
    repository : String
    branch : String
    postSixthPath : String
    cosineL1Path : String
    inversionPath : String
    specializationPath : String

    dualPunctureCommit : String
    physicalOriginIdentityCommit : String
    muSplitCommit : String
    commonWindowFactorCommit : String
    positiveCentralWindowCommit : String
    negativeProfileOriginCommit : String
    cosineL1Commit : String
    scaledCosineL1Commit : String
    inversionCommit : String
    specializationCommit : String
    centerDensityCommit : String

open QuarticSignedPoleFourierMassReceipt public

currentQuarticSignedPoleFourierMassReceipt :
  QuarticSignedPoleFourierMassReceipt
currentQuarticSignedPoleFourierMassReceipt =
  quartic-signed-pole-fourier-mass-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-marked-cluster-target-reflection"
    "Synthesis/RiemannProjectiveQuarticFourWindowSignedPolePostSixthAbsorb.lean"
    "Synthesis/RiemannCompactCosineFourierMass.lean"
    "Synthesis/RiemannCompactCosineFourierMassInversion.lean"
    "Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean"

    "395431a2352400188e14b96614c3863a2625ded1"
    "eae679fb43cfb11d3a4283be73faffb74752077c"
    "4d1509fb07357c142e6148ae14b41229c2870465"
    "824f84cddf5cf424c643688c2d24e351795dac07"
    "4b1f53c0c3ca8fdaa93d3ce82294756b8a6fa695"
    "d4a10119d2f52049593a54ec4db7a8f1eb1e32f0"
    "5f0e5d9f0f66bf51fa6b2cd27cf3c8c247a9aa67"
    "d7129670fbc00914b917f9ec6130d96c133da00e"
    "e38a915b1c8e5961269442e81ff858ac840d12e2"
    "0203c40ce5068f6def0e3ac4f91e768b4f58231b"
    "e3f4e2a7b0ad2dd3e5fb183b5aeeb7861a81c7a0"

record QuarticSignedPoleFourierMassBoundary : Set where
  constructor quartic-signed-pole-fourier-mass-boundary
  field
    dualCenterPunctureSourceWritten : Bool
    sameOrdinateBaseSourceKilledSourceWritten : Bool

    negativePhysicalOriginDeterminantSourceWritten : Bool
    endpointWindowOriginCommonSourceWritten : Bool
    positiveCentralWindowExactValueSourceWritten : Bool
    negativeCombinedPhysicalProfileOriginSourceWritten : Bool

    compactCosineInverseSquareDecaySourceWritten : Bool
    compactCosineL1SourceWritten : Bool
    scaledCompactCosineL1SourceWritten : Bool
    cosineFourierNormalizationSourceWritten : Bool
    cosineMassEqualsTwoPiPhysicalOriginSourceWritten : Bool

    physicalPsiMassExactSourceWritten : Bool
    physicalPsiMassNegativeForSelectedWitnessSourceWritten : Bool

    finiteMuCenterDensityVariationSplitSourceWritten : Bool
    exactCenterDensityOriginFactorSourceWritten : Bool
    adverseCenterDensitySignConditionalOnMuPositiveSourceWritten : Bool

    dualPunctureImpliesPhysicalOriginZero : Bool
    balancedTernaryPunctureIdentifiedWithDualOrigin : Bool
    balancedTernaryPunctureIdentifiedWithPhysicalOrigin : Bool

    fullFarMinusMuCancellationPaid : Bool
    densityVariationCancellationPaid : Bool
    leanExactHeadKernelReceiptOwnedHere : Bool
    agdaReprovesFourierInversionHere : Bool
    rhDerivedHere : Bool

    dualCenterPunctureSourceWrittenIsTrue :
      dualCenterPunctureSourceWritten ≡ true
    physicalOriginSurvivalSourceWrittenIsTrue :
      negativePhysicalOriginDeterminantSourceWritten ≡ true
    cosineMassWeldSourceWrittenIsTrue :
      cosineMassEqualsTwoPiPhysicalOriginSourceWritten ≡ true
    physicalPsiMassSourceWrittenIsTrue :
      physicalPsiMassExactSourceWritten ≡ true
    centerDensityFactorSourceWrittenIsTrue :
      exactCenterDensityOriginFactorSourceWritten ≡ true

    dualPunctureDoesNotKillPhysicalOrigin :
      dualPunctureImpliesPhysicalOriginZero ≡ false
    noTernaryDualOriginSemanticIdentification :
      balancedTernaryPunctureIdentifiedWithDualOrigin ≡ false
    noTernaryPhysicalOriginSemanticIdentification :
      balancedTernaryPunctureIdentifiedWithPhysicalOrigin ≡ false

    fullCancellationStillOpen :
      fullFarMinusMuCancellationPaid ≡ false
    variationCancellationStillOpen :
      densityVariationCancellationPaid ≡ false
    leanKernelReceiptNotClaimed :
      leanExactHeadKernelReceiptOwnedHere ≡ false
    agdaDoesNotReproveFourierInversion :
      agdaReprovesFourierInversionHere ≡ false
    rhStillNotDerived :
      rhDerivedHere ≡ false

    exactMassFormula : String
    exactCenterDensityFormula : String
    currentAnalyticWall : String
    comparisonWithOldG2Route : String

open QuarticSignedPoleFourierMassBoundary public

canonicalQuarticSignedPoleFourierMassBoundary :
  QuarticSignedPoleFourierMassBoundary
canonicalQuarticSignedPoleFourierMassBoundary =
  quartic-signed-pole-fourier-mass-boundary
    true true

    true true true true

    true true true true true

    true true

    true true true

    false false false

    false false false false false

    refl refl refl refl refl
    refl refl refl
    refl refl refl refl refl

    "integral Psi_t = 128*pi/(t*R*M0) * OriginDet_W"
    "mu(t)*integral Psi_t = 128*pi*mu(t)/(t*R*M0) * OriginDet_W"
    "Prove the exact coupled canonical far-zero source minus center-density minus mu-variation scalar is below the terminal quartic margin.  Separate absolute estimates are not the preferred cut."
    "The older G2 donor killed its constant-density mode because the physical profile had H_t(0)=0.  The present quartic signed-pole witness instead has a dual-center puncture Psi_t(t)=0 while P_W(0)<0, so Fourier inversion produces a nonzero constant-density mode."

dualAndPhysicalOriginsAreFormallyDistinct :
  QuarticSignedPoleFourierMassBoundary.dualPunctureImpliesPhysicalOriginZero
    canonicalQuarticSignedPoleFourierMassBoundary ≡ false
dualAndPhysicalOriginsAreFormallyDistinct = refl

fourierMassWeldRecorded :
  QuarticSignedPoleFourierMassBoundary.cosineMassEqualsTwoPiPhysicalOriginSourceWritten
    canonicalQuarticSignedPoleFourierMassBoundary ≡ true
fourierMassWeldRecorded = refl

centerDensityModeIsNowExplicit :
  QuarticSignedPoleFourierMassBoundary.exactCenterDensityOriginFactorSourceWritten
    canonicalQuarticSignedPoleFourierMassBoundary ≡ true
centerDensityModeIsNowExplicit = refl

jointFarMinusMuCancellationRemainsOpen :
  QuarticSignedPoleFourierMassBoundary.fullFarMinusMuCancellationPaid
    canonicalQuarticSignedPoleFourierMassBoundary ≡ false
jointFarMinusMuCancellationRemainsOpen = refl
