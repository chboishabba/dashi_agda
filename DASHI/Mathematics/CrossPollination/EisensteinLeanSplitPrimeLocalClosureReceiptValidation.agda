module DASHI.Mathematics.CrossPollination.EisensteinLeanSplitPrimeLocalClosureReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution
import DASHI.Mathematics.CrossPollination.EisensteinLeanSplitPrimeLocalClosureReceiptExact as Receipt

formalSourceOrigin :
  Receipt.claimOrigin ≡ Attribution.leanFormalReconstruction
formalSourceOrigin = refl

cubeFibreCertificateObserved :
  Receipt.canonicalCubeFibreCertificateObserved ≡ true
cubeFibreCertificateObserved = refl

genericKernelEqualsCubesObserved :
  Receipt.arbitraryOrderThreeKernelEqualsCubesObserved ≡ true
genericKernelEqualsCubesObserved = refl

jacobiNormPrimeObserved :
  Receipt.splitJacobiNormPrimeObserved ≡ true
jacobiNormPrimeObserved = refl

literalEisensteinPullbackObserved :
  Receipt.literalEisensteinQAPullbackObserved ≡ true
literalEisensteinPullbackObserved = refl

splitTraceObserved : Receipt.splitPrimeTraceObserved ≡ true
splitTraceObserved = refl

splitEulerObserved : Receipt.splitPrimeLocalEulerObserved ≡ true
splitEulerObserved = refl

sixUnitNormalizationObserved :
  Receipt.sixUnitNormalizationObserved ≡ true
sixUnitNormalizationObserved = refl

allGoodPrimeLocalObserved :
  Receipt.allGoodPrimeLocalClassificationObserved ≡ true
allGoodPrimeLocalObserved = refl

badPrimeTwoLiteralReductionObserved :
  Receipt.badPrimeTwoLiteralReductionObserved ≡ true
badPrimeTwoLiteralReductionObserved = refl

badPrimeThreeLiteralReductionObserved :
  Receipt.badPrimeThreeLiteralReductionObserved ≡ true
badPrimeThreeLiteralReductionObserved = refl

badPrimeLocalFactorsStillUnpaid :
  Receipt.badPrimeEllipticLocalFactorsObserved ≡ false
badPrimeLocalFactorsStillUnpaid = refl

external36a1ProvenanceRecorded :
  Receipt.external36a1ProvenanceReceiptObserved ≡ true
external36a1ProvenanceRecorded = refl

externalMetadataNotProofAuthority :
  Receipt.externalMetadataPromotedToProofAuthority ≡ false
externalMetadataNotProofAuthority = refl

noLeanProofObjectImported :
  Receipt.leanProofObjectImportedIntoAgda ≡ false
noLeanProofObjectImported = refl

noAgdaTheoremManufactured :
  Receipt.agdaSplitPrimeTheoremInhabitedFromReceipt ≡ false
noAgdaTheoremManufactured = refl

noExternalScientificAuthorityManufactured :
  Receipt.externalScientificSourceAcquiredByThisReceipt ≡ false
noExternalScientificAuthorityManufactured = refl

geometricDegreeStillSeparate :
  Receipt.geometricEndomorphismDegreeNormObserved ≡ false
geometricDegreeStillSeparate = refl

groessencharacterStillSeparate :
  Receipt.groessencharacterObserved ≡ false
groessencharacterStillSeparate = refl

globalEllipticLStillSeparate :
  Receipt.globalEllipticLSeriesAgreementObserved ≡ false
globalEllipticLStillSeparate = refl
