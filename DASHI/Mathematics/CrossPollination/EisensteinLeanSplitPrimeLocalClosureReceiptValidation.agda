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

badPrimeLiteralReductionObserved :
  Receipt.badPrimeThreeLiteralReductionObserved ≡ true
badPrimeLiteralReductionObserved = refl

badPrimeLocalFactorStillUnpaid :
  Receipt.badPrimeThreeEllipticLocalFactorObserved ≡ false
badPrimeLocalFactorStillUnpaid = refl

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
