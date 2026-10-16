module DASHI.Mathematics.CrossPollination.EisensteinLeanJZeroCMOrderActionReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution
import DASHI.Mathematics.CrossPollination.EisensteinLeanJZeroCMOrderActionReceiptExact as Receipt

leanCMReceiptIsFormalReconstruction :
  Receipt.leanCMClaimOrigin ≡ Attribution.leanFormalReconstruction
leanCMReceiptIsFormalReconstruction = refl

leanNativePointGroupEndomorphismObserved :
  Receipt.leanNativePointGroupEndomorphismSourceObserved ≡ true
leanNativePointGroupEndomorphismObserved = refl

leanQuadraticRelationObserved :
  Receipt.leanEisensteinQuadraticRelationSourceObserved ≡ true
leanQuadraticRelationObserved = refl

leanOrderActionObserved :
  Receipt.leanEisensteinOrderActionSourceObserved ≡ true
leanOrderActionObserved = refl

noLeanProofObjectImported :
  Receipt.leanProofObjectImportedIntoAgda ≡ false
noLeanProofObjectImported = refl

noAgdaCMTheoremManufactured :
  Receipt.agdaCMEndomorphismTheoremInhabitedFromReceipt ≡ false
noAgdaCMTheoremManufactured = refl

noFaithfulEmbeddingManufactured :
  Receipt.leanFaithfulGeometricCMEmbeddingObserved ≡ false
noFaithfulEmbeddingManufactured = refl

noHeckeAuthorityManufactured :
  Receipt.leanHeckeCharacterObserved ≡ false
noHeckeAuthorityManufactured = refl

noExternalScientificSourceAcquired :
  Receipt.externalScientificSourceAcquiredByThisReceipt ≡ false
noExternalScientificSourceAcquired = refl
