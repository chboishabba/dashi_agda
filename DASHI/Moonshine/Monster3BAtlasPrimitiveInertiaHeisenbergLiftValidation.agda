module DASHI.Moonshine.Monster3BAtlasPrimitiveInertiaHeisenbergLiftValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BAtlasPrimitiveInertiaHeisenbergLiftReceiptExact as Receipt
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Phase

primitiveCompressionPaid :
  Receipt.primitiveCompressionOrder728Paid Receipt.canonicalBoundary ≡ true
primitiveCompressionPaid = refl

centerPreservingPaid :
  Receipt.selectedWordCenterPreservingPaid Receipt.canonicalBoundary ≡ true
centerPreservingPaid = refl

heisenbergLiftPaid :
  Receipt.selectedWordHeisenbergLiftRuntimePaid Receipt.canonicalBoundary ≡ true
heisenbergLiftPaid = refl

phaseImageIsZeta : Receipt.preferredWordPhaseImage ≡ Phase.phaseZeta
phaseImageIsZeta = refl

actualPhaseResolvedMonsterSectorStillOpen :
  Receipt.actualPhaseResolvedMonsterSectorActionPaid Receipt.canonicalBoundary ≡ false
actualPhaseResolvedMonsterSectorStillOpen = refl
