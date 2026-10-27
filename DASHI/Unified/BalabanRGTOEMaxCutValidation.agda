{-# OPTIONS --safe #-}
module DASHI.Unified.BalabanRGTOEMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)

open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

import DASHI.Unified.BalabanRGTOERegression as Balaban
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Physics as Physics

------------------------------------------------------------------------
-- Receipt completeness.
------------------------------------------------------------------------

receiptStressCauchyCompilerMatchesOwner :
  Balaban.stressCauchyModulusCompiler Balaban.canonicalBalabanRGTOEReceipt
  ≡
  Balaban.balabanStressCauchyModulusCompilerLevel
receiptStressCauchyCompilerMatchesOwner = refl

receiptStressCauchyPhysicalInsertionMatchesOwner :
  Balaban.stressCauchyPhysicalInsertion Balaban.canonicalBalabanRGTOEReceipt
  ≡
  Balaban.balabanStressCauchyPhysicalInsertionLevel
receiptStressCauchyPhysicalInsertionMatchesOwner = refl

receiptStressHilbertCompilerMatchesOwner :
  Balaban.stressHilbertBoundCompiler Balaban.canonicalBalabanRGTOEReceipt
  ≡
  Balaban.balabanStressHilbertBoundCompilerLevel
receiptStressHilbertCompilerMatchesOwner = refl

receiptStressHilbertPhysicalShellMatchesOwner :
  Balaban.stressHilbertPhysicalShell Balaban.canonicalBalabanRGTOEReceipt
  ≡
  Balaban.balabanStressHilbertPhysicalShellLevel
receiptStressHilbertPhysicalShellMatchesOwner = refl

receiptUniformKPAbsorptionStillFalse :
  Balaban.uniformKPAbsorptionProved Balaban.canonicalBalabanRGTOEReceipt
  ≡ false
receiptUniformKPAbsorptionStillFalse = refl

receiptOSWightmanConstructionStillFalse :
  Balaban.osWightmanContinuumConstructionProved
    Balaban.canonicalBalabanRGTOEReceipt
  ≡ false
receiptOSWightmanConstructionStillFalse = refl

receiptBlockSpinTransferStillFalse :
  Balaban.blockSpinTransferProved Balaban.canonicalBalabanRGTOEReceipt
  ≡ false
receiptBlockSpinTransferStillFalse = refl

receiptContinuumYangMillsStillFalse :
  Balaban.continuumYangMillsConstructed Balaban.canonicalBalabanRGTOEReceipt
  ≡ false
receiptContinuumYangMillsStillFalse = refl

receiptContinuumMassGapStillFalse :
  Balaban.continuumMassGapProved Balaban.canonicalBalabanRGTOEReceipt
  ≡ false
receiptContinuumMassGapStillFalse = refl

receiptTerminalPromotionStillFalse :
  Balaban.terminalPromotion Balaban.canonicalBalabanRGTOEReceipt
  ≡ false
receiptTerminalPromotionStillFalse = refl

receiptClayPromotionStillFalse :
  Balaban.clayPromotion Balaban.canonicalBalabanRGTOEReceipt
  ≡ false
receiptClayPromotionStillFalse = refl

------------------------------------------------------------------------
-- Consumer agreement.
------------------------------------------------------------------------

toeStressCauchyCompilerMatchesOwner :
  TOE.toeBalabanStressCauchyModulusCompilerLevel
  ≡
  Balaban.balabanStressCauchyModulusCompilerLevel
toeStressCauchyCompilerMatchesOwner = refl

unifierStressCauchyCompilerMatchesOwner :
  Unifier.toeBalabanStressCauchyModulusCompilerLevel
  ≡
  Balaban.balabanStressCauchyModulusCompilerLevel
unifierStressCauchyCompilerMatchesOwner = refl

physicsStressCauchyCompilerMatchesOwner :
  Physics.yangMillsBalabanStressCauchyModulusCompilerLevel
  ≡
  Balaban.balabanStressCauchyModulusCompilerLevel
physicsStressCauchyCompilerMatchesOwner = refl

toeStressHilbertCompilerMatchesOwner :
  TOE.toeBalabanStressHilbertBoundCompilerLevel
  ≡
  Balaban.balabanStressHilbertBoundCompilerLevel
toeStressHilbertCompilerMatchesOwner = refl

unifierStressHilbertCompilerMatchesOwner :
  Unifier.toeBalabanStressHilbertBoundCompilerLevel
  ≡
  Balaban.balabanStressHilbertBoundCompilerLevel
unifierStressHilbertCompilerMatchesOwner = refl

physicsStressHilbertCompilerMatchesOwner :
  Physics.yangMillsBalabanStressHilbertBoundCompilerLevel
  ≡
  Balaban.balabanStressHilbertBoundCompilerLevel
physicsStressHilbertCompilerMatchesOwner = refl

physicsUniformKPStillOpen :
  Balaban.balabanRGUniformKPAbsorptionOpenFlag ≡ false
physicsUniformKPStillOpen =
  Physics.yangMillsBalabanRGUniformKPAbsorptionStillOpen

physicsOSWightmanStillOpen :
  Balaban.balabanOSWightmanContinuumConstructionOpenFlag ≡ false
physicsOSWightmanStillOpen =
  Physics.yangMillsBalabanOSWightmanContinuumConstructionStillOpen

physicsContinuumStillOpen :
  Balaban.balabanRGContinuumConstructionOpenFlag ≡ false
physicsContinuumStillOpen =
  Physics.yangMillsBalabanRGContinuumConstructionStillOpen

physicsMassGapStillOpen :
  Balaban.balabanRGContinuumMassGapOpenFlag ≡ false
physicsMassGapStillOpen =
  Physics.yangMillsBalabanContinuumMassGapStillOpen

physicsTerminalStillOpen :
  Balaban.balabanTerminalPromotionOpenFlag ≡ false
physicsTerminalStillOpen =
  Physics.yangMillsBalabanTerminalPromotionStillOpen

physicsClayStillFalse :
  Balaban.balabanRGClayPromotionFlag ≡ false
physicsClayStillFalse =
  Physics.yangMillsBalabanClayPromotionStillFalse

------------------------------------------------------------------------
-- ZKP frame remains the existing typed contract.
------------------------------------------------------------------------

validationZKPFrame : Balaban.BalabanTOEZKPFrame
validationZKPFrame =
  Balaban.canonicalBalabanTOEZKPFrame
