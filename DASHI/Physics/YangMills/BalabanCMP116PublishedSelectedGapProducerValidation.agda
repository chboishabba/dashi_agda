{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedSelectedGapProducerValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116PublishedSelectedGapProducerExact as B
compilerOwned : B.publishedSelectedCMP116CompilerLevel ≡ machineChecked
compilerOwned = refl
publishedLocalizationImported :
  B.publishedCMP116LocalizationAuthorityLevel ≡ standardImported
publishedLocalizationImported = refl
selectedApplicationStillPhysical :
  B.selectedCMP116SameObjectApplicationLevel ≡ conditional
selectedApplicationStillPhysical = refl
selectedCalibrationStillPhysical :
  B.selectedCMP116EnvelopeCalibrationLevel ≡ conditional
selectedCalibrationStillPhysical = refl
