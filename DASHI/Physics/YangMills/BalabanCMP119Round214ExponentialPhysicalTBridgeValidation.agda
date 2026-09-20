module DASHI.Physics.YangMills.BalabanCMP119Round214ExponentialPhysicalTBridgeValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Round214ExponentialPhysicalTBridgeExact as B

physicalTCompilerOwned :
  B.round214ExponentialPhysicalTCompilerLevel ≡ machineChecked
physicalTCompilerOwned = refl

physicalTAssemblyCompilerOwned :
  B.round214ExponentialPhysicalTAssemblyCompilerLevel ≡ machineChecked
physicalTAssemblyCompilerOwned = refl

sourceExponentialMeaningRemainsPhysical :
  B.literalOperationActionUsesRound214ExponentialLevel ≡ conditional
sourceExponentialMeaningRemainsPhysical = refl

round214ExponentialPhysicalTRemainsPhysical :
  B.literalRound214ExponentialIsPhysicalTOperationLevel ≡ conditional
round214ExponentialPhysicalTRemainsPhysical = refl

backgroundAdapterRemainsPhysical :
  B.slowFieldToRound214BackgroundLevel ≡ conditional
backgroundAdapterRemainsPhysical = refl

embeddingInjectivityRemainsFoundational :
  B.injectiveRationalRealEmbeddingLevel ≡ conditional
embeddingInjectivityRemainsFoundational = refl

positiveSupportRemainsPhysical :
  B.literalRound214ExponentialPositiveSupportLevel ≡ conditional
positiveSupportRemainsPhysical = refl
