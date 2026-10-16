module DASHI.Moonshine.Monster3BLinearIsotypicCurrentMaxCutValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BLinearIsotypicCurrentMaxCutExact as Cut

boundary = Cut.canonicalBoundary

schurTailPaidAtSource :
  Cut.genericSchurMultiplicityCoordinatesSourceWritten boundary ≡ true
schurTailPaidAtSource = refl

coordinateRecoveryPaidAtSource :
  Cut.genericCoordinateEvaluationRecoverySourceWritten boundary ≡ true
coordinateRecoveryPaidAtSource = refl

actualPacketTyped : Cut.actualInputPacketTyped boundary ≡ true
actualPacketTyped = refl

hZetaClosesAfterPacket : Cut.hZetaRecognitionClosesAfterActualPacket boundary ≡ true
hZetaClosesAfterPacket = refl

actualClassifierStillOpen : Cut.actualMonsterSimpleTypeClassifierPaid boundary ≡ false
actualClassifierStillOpen = refl

actualNormalizerStillOpen : Cut.actualSuzukiNormalizerActionPaid boundary ≡ false
actualNormalizerStillOpen = refl

fin90NotPrerequisite : Cut.fin90BasisNeededBeforeRepresentationRecognition boundary ≡ false
fin90NotPrerequisite = refl
