module DASHI.Base369Monster3BActualKernelSameElementValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as Same

selectedElementAndKernelClassAreExplicitlyWelded :
  Same.Actual3BKernelSameElementBoundary.selectedElementAttachedToCentralZetaClass
    Same.canonicalActual3BKernelSameElementBoundary
  ≡ true
selectedElementAndKernelClassAreExplicitlyWelded = refl

zetaAmplitudeCompilerIsAvailable :
  Same.Actual3BKernelSameElementBoundary.centralZetaAmplitude65610CompilerAvailable
    Same.canonicalActual3BKernelSameElementBoundary
  ≡ true
zetaAmplitudeCompilerIsAvailable = refl

ninetyCopyCharacterCompilerIsAvailable :
  Same.Actual3BKernelSameElementBoundary.ninetyHeisenbergCharacterIsotypyCompilerAvailable
    Same.canonicalActual3BKernelSameElementBoundary
  ≡ true
ninetyCopyCharacterCompilerIsAvailable = refl

trace53DoesNotIdentify3BByItself :
  Same.Actual3BKernelSameElementBoundary.trace53AloneIdentifiesMonster3B
    Same.canonicalActual3BKernelSameElementBoundary
  ≡ false
trace53DoesNotIdentify3BByItself = refl

characterIsotypyDoesNotConstructActionIntertwiner :
  Same.Actual3BKernelSameElementBoundary.characterIsotypyConstructsActionIntertwiner
    Same.canonicalActual3BKernelSameElementBoundary
  ≡ false
characterIsotypyDoesNotConstructActionIntertwiner = refl

actualZetaRecognitionRemainsOpen :
  Same.Actual3BKernelSameElementBoundary.actualZetaRecognitionProvedHere
    Same.canonicalActual3BKernelSameElementBoundary
  ≡ false
actualZetaRecognitionRemainsOpen = refl
