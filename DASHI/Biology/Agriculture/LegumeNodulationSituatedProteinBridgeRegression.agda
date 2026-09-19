module DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact as Nod

bakhoumDOIIsAttached :
  Attribution.doiState (Nod.attributedSource Nod.bakhoum2015) ≡
  Attribution.doiRecorded "10.1007/s00248-014-0507-1"
bakhoumDOIIsAttached = refl

nowakDOIIsAttached :
  Attribution.doiState (Nod.attributedSource Nod.nowak2004) ≡
  Attribution.doiRecorded "10.1016/j.carres.2004.02.013"
nowakDOIIsAttached = refl

rasanenDOIIsAttached :
  Attribution.doiState (Nod.attributedSource Nod.rasanen1999) ≡
  Attribution.doiRecorded "10.1111/j.1574-6941.1999.tb00561.x"
rasanenDOIIsAttached = refl

tsitsikliDOIIsAttached :
  Attribution.doiState (Nod.attributedSource Nod.tsitsikli2025) ≡
  Attribution.doiRecorded "10.1038/s41586-025-09696-3"
tsitsikliDOIIsAttached = refl

receptorIdentityIsNotSignalAdequate :
  Nod.receptorIdentityAloneAdequate Nod.canonicalNodulationBoundary ≡ false
receptorIdentityIsNotSignalAdequate = refl

recognitionDoesNotCreateNodule :
  Nod.nodFactorRecognitionImpliesSuccessfulNodulation Nod.canonicalNodulationBoundary ≡ false
recognitionDoesNotCreateNodule = refl

noduleDoesNotCreateActiveNitrogenase :
  Nod.successfulNodulationImpliesActiveNitrogenase Nod.canonicalNodulationBoundary ≡ false
noduleDoesNotCreateActiveNitrogenase = refl

activeNitrogenaseDoesNotCreatePlantDelivery :
  Nod.activeNitrogenaseImpliesIntegratedFixedNDelivery Nod.canonicalNodulationBoundary ≡ false
activeNitrogenaseDoesNotCreatePlantDelivery = refl

lotusBarleyDoesNotBecomeAcaciaMechanism :
  Nod.lotusBarleyMechanismTransfersToAcacia Nod.canonicalNodulationBoundary ≡ false
lotusBarleyDoesNotBecomeAcaciaMechanism = refl
