module DASHI.Physics.Closure.SyntheticRealizationWitness where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.ShellNeighborhoodClass as SNC
open import DASHI.Physics.LorentzNeighborhoodDynamicCandidate as LNDC
open import DASHI.Physics.SyntheticOneMinusShellRealization as SOM
open import DASHI.Physics.Signature31Canonical as S31C
  hiding (syntheticSignatureMatchesCanonical)
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness as SODW
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusOrientationSignatureBridge as SOSB
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusPromotionBridge as SOPB
  hiding (orientationJustified)

record SyntheticRealizationWitness : Set where
  field
    providerIsSynthetic :
      S31C.providerSource S31C.syntheticCoreProvider
      ≡ S31C.syntheticOneMinusSource
    shellNeighborhoodPreserved :
      SOM.shellNeighborhood ≡ SNC.oneMinusShellNeighborhood
    shell1ProfilePreserved :
      SOM.shell1Profile ≡ OPD.shell1_p3_q1
    shell2ProfilePreserved :
      SOM.shell2Profile ≡ OPD.shell2_p3_q1
    orientationJustified :
      SOSB.syntheticOrientationTag ≡ OSD.OrientationTag OSD.sig31
    promotionReady :
      SOPB.SyntheticPromotionBridge.promotionStatus SOPB.bridge
      ≡ SOPB.admissiblePromotionReady
    dynamicsReady :
      LNDC.LorentzNeighborhoodDynamicCandidate.status LNDC.syntheticReady
      ≡ LNDC.admissibleDynamicReady
    dynamicsWitnessPreservesShellNeighborhood :
      SODW.SyntheticOneMinusDynamicsWitness.shellNeighborhoodPreserved
        SODW.syntheticDynamicsWitness
      ≡ SOM.shellNeighborhood-theorem
    dynamicsWitnessPreservesShell1 :
      SODW.SyntheticOneMinusDynamicsWitness.shell1ProfilePreserved
        SODW.syntheticDynamicsWitness
      ≡ refl
    dynamicsWitnessPreservesShell2 :
      SODW.SyntheticOneMinusDynamicsWitness.shell2ProfilePreserved
        SODW.syntheticDynamicsWitness
      ≡ refl
    syntheticSignatureMatchesCanonical :
      S31C.signature31FromProvider S31C.syntheticCoreProvider
      ≡ S31C.signature31

syntheticRealizationWitness : SyntheticRealizationWitness
syntheticRealizationWitness =
  record
    { providerIsSynthetic = refl
    ; shellNeighborhoodPreserved = SOM.shellNeighborhood-theorem
    ; shell1ProfilePreserved =
        SODW.SyntheticOneMinusDynamicsWitness.shell1ProfilePreserved
          SODW.syntheticDynamicsWitness
    ; shell2ProfilePreserved =
        SODW.SyntheticOneMinusDynamicsWitness.shell2ProfilePreserved
          SODW.syntheticDynamicsWitness
    ; orientationJustified = SOSB.syntheticOrientationJustified
    ; promotionReady = refl
    ; dynamicsReady = refl
    ; dynamicsWitnessPreservesShellNeighborhood = refl
    ; dynamicsWitnessPreservesShell1 = refl
    ; dynamicsWitnessPreservesShell2 = refl
    ; syntheticSignatureMatchesCanonical = S31C.syntheticSignatureMatchesCanonical
    }
