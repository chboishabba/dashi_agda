module DASHI.Physics.Closure.Gate3TheoremPackageCurrentStateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.FullUnificationPublicationRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.Gate3DensityOfCarrierCoreConstructedReceipt as Density
import DASHI.Physics.Closure.Gate3MoscoRecoveryConstructedReceipt as Mosco
import DASHI.Physics.Closure.Gate3NoSpectralPollutionConstructedReceipt as NoPollution
import DASHI.Physics.Closure.Gate3MassShellBridgeConstructedReceipt as MassShell
import DASHI.Physics.Closure.Gate3UniformSeparationConstructedReceipt as Separation

data Gate3TheoremPackageCurrentStateStatus : Set where
  gate3TheoremPackageRecorded_failClosedPromotion :
    Gate3TheoremPackageCurrentStateStatus

data Gate3TheoremPackageLane : Set where
  gate3DensityLaneDone :
    Gate3TheoremPackageLane

  gate3MoscoLaneDone :
    Gate3TheoremPackageLane

  gate3NoSpectralPollutionLaneDone :
    Gate3TheoremPackageLane

  gate3MassShellLaneDone :
    Gate3TheoremPackageLane

  gate3UniformSeparationLaneDone :
    Gate3TheoremPackageLane

  gate3PromotionStillBlocked :
    Gate3TheoremPackageLane

canonicalGate3TheoremPackageLanes :
  List Gate3TheoremPackageLane
canonicalGate3TheoremPackageLanes =
  gate3DensityLaneDone
  ∷ gate3MoscoLaneDone
  ∷ gate3NoSpectralPollutionLaneDone
  ∷ gate3MassShellLaneDone
  ∷ gate3UniformSeparationLaneDone
  ∷ gate3PromotionStillBlocked
  ∷ []

data Gate3TheoremPackagePromotion : Set where

gate3TheoremPackagePromotionImpossibleHere :
  Gate3TheoremPackagePromotion →
  ⊥
gate3TheoremPackagePromotionImpossibleHere ()

gate3TheoremPackageSummary : String
gate3TheoremPackageSummary =
  "Gate 3 current theorem package: density, Mosco recovery, no-spectral-pollution, mass-shell bridge, and PAWOTG uniform separation are all recorded as closed at their owning theorem surfaces, while the publication roadmap still keeps Gate 3 promotion fail-closed."

record Gate3TheoremPackageCurrentStateReceipt : Setω where
  field
    status :
      Gate3TheoremPackageCurrentStateStatus

    statusIsCanonical :
      status ≡ gate3TheoremPackageRecorded_failClosedPromotion

    roadmapReceipt :
      Roadmap.FullUnificationPublicationRoadmapReceipt

    roadmapGate3StillFalse :
      Roadmap.FullUnificationPublicationRoadmapReceipt.gate3Promoted
        roadmapReceipt
      ≡
      false

    densityReceipt :
      Density.Gate3DensityOfCarrierCoreConstructedReceipt

    densityRecorded :
      Density.densityOfCarrierCoreConstructed densityReceipt ≡ true

    moscoReceipt :
      Mosco.Gate3MoscoRecoveryConstructedReceipt

    moscoRecorded :
      Mosco.moscoConditionIConstructedFlag moscoReceipt ≡ true

    noSpectralPollutionReceipt :
      NoPollution.Gate3NoSpectralPollutionConstructedReceipt

    noSpectralPollutionRecorded :
      NoPollution.noSpectralPollutionConstructed
        noSpectralPollutionReceipt
      ≡
      true

    massShellReceipt :
      MassShell.Gate3MassShellBridgeConstructedReceipt

    massShellRecorded :
      MassShell.massShellBridgeConstructed massShellReceipt ≡ true

    uniformSeparationReceipt :
      Separation.Gate3UniformSeparationConstructedReceipt

    uniformSeparationRecorded :
      Separation.infANPositiveConstructedHere uniformSeparationReceipt ≡ true

    theoremPackageLanes :
      List Gate3TheoremPackageLane

    theoremPackageLanesAreCanonical :
      theoremPackageLanes ≡ canonicalGate3TheoremPackageLanes

    gate3TheoremPackageRecorded :
      Bool

    gate3TheoremPackageRecordedIsTrue :
      gate3TheoremPackageRecorded ≡ true

    gate3PromotionStillBlockedFlag :
      Bool

    gate3PromotionStillBlockedFlagIsTrue :
      gate3PromotionStillBlockedFlag ≡ true

    clayPromotionStillBlocked :
      Bool

    clayPromotionStillBlockedIsTrue :
      clayPromotionStillBlocked ≡ true

    summary :
      String

    summaryIsCanonical :
      summary ≡ gate3TheoremPackageSummary

    promotionFlags :
      List Gate3TheoremPackagePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3TheoremPackageCurrentStateReceipt public

canonicalGate3TheoremPackageCurrentStateReceipt :
  Gate3TheoremPackageCurrentStateReceipt
canonicalGate3TheoremPackageCurrentStateReceipt =
  record
    { status =
        gate3TheoremPackageRecorded_failClosedPromotion
    ; statusIsCanonical =
        refl
    ; roadmapReceipt =
        Roadmap.canonicalFullUnificationPublicationRoadmapReceipt
    ; roadmapGate3StillFalse =
        refl
    ; densityReceipt =
        Density.canonicalGate3DensityOfCarrierCoreConstructedReceipt
    ; densityRecorded =
        refl
    ; moscoReceipt =
        Mosco.canonicalGate3MoscoRecoveryConstructedReceipt
    ; moscoRecorded =
        refl
    ; noSpectralPollutionReceipt =
        NoPollution.canonicalGate3NoSpectralPollutionConstructedReceipt
    ; noSpectralPollutionRecorded =
        refl
    ; massShellReceipt =
        MassShell.canonicalGate3MassShellBridgeConstructedReceipt
    ; massShellRecorded =
        refl
    ; uniformSeparationReceipt =
        Separation.canonicalGate3UniformSeparationConstructedReceipt
    ; uniformSeparationRecorded =
        refl
    ; theoremPackageLanes =
        canonicalGate3TheoremPackageLanes
    ; theoremPackageLanesAreCanonical =
        refl
    ; gate3TheoremPackageRecorded =
        true
    ; gate3TheoremPackageRecordedIsTrue =
        refl
    ; gate3PromotionStillBlockedFlag =
        true
    ; gate3PromotionStillBlockedFlagIsTrue =
        refl
    ; clayPromotionStillBlocked =
        true
    ; clayPromotionStillBlockedIsTrue =
        refl
    ; summary =
        gate3TheoremPackageSummary
    ; summaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }
