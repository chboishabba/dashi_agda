module DASHI.Physics.QFT.CarrierFunctorResidualInstances where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierToPhysicsInterpretationFunctor as CarrierFunctor
import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIsoSU3 as SU3Bridge

------------------------------------------------------------------------
-- Upstream Gate 1 residual witness bundle.
--
-- This file only packages already-inhabited witnesses.  It does not touch
-- the carrier functor surface and it does not close exact Standard Model
-- matching.  The SU(3) bridge is consumed here as a concrete witness bundle
-- so downstream wiring can import a single upstream module.

record Gate1ResidualUpstreamWitnessBundle : Setω where
  field
    filteredColimitLawReceipt :
      CarrierFunctor.FiniteSupportFilteredColimitLawReceipt

    dhrCompatibilityLawReceipt :
      CarrierFunctor.DHRSectorCompatibilityLawReceipt

    filteredColimitPrimitiveWitness :
      CarrierFunctor.CarrierToPhysicsMissingPrimitiveWitness
        CarrierFunctor.missingFilteredColimitPreservation

    dhrSectorCompatibilityPrimitiveWitness :
      CarrierFunctor.CarrierToPhysicsMissingPrimitiveWitness
        CarrierFunctor.missingDHRSectorCompatibility

    su3DepthQuotientIsoWitness :
      SU3Bridge.DepthQuotientIsoSU3Witness

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    dhrSectorCompatibilityPromoted :
      Bool

    dhrSectorCompatibilityPromotedIsFalse :
      dhrSectorCompatibilityPromoted ≡ false

    su3DepthQuotientIsoPromoted :
      Bool

    su3DepthQuotientIsoPromotedIsFalse :
      su3DepthQuotientIsoPromoted ≡ false

    residualBoundary :
      List String

open Gate1ResidualUpstreamWitnessBundle public

canonicalGate1ResidualUpstreamWitnessBundle :
  Gate1ResidualUpstreamWitnessBundle
canonicalGate1ResidualUpstreamWitnessBundle =
  record
    { filteredColimitLawReceipt =
        CarrierFunctor.canonicalFiniteSupportFilteredColimitLawReceipt
    ; dhrCompatibilityLawReceipt =
        CarrierFunctor.canonicalDHRSectorCompatibilityLawReceipt
    ; filteredColimitPrimitiveWitness =
        CarrierFunctor.missingFiniteSupportFilteredColimitPrimitiveWitness
    ; dhrSectorCompatibilityPrimitiveWitness =
        CarrierFunctor.missingDHRSectorCompatibilityPrimitiveWitness
    ; su3DepthQuotientIsoWitness =
        SU3Bridge.canonicalDepthQuotientIsoSU3Witness
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; dhrSectorCompatibilityPromoted =
        false
    ; dhrSectorCompatibilityPromotedIsFalse =
        refl
    ; su3DepthQuotientIsoPromoted =
        false
    ; su3DepthQuotientIsoPromotedIsFalse =
        refl
    ; residualBoundary =
        "filtered colimit and DHR compatibility are packaged from the canonical carrier-functor receipts"
        ∷ "the SU(3) bridge is packaged from canonicalDepthQuotientIsoSU3Witness"
        ∷ "exact Standard Model matching remains open and is not bundled here"
        ∷ []
    }

filteredColimitPreservationWitness :
  CarrierFunctor.FiniteSupportFilteredColimitLawReceipt
filteredColimitPreservationWitness =
  Gate1ResidualUpstreamWitnessBundle.filteredColimitLawReceipt
    canonicalGate1ResidualUpstreamWitnessBundle

dhrSectorCompatibilityWitness :
  CarrierFunctor.DHRSectorCompatibilityLawReceipt
dhrSectorCompatibilityWitness =
  Gate1ResidualUpstreamWitnessBundle.dhrCompatibilityLawReceipt
    canonicalGate1ResidualUpstreamWitnessBundle

filteredColimitPrimitiveWitnessTerm :
  CarrierFunctor.CarrierToPhysicsMissingPrimitiveWitness
    CarrierFunctor.missingFilteredColimitPreservation
filteredColimitPrimitiveWitnessTerm =
  Gate1ResidualUpstreamWitnessBundle.filteredColimitPrimitiveWitness
    canonicalGate1ResidualUpstreamWitnessBundle

dhrSectorCompatibilityPrimitiveWitnessTerm :
  CarrierFunctor.CarrierToPhysicsMissingPrimitiveWitness
    CarrierFunctor.missingDHRSectorCompatibility
dhrSectorCompatibilityPrimitiveWitnessTerm =
  Gate1ResidualUpstreamWitnessBundle.dhrSectorCompatibilityPrimitiveWitness
    canonicalGate1ResidualUpstreamWitnessBundle

su3DepthQuotientIsoWitnessTerm :
  SU3Bridge.DepthQuotientIsoSU3Witness
su3DepthQuotientIsoWitnessTerm =
  Gate1ResidualUpstreamWitnessBundle.su3DepthQuotientIsoWitness
    canonicalGate1ResidualUpstreamWitnessBundle
