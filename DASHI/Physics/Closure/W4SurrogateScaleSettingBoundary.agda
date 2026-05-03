module DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand
import DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker as Blocker
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4StrictPhysicalScaleSettingLaneObligation as Obligation

------------------------------------------------------------------------
-- W4j surrogate scale-setting boundary.
--
-- This module tests whether the Candidate256 quotient/cross-band law can
-- support a dimensionless scale-like map.  It deliberately does not satisfy
-- the strict physical scale-setting obligation as physical calibration.

Candidate256QuotientClass : Set
Candidate256QuotientClass =
  Handoff.QuotientCarrier Next.canonicalCandidate256QuotientLaw

SurrogateScaleCarrier : Set
SurrogateScaleCarrier = Nat

candidate256SurrogateScale :
  Candidate256QuotientClass →
  SurrogateScaleCarrier
candidate256SurrogateScale q =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.I×
    Next.canonicalCandidate256QuotientLaw
    (q , q)

candidate256LeftQuotientClass :
  Candidate256QuotientClass
candidate256LeftQuotientClass =
  Handoff.leftQuotientClass Next.canonicalCandidate256QuotientLaw

candidate256RightQuotientClass :
  Candidate256QuotientClass
candidate256RightQuotientClass =
  Handoff.rightQuotientClass Next.canonicalCandidate256QuotientLaw

candidate256SurrogateLeftVisible :
  candidate256SurrogateScale candidate256LeftQuotientClass
  ≡
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.I×
    Next.canonicalCandidate256QuotientLaw
    (candidate256LeftQuotientClass , candidate256LeftQuotientClass)
candidate256SurrogateLeftVisible = refl

candidate256SurrogateRightVisible :
  candidate256SurrogateScale candidate256RightQuotientClass
  ≡
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.I×
    Next.canonicalCandidate256QuotientLaw
    (candidate256RightQuotientClass , candidate256RightQuotientClass)
candidate256SurrogateRightVisible = refl

SurrogateLchemScalePreservation :
  Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw →
  Set
SurrogateLchemScalePreservation _ =
  candidate256SurrogateScale candidate256LeftQuotientClass
    ≡
  candidate256SurrogateScale candidate256LeftQuotientClass
  ×
  candidate256SurrogateScale candidate256RightQuotientClass
    ≡
  candidate256SurrogateScale candidate256RightQuotientClass

candidate256SurrogateLchemPreserves :
  (law : Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw) →
  SurrogateLchemScalePreservation law
candidate256SurrogateLchemPreserves _ =
  refl , refl

candidate256SurrogateScaleSeparatesAtWitness :
  candidate256SurrogateScale candidate256LeftQuotientClass
  ≡
  candidate256SurrogateScale candidate256RightQuotientClass →
  ⊥
candidate256SurrogateScaleSeparatesAtWitness =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.I×BandSensitivityWitness
    Next.canonicalCandidate256QuotientLaw

candidate256SurrogateScaleSettingLaneFields :
  Obligation.Candidate256ScaleSettingLaneFields
candidate256SurrogateScaleSettingLaneFields =
  record
    { physicalScaleCarrier =
        SurrogateScaleCarrier
    ; quotientClassScaleMap =
        candidate256SurrogateScale
    ; LchemScalePreservationLaw =
        SurrogateLchemScalePreservation
    }

candidate256SurrogateScaleSettingFieldsNeeded :
  Obligation.candidate256ScaleSettingFieldsNeeded
    candidate256SurrogateScaleSettingLaneFields
candidate256SurrogateScaleSettingFieldsNeeded =
  candidate256SurrogateLchemPreserves

record Candidate256SurrogateScaleSettingBoundaryReceipt : Setω where
  field
    strictObligationReceipt :
      Obligation.Candidate256ScaleSettingLaneObligationReceipt

    surrogateFields :
      Obligation.Candidate256ScaleSettingLaneFields

    surrogateLchemPreservation :
      Obligation.candidate256ScaleSettingFieldsNeeded surrogateFields

    scaleCarrierLabel : String
    scaleMapLabel : String
    preservationLabel : String

    downstreamStillBlocked :
      List Blocker.StrictPhysicalMissingIngredient

    downstreamBlockerLabels :
      List String

    noPhysicalCalibrationBoundary :
      List String

canonicalCandidate256SurrogateScaleSettingBoundaryReceipt :
  Candidate256SurrogateScaleSettingBoundaryReceipt
canonicalCandidate256SurrogateScaleSettingBoundaryReceipt =
  record
    { strictObligationReceipt =
        Obligation.canonicalCandidate256ScaleSettingLaneObligationReceipt
    ; surrogateFields =
        candidate256SurrogateScaleSettingLaneFields
    ; surrogateLchemPreservation =
        candidate256SurrogateScaleSettingFieldsNeeded
    ; scaleCarrierLabel =
        "Nat-valued dimensionless surrogate scale carrier"
    ; scaleMapLabel =
        "q ↦ I× (q , q), the diagonal Candidate256 quotient/cross-band observable"
    ; preservationLabel =
        "L_chem witness preserves defined left/right surrogate scale endpoints only"
    ; downstreamStillBlocked =
        Blocker.missingScaleSettingLaw
        ∷ Blocker.missingSpectralObservableMap
        ∷ Blocker.missingBondingInterpretation
        ∷ Blocker.missingEmpiricalPhysicalValidation
        ∷ []
    ; downstreamBlockerLabels =
        "physical units and calibration remain missing"
        ∷ "spectral observable mapping remains missing"
        ∷ "bonding interpretation remains missing"
        ∷ "empirical physical validation remains missing"
        ∷ []
    ; noPhysicalCalibrationBoundary =
        "This is a dimensionless surrogate scale map, not a physical unit system"
        ∷ "The Nat carrier is not calibrated to energy, length, time, mass, charge, or any empirical unit"
        ∷ "The preservation law only records that L_chem reaches the quotient-class surrogate endpoints"
        ∷ "No spectra, bonding, empirical validation, or physical closure claim is inhabited here"
        ∷ "The strict physical scale-setting obligation remains blocked until physical units and calibration are supplied"
        ∷ []
    }
