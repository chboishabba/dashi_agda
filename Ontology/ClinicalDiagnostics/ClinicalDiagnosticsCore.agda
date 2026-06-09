module Ontology.ClinicalDiagnostics.ClinicalDiagnosticsCore where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Boundaries.ClayYMGap as Clay
import DASHI.Physics.Boundaries.HiggsPDGBoundary as Higgs
import DASHI.Physics.QFT.DHRThermodynamicLimitBoundary as DHR

------------------------------------------------------------------------
-- Clinical diagnostics core.
--
-- This module is intentionally abstract: it does not invent a new
-- diagnostic theory, but packages the canonical boundary receipts already
-- present in the repository into one typed core record that downstream
-- consumers can reuse without bypassing the boundary surfaces.

data ClinicalDiagnosticAxis : Set where
  massGapAxis :
    ClinicalDiagnosticAxis

  electroweakAxis :
    ClinicalDiagnosticAxis

  thermodynamicLimitAxis :
    ClinicalDiagnosticAxis

canonicalClinicalDiagnosticAxes :
  List ClinicalDiagnosticAxis
canonicalClinicalDiagnosticAxes =
  massGapAxis
  ∷ electroweakAxis
  ∷ thermodynamicLimitAxis
  ∷ []

record ClinicalDiagnosticsCore : Setω where
  field
    clayYMGapReceipt :
      Clay.ClayYMGapReceipt

    higgsPDGBoundaryReceipt :
      Higgs.HiggsPDGBoundaryReceipt

    dhrThermodynamicLimitBoundaryReceipt :
      DHR.DHRThermodynamicLimitBoundaryReceipt

    diagnosticAxes :
      List ClinicalDiagnosticAxis

    diagnosticAxesAreCanonical :
      diagnosticAxes ≡ canonicalClinicalDiagnosticAxes

    boundaryOnly :
      Bool

    boundaryOnlyIsFalse :
      boundaryOnly ≡ false

    clinicalDiagnosticsNotes :
      List String

open ClinicalDiagnosticsCore public

canonicalClinicalDiagnosticsCore :
  ClinicalDiagnosticsCore
canonicalClinicalDiagnosticsCore =
  record
    { clayYMGapReceipt =
        Clay.canonicalClayYMGapReceipt
    ; higgsPDGBoundaryReceipt =
        Higgs.canonicalHiggsPDGBoundaryReceipt
    ; dhrThermodynamicLimitBoundaryReceipt =
        DHR.canonicalDHRThermodynamicLimitBoundaryReceipt
    ; diagnosticAxes =
        canonicalClinicalDiagnosticAxes
    ; diagnosticAxesAreCanonical =
        refl
    ; boundaryOnly =
        false
    ; boundaryOnlyIsFalse =
        refl
    ; clinicalDiagnosticsNotes =
        "The diagnostic core reuses the canonical Clay/YM mass-gap boundary receipt"
        ∷ "The diagnostic core reuses the canonical Higgs/PDG boundary receipt"
        ∷ "The diagnostic core reuses the canonical DHR thermodynamic-limit boundary receipt"
        ∷ "The core remains boundary-only and does not promote any new diagnosis theorem"
        ∷ []
    }

canonicalClinicalDiagnosticsCoreIsBoundaryOnly :
  boundaryOnly canonicalClinicalDiagnosticsCore ≡ false
canonicalClinicalDiagnosticsCoreIsBoundaryOnly =
  refl
