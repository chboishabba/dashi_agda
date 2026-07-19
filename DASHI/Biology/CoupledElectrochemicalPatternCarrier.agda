module DASHI.Biology.CoupledElectrochemicalPatternCarrier where

------------------------------------------------------------------------
-- Generic n-component electrochemical / excitable carrier.
--
-- This is deliberately substrate-neutral: components may represent chemical
-- species, cells, tissue compartments, organs, or coupled parts thereof.  The
-- record only exposes the ingredients required for mode selection.

open import DASHI.Biology.TuringPatternRegimeSurface using
  ( TuringInputVariable
  ; TuringRegime
  ; TuringPatternFamily
  )

record CoupledElectrochemicalCarrier : Set₁ where
  constructor coupledElectrochemicalCarrier
  field
    Component : Set
    State : Component → Set
    LocalInteraction : Component → Component → Set
    TransportLaw : Component → Component → Set
    BoundaryGeometry : Set
    ExternalDrive : Set
    EndogenousNoise : Set

    finiteOrIndexedBody : Set
    electrochemicalCoupling : Set
    localExcitationPresent : Set
    lateralInhibitionPresent : Set
    transportOrDiffusionPresent : Set

record PatternSelectionInput : Set₁ where
  constructor patternSelectionInput
  field
    carrier : CoupledElectrochemicalCarrier
    variables : TuringInputVariable → Set
    candidateRegime : TuringRegime
    candidateFamily : TuringPatternFamily

    wavelengthAmplification : Set
    wavelengthSuppression : Set
    symmetryConstraint : Set
    projectionGeometryAvailable : Set

------------------------------------------------------------------------
-- The carrier supports candidate pattern selection; it does not by itself
-- prove that a biological system instantiates a particular PDE or percept.

record CoupledCarrierBoundary : Set₁ where
  constructor coupledCarrierBoundary
  field
    input : PatternSelectionInput

    notExactTuringPDEWithoutParameters : Set
    notUniqueBiologicalMechanism : Set
    notPerceptByItself : Set
    notSemanticAuthority : Set
    notClinicalDiagnosis : Set
