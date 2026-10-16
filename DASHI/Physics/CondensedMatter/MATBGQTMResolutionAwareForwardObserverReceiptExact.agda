module DASHI.Physics.CondensedMatter.MATBGQTMResolutionAwareForwardObserverReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RESOLUTION-AWARE SYNTHETIC QTM FORWARD OBSERVER
--
-- Composes the finite BM wavefunction/matrix-element observer with Xiao et
-- al.'s source-bounded momentum/energy resolution coordinates.  The resulting
-- surface is theoretical/synthetic.  No experimental intensity arrays are
-- consumed and the absolute wAB scale remains a generic reference.
------------------------------------------------------------------------

record QTMResolutionAwareForwardObserverReceipt : Set where
  constructor qtm-resolution-aware-forward-observer-receipt
  field
    xiaoSourceDOI : String
    bmSourceDOI : String
    producer : String
    evidence : String
    thetaDeg : String
    w0OverW1 : String
    genericWABeV : String
    qSamples : String
    b1NormInvNm : String
    energyFWHMUpperBoundMeV : String
    momentumFWHMInvNm : String
    integratedSyntheticIntensity : String
    unbroadenedMatrixElementWeight : String
    peakEnergyMeV : String
    peakMomentumInvNm : String
    numericalForwardObserverPaid : Bool
    experimentalArraysUsed : Bool
    absoluteWABSampleCalibrated : Bool
    interactingSelfEnergyIncluded : Bool
    experimentalFitPaid : Bool

open QTMResolutionAwareForwardObserverReceipt public

canonicalQTMResolutionAwareForwardObserverReceipt : QTMResolutionAwareForwardObserverReceipt
canonicalQTMResolutionAwareForwardObserverReceipt =
  qtm-resolution-aware-forward-observer-receipt
    "10.1038/s41586-026-10378-x"
    "10.1073/pnas.1108174108"
    "scripts/matbg_qtm_resolution_aware_forward_observer.py"
    "Docs/evidence/matbg_qtm_resolution_aware_forward_observer_2026-10-16.json"
    "1.10"
    "0.6"
    "0.11"
    "41"
    "0.5662099702530637"
    "10"
    "0.03"
    "17.659947828215955"
    "17.66000159143856"
    "-0.5"
    "0.03993834598416361"
    true false false false false

record QTMResolutionAwareForwardObserverBoundary : Set where
  constructor qtm-resolution-aware-forward-observer-boundary
  field
    matrixElementObserverComposed : Bool
    sourceResolutionCoordinatesComposed : Bool
    syntheticResolutionAwareSurfaceExecuted : Bool
    genericAbsoluteScaleDoesNotBecomeSampleCalibration : Bool
    syntheticSurfaceDoesNotBecomeExperimentalArray : Bool
    nonInteractingSurfaceDoesNotBecomeInteractingFit : Bool

open QTMResolutionAwareForwardObserverBoundary public

canonicalQTMResolutionAwareForwardObserverBoundary : QTMResolutionAwareForwardObserverBoundary
canonicalQTMResolutionAwareForwardObserverBoundary =
  qtm-resolution-aware-forward-observer-boundary true true true true true true
