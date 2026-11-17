module DASHI.Physics.CondensedMatter.MATBGQTMMatrixElementObserverReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record QTMMatrixElementObserverReceipt : Set where
  constructor qtm-matrix-element-observer-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    xiaoSourceDOI : String
    bmSourceDOI : String
    thetaDegFixture : String
    w0w1Ratio : String
    shellCount : String
    factorMinimum : String
    factorMaximum : String
    assertionsPassed : Bool

open QTMMatrixElementObserverReceipt public

canonicalQTMMatrixElementObserverReceipt : QTMMatrixElementObserverReceipt
canonicalQTMMatrixElementObserverReceipt =
  qtm-matrix-element-observer-receipt
    "scripts/matbg_qtm_matrix_element_observer.py"
    "Docs/evidence/matbg_qtm_matrix_element_observer_2026-10-16.json"
    "cad222054d173be33855801df1d8092f06b171498bf590cfe72dcf75b257255a"
    "10.1038/s41586-026-10378-x"
    "10.1073/pnas.1108174108"
    "1.10" "0.6" "3"
    "0.22349333217160083"
    "0.7546836020406058"
    true

record QTMMatrixElementObserverBoundary : Set where
  constructor qtm-matrix-element-observer-boundary
  field
    xiaoPtPsObserverSourcePaid : Bool
    bmEigenvectorBackendPaid : Bool
    sourceRatioUsed : Bool
    wavefunctionObserverExecutionPaid : Bool
    momentumDependenceNonconstantReceiptPaid : Bool
    qtmElectrostaticsReplayPaid : Bool
    probeSpectralFunctionReplayPaid : Bool
    interactingSelfEnergyPaid : Bool
    rawQTMDataUsed : Bool
    experimentalQTMFitPaid : Bool
    sameSampleEntropyPaid : Bool
    agdaKernelReceiptPaid : Bool

open QTMMatrixElementObserverBoundary public

canonicalQTMMatrixElementObserverBoundary : QTMMatrixElementObserverBoundary
canonicalQTMMatrixElementObserverBoundary =
  qtm-matrix-element-observer-boundary
    true true true true true
    false false false false false false false

record QTMMatrixElementObserverAttributionBoundary : Set where
  constructor qtm-matrix-element-observer-attribution-boundary
  field
    xiaoEtAlOwnPtPsExperimentalObserverRole : Bool
    bmOwnsSingleParticleWavefunctionBackendRole : Bool
    dashiOwnsNumericalObserverReplay : Bool
    genericWABReferenceIsNotSameSampleCalibration : Bool
    observerReplayDoesNotCreateExperimentalFit : Bool

open QTMMatrixElementObserverAttributionBoundary public

canonicalQTMMatrixElementObserverAttributionBoundary : QTMMatrixElementObserverAttributionBoundary
canonicalQTMMatrixElementObserverAttributionBoundary =
  qtm-matrix-element-observer-attribution-boundary true true true true true
