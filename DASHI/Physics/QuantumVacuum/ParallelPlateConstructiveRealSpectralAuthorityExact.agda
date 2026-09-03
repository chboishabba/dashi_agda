module DASHI.Physics.QuantumVacuum.ParallelPlateConstructiveRealSpectralAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as CRS
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset
import DASHI.Physics.QuantumVacuum.ParallelPlateConstructiveRealScalarBridgeExact as ScalarBridge

------------------------------------------------------------------------
-- CONSTRUCTIVE-REAL SPECTRAL AUTHORITY FOR THE CASIMIR LANE
--
-- The repo already contains reciprocal/nonnegative-square-root structure and a
-- constructive exponential package.  This owner records the same-object welds
-- needed for the parallel-plate frequency and a smooth regulator to use those
-- existing operations rather than introducing application-local surrogates.
------------------------------------------------------------------------

record ParallelPlateConstructiveRealSpectralAuthority
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    scalarPackage : ScalarBridge.CasimirConstructiveRealAnalyticPackage kernel

    realDivisionSqrt :
      Polar.RealDivisionAndSquareRoot
        (ScalarBridge.real scalarPackage)

    exponential :
      CRS.ConstructedRealExponential
        (ScalarBridge.real scalarPackage)

    spectrum : Cutset.ParallelPlateSpectralModel kernel

    spectrumRootIsConstructiveSqrt : Set
    spectrumDivisionIsConstructiveReciprocal : Set
    halfInZeroPointLawIsConstructiveHalf : Set

    RegulatorParameter : Set
    regulatorParameterValue : RegulatorParameter → CRS.Real (ScalarBridge.real scalarPackage)

    smoothRegulatorWeight :
      RegulatorParameter →
      CRS.Real (ScalarBridge.real scalarPackage) →
      CRS.Real (ScalarBridge.real scalarPackage)

    regulatorUsesConstructiveExponential : Set
    regulatorTendsToOnePointwise : Set

    authorityReading : String

open ParallelPlateConstructiveRealSpectralAuthority public

------------------------------------------------------------------------
-- Analytic obligations exposed in the reverse direction.
------------------------------------------------------------------------

record ConstructiveRealSpectralObligations
    (kernel : Casimir.CasimirScalarModel)
    (A : ParallelPlateConstructiveRealSpectralAuthority kernel) : Set₁ where
  field
    frequencyRadicandNonnegative : Set
    plateSeparationNonzeroForReciprocal : Set
    regulatorParameterPositive : Set
    regulatorWeightBounded : Set
    regulatorWeightPointwiseLimit : regulatorTendsToOnePointwise A
    zeroPointWeightSameObject : Set
    reading : String

open ConstructiveRealSpectralObligations public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ExistingSqrtAutomaticallyProvesCasimirDispersion : Set where

data ExistingExponentialAutomaticallyProvesRegulatorConvergence : Set where

sqrtStructureDoesNotAutoProveDispersion :
  ExistingSqrtAutomaticallyProvesCasimirDispersion → ⊥
sqrtStructureDoesNotAutoProveDispersion ()

expStructureDoesNotAutoProveRegulatorLimit :
  ExistingExponentialAutomaticallyProvesRegulatorConvergence → ⊥
expStructureDoesNotAutoProveRegulatorLimit ()

record ConstructiveRealSpectralStatus : Set where
  field
    constructiveReciprocalSqrtShapeExists : Bool
    constructiveExponentialShapeExists : Bool
    casimirSpectralWeldInterfaceOwned : Bool
    physicalDispersionWeldClosed : Bool
    regulatorEstimateClosed : Bool

    constructiveReciprocalSqrtShapeExistsIsTrue :
      constructiveReciprocalSqrtShapeExists ≡ true
    constructiveExponentialShapeExistsIsTrue :
      constructiveExponentialShapeExists ≡ true
    casimirSpectralWeldInterfaceOwnedIsTrue :
      casimirSpectralWeldInterfaceOwned ≡ true
    physicalDispersionWeldClosedIsFalse : physicalDispersionWeldClosed ≡ false
    regulatorEstimateClosedIsFalse : regulatorEstimateClosed ≡ false

open ConstructiveRealSpectralStatus public

canonicalConstructiveRealSpectralStatus : ConstructiveRealSpectralStatus
canonicalConstructiveRealSpectralStatus = record
  { constructiveReciprocalSqrtShapeExists = true
  ; constructiveExponentialShapeExists = true
  ; casimirSpectralWeldInterfaceOwned = true
  ; physicalDispersionWeldClosed = false
  ; regulatorEstimateClosed = false
  ; constructiveReciprocalSqrtShapeExistsIsTrue = refl
  ; constructiveExponentialShapeExistsIsTrue = refl
  ; casimirSpectralWeldInterfaceOwnedIsTrue = refl
  ; physicalDispersionWeldClosedIsFalse = refl
  ; regulatorEstimateClosedIsFalse = refl
  }
