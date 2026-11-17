module DASHI.Physics.Photovoltaic.GaAs111MeasuredMassAdversarialExact where

-- PV P1d: REFEREED EXTERNAL SPECTROSCOPY, not self-fit to our Hamiltonian.
-- Molenkamp, Eppenga, 't Hooft, Dawson, Foxon, Moore:
-- Phys Rev B 38, 4314 (1988), DOI 10.1103/PhysRevB.38.4314
-- Excitation spectra of (001), (111)B and (310) GaAs/(Al,Ga)As QWs.
-- Reported mass values: mHH001=0.34m0; mLH001=0.094m0; mHH111=0.7m0.
-- The source describes masses extracted with an 8-band QW model;
-- they are not raw continuum band curvatures in an identical wafer.
--
-- Exact rational negative controls against a Gamma-only six-band
-- Luttinger mass reconstruction from gamma=(6.98,2.06,2.93).
-- This is a mismatch witness, NOT a fitted material/electricity theorem.
-- Agda Golden acceptance still OPEN.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Photovoltaic.GaAs111OpticalDeviceSourceWeldExact as Original

data False : Set where

-- Six-band Gamma-point reciprocal curvatures, exact fraction arithmetic:
-- mHH001/m0 = 1/(6.98 - 2*2.06) = 50/143.
-- mLH001/m0 = 1/(6.98 + 2*2.06) = 10/111.
-- mHH111/m0 = 1/(6.98 - 2*2.93) = 25/28.
-- Empirical orientation-QW inferred values as published decimals:
-- mHH001=17/50, mLH001=47/500, mHH111=7/10.

predicted001HHCannotEqual1988Observed :
  50 * 50 ≡ 17 * 143 -> False
predicted001HHCannotEqual1988Observed ()

predicted001LHCannotEqual1988Observed :
  10 * 500 ≡ 47 * 111 -> False
predicted001LHCannotEqual1988Observed ()

predicted111HHCannotEqual1988Observed :
  25 * 10 ≡ 7 * 28 -> False
predicted111HHCannotEqual1988Observed ()

-- The 111 HH discrepancy is ~27.55 percent relative to the
-- source-inferred 0.7. This is NOT a statement of measurement sigma.
predicted111ExceedsObservedCrossProduct :
  25 * 10 ≡ 250
predicted111ExceedsObservedCrossProduct = refl

observed111CrossProduct :
  7 * 28 ≡ 196
observed111CrossProduct = refl

-- Distinguish the observational domains BEFORE asking for any mapping:
-- reconstructed bulk curvature, inferred QW effective mass, exciton
-- fine structure, measured absorptance, and terminal power are separate.
data ObservationKind : Set where
  BulkGammaCurvature : ObservationKind
  QuantumWellEffectiveMass : ObservationKind
  ExcitonFineStructure : ObservationKind
  PolarizedAbsorption : ObservationKind
  ExternalQuantumEfficiency : ObservationKind
  LoadedMaximumPower : ObservationKind

record SameSampleMassInferenceAdmission : Set where
  field
    originalPaperDOI : String
    observedKind : ObservationKind
    originalSampleAndGrowthDirection : String
    measuredSpectrumAndTemperature : String
    inferredMassWithUncertainty : String
    fittedWellWidthAndConfinement : String
    materialAndInterfaceComposition : String
    comparableModelHamiltonian : String
    independentlyReplicatedFit : String

-- This record does not synthesize any observed photocurrent or claim a
-- unique gamma3 fit. The cited 0.70m0 is a QW-inferred quantity.
