module DASHI.Physics.Gravity.RelativityOpticalKernelBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Optics.PhysicalConstantsKernelClosure as Constants

------------------------------------------------------------------------
-- Relativity contact surface for propagation, lensing, horizons, and
-- tidal deformation.  Standard GR laws are recorded as authority-backed
-- target equations.  No claim is made that involution/kernel/MDL alone
-- derives Einstein dynamics, black-hole existence, or measured G.

data GeometryKernel : Set where
  inertialFrameKernel : GeometryKernel
  lorentzianMetricKernel : GeometryKernel
  connectionKernel : GeometryKernel
  curvatureKernel : GeometryKernel
  nullGeodesicKernel : GeometryKernel
  geodesicDeviationKernel : GeometryKernel

data GRBoundary : Set where
  kinematicIdentity : GRBoundary
  einsteinDynamicsRequired : GRBoundary
  solutionFamilyRequired : GRBoundary
  weakFieldApproximation : GRBoundary
  empiricalCalibrationRequired : GRBoundary

record RelativityLawBridge : Set where
  field
    phenomenon : String
    sourceKernel : GeometryKernel
    targetKernel : GeometryKernel
    standardLaw : String
    observableMap : String
    constantsUsed : List String
    assumptions : List String
    boundary : GRBoundary
    failureMeaning : String

open RelativityLawBridge public

lorentzIntervalBridge : RelativityLawBridge
lorentzIntervalBridge = record
  { phenomenon = "special-relativistic interval invariance"
  ; sourceKernel = inertialFrameKernel
  ; targetKernel = lorentzianMetricKernel
  ; standardLaw = "ds^2 = -c^2 dt^2 + dx^2 + dy^2 + dz^2"
  ; observableMap = "invariant light cone -> Lorentz transformations -> time dilation and length contraction"
  ; constantsUsed = "c" ∷ []
  ; assumptions =
      "inertial-frame equivalence"
      ∷ "observer-independent vacuum light speed"
      ∷ []
  ; boundary = kinematicIdentity
  ; failureMeaning = "the selected frame transport is not Lorentz compatible"
  }

einsteinFieldBridge : RelativityLawBridge
einsteinFieldBridge = record
  { phenomenon = "stress-energy coupled spacetime geometry"
  ; sourceKernel = curvatureKernel
  ; targetKernel = connectionKernel
  ; standardLaw =
      "G_mn + Lambda g_mn = (8 pi G / c^4) T_mn"
  ; observableMap = "stress-energy and boundary data -> metric solution -> causal and tidal observables"
  ; constantsUsed = "G" ∷ "c" ∷ "Lambda when admitted" ∷ []
  ; assumptions =
      "diffeomorphism-invariant metric theory"
      ∷ "Einstein-Hilbert leading action"
      ∷ "declared matter stress-energy tensor"
      ∷ []
  ; boundary = einsteinDynamicsRequired
  ; failureMeaning = "kernel compatibility alone has not supplied Einstein dynamics"
  }

schwarzschildRadiusBridge : RelativityLawBridge
schwarzschildRadiusBridge = record
  { phenomenon = "Schwarzschild horizon radius"
  ; sourceKernel = curvatureKernel
  ; targetKernel = nullGeodesicKernel
  ; standardLaw = "r_s = 2 G M / c^2"
  ; observableMap = "mass M -> horizon scale and null-geodesic structure"
  ; constantsUsed = "G" ∷ "c" ∷ []
  ; assumptions =
      "vacuum exterior"
      ∷ "spherical symmetry"
      ∷ "zero angular momentum and charge"
      ∷ "asymptotic flatness"
      ∷ []
  ; boundary = solutionFamilyRequired
  ; failureMeaning = "the Schwarzschild assumptions or numerical calibration do not hold"
  }

weakLensingBridge : RelativityLawBridge
weakLensingBridge = record
  { phenomenon = "weak gravitational deflection"
  ; sourceKernel = nullGeodesicKernel
  ; targetKernel = nullGeodesicKernel
  ; standardLaw = "Delta phi approximately 4 G M / (b c^2)"
  ; observableMap = "mass M and impact parameter b -> leading deflection angle"
  ; constantsUsed = "G" ∷ "c" ∷ []
  ; assumptions =
      "b much greater than Schwarzschild radius"
      ∷ "static weak field"
      ∷ "asymptotically flat source geometry"
      ∷ []
  ; boundary = weakFieldApproximation
  ; failureMeaning = "strong-field, spin, charge, plasma, or extended-lens terms are non-negligible"
  }

tidalStretchBridge : RelativityLawBridge
tidalStretchBridge = record
  { phenomenon = "radial tidal stretching / spaghettification scale"
  ; sourceKernel = curvatureKernel
  ; targetKernel = geodesicDeviationKernel
  ; standardLaw =
      "D^2 xi^mu / D tau^2 = - R^mu_nu rho sigma u^nu xi^rho u^sigma; Newtonian radial estimate Delta a approximately 2 G M ell / r^3"
  ; observableMap = "curvature, worldline, and body separation ell -> relative acceleration"
  ; constantsUsed = "G" ∷ "c in the relativistic metric solution" ∷ []
  ; assumptions =
      "nearby freely falling worldlines"
      ∷ "body size small relative to curvature scale"
      ∷ "Newtonian estimate used only outside its strong-field failure region"
      ∷ []
  ; boundary = solutionFamilyRequired
  ; failureMeaning = "the curvature tensor or body-model approximation is missing"
  }

record RelativityOpticalKernelClosure : Set where
  field
    constantClosure : Constants.PhysicalConstantsKernelClosure
    bridges : List RelativityLawBridge
    predictsLorentzKinematicsGivenLightCone : Bool
    predictsLorentzKinematicsGivenLightConeIsTrue :
      predictsLorentzKinematicsGivenLightCone ≡ true
    derivesEinsteinEquationFromKernelAlone : Bool
    derivesEinsteinEquationFromKernelAloneIsFalse :
      derivesEinsteinEquationFromKernelAlone ≡ false
    supportsGRSolutionAudit : Bool
    supportsGRSolutionAuditIsTrue : supportsGRSolutionAudit ≡ true
    blackHolePhysicsPromoted : Bool
    blackHolePhysicsPromotedIsFalse : blackHolePhysicsPromoted ≡ false

open RelativityOpticalKernelClosure public

canonicalRelativityOpticalKernelClosure : RelativityOpticalKernelClosure
canonicalRelativityOpticalKernelClosure = record
  { constantClosure = Constants.canonicalPhysicalConstantsKernelClosure
  ; bridges =
      lorentzIntervalBridge
      ∷ einsteinFieldBridge
      ∷ schwarzschildRadiusBridge
      ∷ weakLensingBridge
      ∷ tidalStretchBridge
      ∷ []
  ; predictsLorentzKinematicsGivenLightCone = true
  ; predictsLorentzKinematicsGivenLightConeIsTrue = refl
  ; derivesEinsteinEquationFromKernelAlone = false
  ; derivesEinsteinEquationFromKernelAloneIsFalse = refl
  ; supportsGRSolutionAudit = true
  ; supportsGRSolutionAuditIsTrue = refl
  ; blackHolePhysicsPromoted = false
  ; blackHolePhysicsPromotedIsFalse = refl
  }
