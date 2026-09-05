module DASHI.Physics.Plasma.ReducedFluidKineticHermiteNumericsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC REDUCED FLUID-KINETIC / FOURIER-HERMITE NUMERICS
------------------------------------------------------------------------

data ReducedModel : Set where
  reducedMHD
  kineticReducedMHD
  kineticReducedElectronHeating
  twoFieldGyrofluidLimit
  : ReducedModel

data NumericalAxis : Set where
  parallelCoordinate
  perpendicularPlane
  velocityMomentAxis
  timeSplitting
  : NumericalAxis

record StrongGuideFieldOrdering : Set where
  constructor strong-guide-field-ordering
  field
    guideField : String
    anisotropy : String
    fluctuationOrdering : String
    applicability : String

open StrongGuideFieldOrdering public

canonicalStrongGuideFieldOrdering : StrongGuideFieldOrdering
canonicalStrongGuideFieldOrdering = strong-guide-field-ordering
  "strong ambient magnetic field defines parallel/perpendicular directions"
  "fluctuations are anisotropic with comparatively long parallel scales"
  "reduced equations retain selected low-frequency electromagnetic/fluid-kinetic dynamics"
  "turbulence/reconnection regimes satisfying the asymptotic ordering; not arbitrary magnetised plasmas"

record FourierHermiteDiscretisation : Set where
  constructor fourier-hermite-discretisation
  field
    perpendicularRepresentation : String
    parallelRepresentation : String
    velocityRepresentation : String
    operatorSplitting : String
    closureIssue : String
    deAliasingOrDissipation : String

open FourierHermiteDiscretisation public

canonicalFourierHermiteDiscretisation : FourierHermiteDiscretisation
canonicalFourierHermiteDiscretisation = fourier-hermite-discretisation
  "Fourier/pseudo-spectral representation is natural in periodic perpendicular directions"
  "parallel propagation may use finite-difference/upwind/high-order schemes or spectral treatment depending on implementation"
  "Hermite polynomials expand the parallel-velocity dependence into a hierarchy of moments"
  "Strang/Godunov-style splitting can separate parallel and perpendicular operators"
  "finite Hermite truncation needs a closure or sufficiently resolved dissipation to control unresolved phase mixing"
  "spectral nonlinearity requires alias control; kinetic hierarchy may require hypercollisional or physical dissipation"

record VerificationHierarchy : Set where
  constructor verification-hierarchy
  field
    analyticLinearModes : String
    conservationOrEnergy : String
    convergence : String
    nonlinearBenchmarks : String
    modelToModelLimits : String

open VerificationHierarchy public

canonicalVerificationHierarchy : VerificationHierarchy
canonicalVerificationHierarchy = verification-hierarchy
  "recover dispersion/growth/damping where the reduced equations admit analytic or high-accuracy reference solutions"
  "check discrete energy/invariant evolution against the continuous closed model"
  "refine spatial, temporal and Hermite resolution and check stable convergence"
  "compare nonlinear reconnection/turbulence test problems across resolutions/codes"
  "recover RMHD/gyrofluid or other asymptotic limits when parameters enter the corresponding regime"

record ReducedNumericsBoundary : Set where
  constructor reduced-numerics-boundary
  field
    convergedDiscreteSolutionMeansFullKineticTruth : Bool
    convergedDiscreteSolutionMeansFullKineticTruthIsFalse : convergedDiscreteSolutionMeansFullKineticTruth ≡ false
    correctRMHDLimitMeansKineticClosureCorrect : Bool
    correctRMHDLimitMeansKineticClosureCorrectIsFalse : correctRMHDLimitMeansKineticClosureCorrect ≡ false
    moreHermiteMomentsAlwaysMeansPhysicalAccuracy : Bool
    moreHermiteMomentsAlwaysMeansPhysicalAccuracyIsFalse : moreHermiteMomentsAlwaysMeansPhysicalAccuracy ≡ false
    benchmarkAgreementMeansUniqueNumericalMethod : Bool
    benchmarkAgreementMeansUniqueNumericalMethodIsFalse : benchmarkAgreementMeansUniqueNumericalMethod ≡ false

canonicalReducedNumericsBoundary : ReducedNumericsBoundary
canonicalReducedNumericsBoundary = reduced-numerics-boundary
  false refl
  false refl
  false refl
  false refl

data ReducedNumericsReverseTarget : Set where
  needOrderingReceipt
  needClosureJustification
  needHermiteConvergence
  needSpatialTemporalConvergence
  needInvariantBudget
  needCrossCodeBenchmark
  : ReducedNumericsReverseTarget
