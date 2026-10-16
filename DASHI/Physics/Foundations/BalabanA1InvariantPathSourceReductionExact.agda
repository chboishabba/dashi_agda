{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanA1InvariantPathSourceReductionExact where

------------------------------------------------------------------------
-- A1 SOURCE MAX-CUT: INVARIANT POTENTIAL + EQUIVARIANT SIGNED BASIS PATH.
--
-- The preferred source frontier names one broad CMP109/116 first-variation
-- naturality package as A1.  The repository's P1 theorem is more precise:
-- signed tensor covariance follows by differentiating an invariant scalar along
-- an equivariant signed basis path.  This file records that reduction without
-- manufacturing the remaining physical source data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as P1
import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004MExact as Preferred
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as CMP109

------------------------------------------------------------------------
-- 1. Exact source package on the continuous/physical scalar carrier.
------------------------------------------------------------------------

record A1InvariantPathSourcePackage (Configuration : Set) : Set₁ where
  field
    derivativeLaws : P1.SignedPathDerivativeLaws
    geometry :
      P1.InvariantSignedBasisPath
        Configuration
        Hyper.HypercubicGenerator
        (λ generator →
          DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact.hypercubicSignedAxisAction generator)

open A1InvariantPathSourcePackage public

realComponentReadout :
  ∀ {Configuration} →
  A1InvariantPathSourcePackage Configuration →
  Configuration → K.SymmetricTensorComponent4 → ℝ
realComponentReadout source =
  P1.componentDerivative (derivativeLaws source) (geometry source)

signedB4ReadoutCovariant :
  ∀ {Configuration}
    (source : A1InvariantPathSourcePackage Configuration)
    generator configuration component →
  Readout.signedComponentReadout
    (realComponentReadout source
      (P1.actConfiguration (geometry source) generator configuration))
    (Signed.actSignedComponent
      (DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact.hypercubicSignedAxisAction generator)
      component)
  ≡
  realComponentReadout source configuration component
signedB4ReadoutCovariant source =
  P1.signedReadoutCovariantFromInvariantPotential
    (derivativeLaws source) (geometry source)

------------------------------------------------------------------------
-- 2. Frontier accounting.
------------------------------------------------------------------------

p1InvariantPathPaysSignedTensorCovariance : Bool
p1InvariantPathPaysSignedTensorCovariance =
  P1.p1SignedCovarianceIsCompilerOutputFromInvariantPathDerivative

generalFirstVariationNaturalityIsNotMinimalA1Leaf : Bool
generalFirstVariationNaturalityIsNotMinimalA1Leaf = true

-- The terminal R144 A1 owner intentionally keeps an exact rational finite-D1
-- readout.  P1 is a theorem over the repository real carrier.  Identifying the
-- selected rational finite-D1 readout with this continuous path derivative is a
-- same-object representation payment and is not inferred from shared notation.
rationalFiniteD1ToRealPathDerivativeIdentificationStillSeparate : Bool
rationalFiniteD1ToRealPathDerivativeIdentificationStillSeparate = true

-- CMP109 Section 5 supplies coordinate/reflection covariance for the literal
-- vacuum-polarization tensor/scalar projection.  That is valuable source
-- symmetry, but it is not by itself a theorem that the selected metric/stress
-- source path is equivariant or that R144's first variation is this path
-- derivative.  Keep those source roles distinct.
cmp109VacuumPolarizationScalarSymmetryDoesNotByItselfPayA1PathNaturality : Bool
cmp109VacuumPolarizationScalarSymmetryDoesNotByItselfPayA1PathNaturality = true

preferredFrontierAlreadyCompilerSaturated : Bool
preferredFrontierAlreadyCompilerSaturated = Preferred.preferredRouteCompilerSaturated

cmp109HypercubicSourceSymmetryCompilerAlreadyMachineChecked : Bool
cmp109HypercubicSourceSymmetryCompilerAlreadyMachineChecked = true

record A1InvariantPathTerminalBoundary : Set where
  constructor a1-invariant-path-terminal-boundary
  field
    signedTensorCovarianceIsCompilerOutput : Bool
    pathDerivativeRealisationStillSourceEvidence : Bool
    sourcePathB4EquivarianceStillSourceEvidence : Bool
    selectedPotentialSameObjectB4InvarianceStillSourceEvidence : Bool
    rationalFiniteD1IdentificationStillSeparate : Bool
    cmp109ScalarSymmetrySubstitutesForMetricPathNaturality : Bool

canonicalA1InvariantPathTerminalBoundary : A1InvariantPathTerminalBoundary
canonicalA1InvariantPathTerminalBoundary =
  a1-invariant-path-terminal-boundary
    true true true true true false
