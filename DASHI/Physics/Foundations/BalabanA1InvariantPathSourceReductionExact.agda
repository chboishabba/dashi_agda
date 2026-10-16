{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanA1InvariantPathSourceReductionExact where

------------------------------------------------------------------------
-- Q1 SOURCE MAX-CUT: INVARIANT POTENTIAL + EQUIVARIANT SIGNED BASIS PATH.
--
-- The live preferred-source frontier has retired primitive signed covariance.
-- The repository's P1 theorem is sharper: signed tensor covariance follows by
-- differentiating an invariant scalar along an equivariant signed basis path.
-- This file records that reduction without manufacturing the remaining physical
-- source-path data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as P1
import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004QExact as Q
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

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
        Axis.hypercubicSignedAxisAction

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
      (Axis.hypercubicSignedAxisAction generator)
      component)
  ≡
  realComponentReadout source configuration component
signedB4ReadoutCovariant source =
  P1.signedReadoutCovariantFromInvariantPotential
    (derivativeLaws source) (geometry source)

------------------------------------------------------------------------
-- 2. Live-Q frontier accounting.
------------------------------------------------------------------------

p1InvariantPathPaysSignedTensorCovariance : Bool
p1InvariantPathPaysSignedTensorCovariance =
  P1.p1SignedCovarianceIsCompilerOutputFromInvariantPathDerivative

primitiveSignedCovarianceRetired : Bool
primitiveSignedCovarianceRetired = Q.primitiveSignedCovarianceRetired

q1IsPathDerivativeSemanticsAndEquivariance : Bool
q1IsPathDerivativeSemanticsAndEquivariance =
  Q.q1IsPathDerivativeSemanticsAndEquivariance

generalFirstVariationNaturalityIsNotMinimalA1Leaf : Bool
generalFirstVariationNaturalityIsNotMinimalA1Leaf = true

-- The exact-rational terminal R144 readout is a separate representation carrier.
-- It is not needed for the real present-cut P1 theorem, and identifying it with
-- the real path derivative remains a same-object payment only for consumers that
-- specifically require the rational readout.
rationalFiniteD1ToRealPathDerivativeIdentificationStillSeparate : Bool
rationalFiniteD1ToRealPathDerivativeIdentificationStillSeparate = true

-- CMP109 Section 5 coordinate/reflection symmetry is valuable source authority,
-- but it is not by itself the selected metric/stress source path nor ordinary
-- derivative semantics.
cmp109VacuumPolarizationScalarSymmetryDoesNotByItselfPayQ1PathSemantics : Bool
cmp109VacuumPolarizationScalarSymmetryDoesNotByItselfPayQ1PathSemantics = true

preferredFrontierAdapterDebtIsZero :
  Q.remainingAdapterDebtInScopedPreferredRoute ≡ zero
preferredFrontierAdapterDebtIsZero = refl

record A1InvariantPathTerminalBoundary : Set where
  constructor a1-invariant-path-terminal-boundary
  field
    signedTensorCovarianceIsCompilerOutput : Bool
    primitiveSignedCovarianceIsRetired : Bool
    pathDerivativeRealisationStillSourceEvidence : Bool
    sourcePathB4EquivarianceStillSourceEvidence : Bool
    rationalFiniteD1IdentificationStillSeparate : Bool
    cmp109ScalarSymmetrySubstitutesForMetricPathSemantics : Bool

canonicalA1InvariantPathTerminalBoundary : A1InvariantPathTerminalBoundary
canonicalA1InvariantPathTerminalBoundary =
  a1-invariant-path-terminal-boundary
    true true true true true false
