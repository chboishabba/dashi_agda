{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanP1PresentCutSpatialC3CompilerExact where

------------------------------------------------------------------------
-- Q1/P1 -> SPATIAL C3 ON THE EXACT PRESENT-CUT FINITE D1.
--
-- The live CMP119 source frontier no longer treats signed B4 covariance as a
-- primitive physics leaf.  `CMP119CosmologyP1PresentCutPathDerivativeExact`
-- derives it from:
--   * invariant effective potential;
--   * B4-equivariant one-parameter source paths;
--   * ordinary derivative semantics.
--
-- This file restricts that derived theorem to the physically aligned spatial
-- 1->2->3 cycle fixing time, by composing the existing swap23 and swap12
-- generators.  No independent C3 covariance receipt is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutPathDerivativeExact as P1
import DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact as Potential
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact as Spatial

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

module _
    {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {source localization bc1Canonical}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical)
    (laws :
      R143.PresentCutBC2FirstVariationLinearity
        (Present10.asPresentCutPhysicalSourceInputs presentData))
    (data : P1.PresentCutSignedSourcePathDerivative presentData laws)
  where

  Background : Set
  Background = P1.Background presentData laws

  moved23 : Background → Background
  moved23 background =
    Potential.actBackground (P1.potentialGeometry data)
      Hyper.swap23 background

  spatialC3Background : Background → Background
  spatialC3Background background =
    Potential.actBackground (P1.potentialGeometry data)
      Hyper.swap12 (moved23 background)

  componentAfter23 :
    K.SymmetricTensorComponent4 → K.SymmetricTensorComponent4
  componentAfter23 component =
    Signed.component
      (Signed.actSignedComponent
        (Axis.hypercubicSignedAxisAction Hyper.swap23) component)

  spatialC3ComponentViaB4 :
    K.SymmetricTensorComponent4 → K.SymmetricTensorComponent4
  spatialC3ComponentViaB4 component =
    Signed.component
      (Signed.actSignedComponent
        (Axis.hypercubicSignedAxisAction Hyper.swap12)
        (componentAfter23 component))

  spatialC3ComponentViaB4MatchesCanonical :
    ∀ component →
    spatialC3ComponentViaB4 component ≡ Spatial.spatialXYZComponent component
  spatialC3ComponentViaB4MatchesCanonical K.component00 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component01 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component02 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component03 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component11 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component12 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component13 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component22 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component23 = refl
  spatialC3ComponentViaB4MatchesCanonical K.component33 = refl

  swap23UnsignedCovariance :
    ∀ background component →
    P1.finiteD1AtComponent presentData laws
      (moved23 background) (componentAfter23 component)
    ≡
    P1.finiteD1AtComponent presentData laws background component
  swap23UnsignedCovariance background K.component00 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component00
  swap23UnsignedCovariance background K.component01 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component01
  swap23UnsignedCovariance background K.component02 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component02
  swap23UnsignedCovariance background K.component03 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component03
  swap23UnsignedCovariance background K.component11 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component11
  swap23UnsignedCovariance background K.component12 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component12
  swap23UnsignedCovariance background K.component13 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component13
  swap23UnsignedCovariance background K.component22 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component22
  swap23UnsignedCovariance background K.component23 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component23
  swap23UnsignedCovariance background K.component33 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap23 background K.component33

  swap12UnsignedCovariance :
    ∀ background component →
    P1.finiteD1AtComponent presentData laws
      (Potential.actBackground (P1.potentialGeometry data)
        Hyper.swap12 background)
      (Signed.component
        (Signed.actSignedComponent
          (Axis.hypercubicSignedAxisAction Hyper.swap12) component))
    ≡
    P1.finiteD1AtComponent presentData laws background component
  swap12UnsignedCovariance background K.component00 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component00
  swap12UnsignedCovariance background K.component01 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component01
  swap12UnsignedCovariance background K.component02 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component02
  swap12UnsignedCovariance background K.component03 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component03
  swap12UnsignedCovariance background K.component11 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component11
  swap12UnsignedCovariance background K.component12 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component12
  swap12UnsignedCovariance background K.component13 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component13
  swap12UnsignedCovariance background K.component22 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component22
  swap12UnsignedCovariance background K.component23 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component23
  swap12UnsignedCovariance background K.component33 =
    P1.signedFiniteD1Covariant presentData laws data
      Hyper.swap12 background K.component33

  spatialC3FiniteD1CovariantViaB4 :
    ∀ background component →
    P1.finiteD1AtComponent presentData laws
      (spatialC3Background background)
      (spatialC3ComponentViaB4 component)
    ≡
    P1.finiteD1AtComponent presentData laws background component
  spatialC3FiniteD1CovariantViaB4 background component =
    trans
      (swap12UnsignedCovariance
        (moved23 background) (componentAfter23 component))
      (swap23UnsignedCovariance background component)

  q1PathSemanticsCompilesSpatialC3WithoutNewReceipt : Bool
  q1PathSemanticsCompilesSpatialC3WithoutNewReceipt = true

  spatialC3UsesSourceAlignedSwap23ThenSwap12 : Bool
  spatialC3UsesSourceAlignedSwap23ThenSwap12 = true

  independentSpatialC3PhysicalLeafRequired : Bool
  independentSpatialC3PhysicalLeafRequired = false

------------------------------------------------------------------------
-- The remaining source payment is exactly Q1: inhabit the literal present-cut
-- path derivative/equivariance package.  The C3 theorem above is then compiler
-- output.  This file does not identify the separate exact-rational R144 readout
-- carrier with the real-valued path-derivative carrier.
------------------------------------------------------------------------

remainingLeafIsQ1PathSemanticsNotC3Covariance : Bool
remainingLeafIsQ1PathSemanticsNotC3Covariance = true

rationalR144ReadoutIdentificationStillSeparate : Bool
rationalR144ReadoutIdentificationStillSeparate = true
