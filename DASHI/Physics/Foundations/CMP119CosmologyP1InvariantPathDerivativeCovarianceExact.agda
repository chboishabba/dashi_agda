{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact where

------------------------------------------------------------------------
-- P1 NEW MATH: DIFFERENTIATE AN INVARIANT SCALAR ALONG AN EQUIVARIANT PATH.
--
-- The old R142 interface was too weak: additive linearity in the FUNCTION
-- argument does not imply naturality in the configuration/tangent arguments.
--
-- The correct theorem is the standard directional-derivative argument.
-- If
--
--   F(g x) = F(x)
--
-- and the one-parameter source path transforms as
--
--   path(g x, e_{g c}, t)
--     = g path(x, e_c, s(g,c) t),
--
-- then differentiating at t=0 gives
--
--   D F(g x)[e_{g c}] = s(g,c) D F(x)[e_c].
--
-- Applying the same basis sign once more in the signed readout gives exact
-- tensor covariance.  Thus the reflection sign does NOT need to live in the
-- ten-label R142 tangent carrier; it lives in the reparameterisation t -> -t.
--
-- Physics/source content remaining after this theorem:
--   * the R144 first variation is the ordinary path derivative;
--   * the selected source path is equivariant under the literal B4 action;
--   * the finite scalar potential is B4 invariant (already sourced by CMP119
--     whole-lattice Euclidean covariance once the exact potential is attached).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout

------------------------------------------------------------------------
-- Ordinary one-variable derivative laws needed by the argument.
--
-- We deliberately keep these independent of R142.  A concrete real derivative
-- calculus may instantiate them from limits/difference quotients.  The only
-- nontrivial chain rule required here is reparameterisation by t or -t.
------------------------------------------------------------------------

record SignedPathDerivativeLaws : Set₁ where
  field
    derivativeAtZero : (ℝ → ℝ) → ℝ

    derivativeCong :
      ∀ f g →
      (∀ t → f t ≡ g t) →
      derivativeAtZero f ≡ derivativeAtZero g

    derivativeUnderBasisSign :
      ∀ sign f →
      derivativeAtZero
        (λ t → f (Readout.applyBasisSign sign t))
      ≡
      Readout.applyBasisSign sign (derivativeAtZero f)

    basisSignInvolutive :
      ∀ sign value →
      Readout.applyBasisSign sign
        (Readout.applyBasisSign sign value)
      ≡ value

open SignedPathDerivativeLaws public

------------------------------------------------------------------------
-- Source geometry.
------------------------------------------------------------------------

record InvariantSignedBasisPath
    (Configuration Action : Set)
    (axisAction : Action → Signed.SignedAxisAction)
    : Set₁ where
  field
    actConfiguration : Action → Configuration → Configuration

    potential : Configuration → ℝ

    potentialInvariant :
      ∀ action configuration →
      potential (actConfiguration action configuration)
      ≡ potential configuration

    sourcePath :
      Configuration → K.SymmetricTensorComponent4 → ℝ → Configuration

    -- A signed tensor basis action is represented on the source path by
    -- reparameterising the ORIGINAL unsigned basis path by ±t.
    sourcePathCovariant :
      ∀ action configuration component t →
      let transformed =
            Signed.actSignedComponent (axisAction action) component
      in
      sourcePath
        (actConfiguration action configuration)
        (Signed.component transformed)
        t
      ≡
      actConfiguration action
        (sourcePath configuration component
          (Readout.applyBasisSign (Signed.sign transformed) t))

open InvariantSignedBasisPath public

componentDerivative :
  ∀ {Configuration Action axisAction} →
  SignedPathDerivativeLaws →
  InvariantSignedBasisPath Configuration Action axisAction →
  Configuration → K.SymmetricTensorComponent4 → ℝ
componentDerivative derivative geometry configuration component =
  derivativeAtZero derivative
    (λ t → potential geometry (sourcePath geometry configuration component t))

unsignedDerivativeTransformsWithBasisSign :
  ∀ {Configuration Action axisAction}
    (derivative : SignedPathDerivativeLaws)
    (geometry : InvariantSignedBasisPath Configuration Action axisAction)
    action configuration component →
  let transformed =
        Signed.actSignedComponent (axisAction action) component
  in
  componentDerivative derivative geometry
    (actConfiguration geometry action configuration)
    (Signed.component transformed)
  ≡
  Readout.applyBasisSign (Signed.sign transformed)
    (componentDerivative derivative geometry configuration component)
unsignedDerivativeTransformsWithBasisSign
    {axisAction = axisAction}
    derivative geometry action configuration component =
  let
    transformed =
      Signed.actSignedComponent (axisAction action) component

    sign = Signed.sign transformed

    originalPathValue : ℝ → ℝ
    originalPathValue =
      λ t → potential geometry (sourcePath geometry configuration component t)

    transformedPathIsSignedOriginal :
      ∀ t →
      potential geometry
        (sourcePath geometry
          (actConfiguration geometry action configuration)
          (Signed.component transformed)
          t)
      ≡
      originalPathValue (Readout.applyBasisSign sign t)
    transformedPathIsSignedOriginal t =
      trans
        (cong (potential geometry)
          (sourcePathCovariant geometry action configuration component t))
        (potentialInvariant geometry action
          (sourcePath geometry configuration component
            (Readout.applyBasisSign sign t)))
  in
  trans
    (derivativeCong derivative
      (λ t → potential geometry
        (sourcePath geometry
          (actConfiguration geometry action configuration)
          (Signed.component transformed)
          t))
      (λ t → originalPathValue (Readout.applyBasisSign sign t))
      transformedPathIsSignedOriginal)
    (derivativeUnderBasisSign derivative sign originalPathValue)

signedReadoutCovariantFromInvariantPotential :
  ∀ {Configuration Action axisAction}
    (derivative : SignedPathDerivativeLaws)
    (geometry : InvariantSignedBasisPath Configuration Action axisAction)
    action configuration component →
  Readout.signedComponentReadout
    (componentDerivative derivative geometry
      (actConfiguration geometry action configuration))
    (Signed.actSignedComponent (axisAction action) component)
  ≡
  componentDerivative derivative geometry configuration component
signedReadoutCovariantFromInvariantPotential
    {axisAction = axisAction}
    derivative geometry action configuration component =
  let
    transformed =
      Signed.actSignedComponent (axisAction action) component
    sign = Signed.sign transformed
  in
  trans
    (cong (Readout.applyBasisSign sign)
      (unsignedDerivativeTransformsWithBasisSign
        derivative geometry action configuration component))
    (basisSignInvolutive derivative sign
      (componentDerivative derivative geometry configuration component))

p1SignedCovarianceIsCompilerOutputFromInvariantPathDerivative : Bool
p1SignedCovarianceIsCompilerOutputFromInvariantPathDerivative = true

p1ReflectionSignMayLiveInPathReparameterization : Bool
p1ReflectionSignMayLiveInPathReparameterization = true

p1DoesNotFollowFromR142FunctionLinearityAlone : Bool
p1DoesNotFollowFromR142FunctionLinearityAlone = true
