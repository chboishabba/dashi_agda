{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1SignedMarkedStressFamilyExact where

------------------------------------------------------------------------
-- FULL-REFLECTION MARKED E1 WITHOUT A FAKE NEGATIVE TANGENT LABEL.
--
-- On the preferred R245/R122 path the metric tangent carrier is the TEN BASIS
-- LABELS `SymmetricTensorComponent4`; it is not a linear vector carrier.  A
-- coordinate reflection sends (for example) h01 to -h01, so an interface
-- `actTangent : Tangent -> Tangent` cannot faithfully encode the tensor action.
--
-- The correct least-privilege representation is a SIGNED STRESS MARK.  The
-- unsigned R144 component readout is extended linearly in the external sign,
-- and Euclidean covariance is stated directly for that signed family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE1DifferentiatedCovarianceExact as MarkedE1
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout

record SignedMarkedStressFamily
    (Action Base : Set)
    (axisAction : Action → Signed.SignedAxisAction)
    : Set₁ where
  field
    actBase : Action → Base → Base

    baseExpectation : Base → ℝ
    baseCovariant : ∀ action base →
      baseExpectation (actBase action base) ≡ baseExpectation base

    -- R144/R119 component family at a selected background.
    unsignedMarkedReadout :
      Base → K.SymmetricTensorComponent4 → ℝ

    -- This is the genuine tensor covariance theorem.  The reflection sign is
    -- carried by `SignedSymmetricComponent`, not by pretending the basis-label
    -- carrier contains additive inverses.
    signedMarkedReadoutCovariant :
      ∀ action base component →
      Readout.signedComponentReadout
        (unsignedMarkedReadout (actBase action base))
        (Signed.actSignedComponent (axisAction action) component)
      ≡ unsignedMarkedReadout base component

open SignedMarkedStressFamily public

signedMarkedDerivative :
  ∀ {Action Base axisAction} →
  SignedMarkedStressFamily Action Base axisAction →
  Base → Signed.SignedSymmetricComponent → ℝ
signedMarkedDerivative family base signed =
  Readout.signedComponentReadout
    (unsignedMarkedReadout family base)
    signed

actSignedMark :
  ∀ {Action Base axisAction} →
  SignedMarkedStressFamily Action Base axisAction →
  Action → Signed.SignedSymmetricComponent → Signed.SignedSymmetricComponent
actSignedMark {axisAction = axisAction} family action signed =
  let
    originalSign = Signed.sign signed
    transformed = Signed.actSignedComponent
      (axisAction action) (Signed.component signed)
  in
  Signed.signed-component
    (Signed.multiplySign originalSign (Signed.sign transformed))
    (Signed.component transformed)

-- Preferred selected marks enter with positive coefficient.
positiveBasisMark :
  K.SymmetricTensorComponent4 → Signed.SignedSymmetricComponent
positiveBasisMark component = Signed.signed-component Signed.plus component

selectedPositiveBasisCovariant :
  ∀ {Action Base axisAction}
    (family : SignedMarkedStressFamily Action Base axisAction)
    action base component →
  signedMarkedDerivative family
    (actBase family action base)
    (Signed.actSignedComponent (axisAction action) component)
  ≡ unsignedMarkedReadout family base component
selectedPositiveBasisCovariant family =
  signedMarkedReadoutCovariant family

fullReflectionE1NoLongerRequiresSignedValueInsideSourceTangent : Bool
fullReflectionE1NoLongerRequiresSignedValueInsideSourceTangent = true

fullReflectionE1LivesOnSignedMarkedStressFamily : Bool
fullReflectionE1LivesOnSignedMarkedStressFamily = true

oldUnsignedActTangentInterfaceSufficientForFullB4Reflections : Bool
oldUnsignedActTangentInterfaceSufficientForFullB4Reflections = false
