{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1CompactGaugeExponentialPathExact where

------------------------------------------------------------------------
-- R1 NEW MATH: B4 COVARIANCE OF THE SOURCE PATH FROM COMPACT-GAUGE ALGEBRA.
--
-- For a background B and selected tensor/source direction X_c, use the ordinary
-- compact-gauge one-parameter perturbation
--
--       path(B,c,t) = perturb B (exp_c(t)).
--
-- A Euclidean lattice symmetry acts on both backgrounds and increments.  If
-- perturbation is equivariant and the exponential increment obeys the signed
-- tensor action, then the full source-path covariance needed by the P1
-- derivative theorem is automatic.  In particular, a reflected mixed component
-- is represented by exp_c(-t), not by requiring a negative element in the
-- ten-label tangent carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as Path
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout

record CompactGaugeExponentialSourcePath
    (Background Increment Action : Set)
    (actBackground : Action → Background → Background)
    (axisAction : Action → Signed.SignedAxisAction)
    : Set₁ where
  field
    actIncrement : Action → Increment → Increment

    perturbBackground : Background → Increment → Background

    exponentialIncrement :
      K.SymmetricTensorComponent4 → ℝ → Increment

    -- Naturality of the finite background perturbation under the Euclidean
    -- lattice action.
    perturbBackgroundEquivariant :
      ∀ action background increment →
      perturbBackground
        (actBackground action background)
        (actIncrement action increment)
      ≡
      actBackground action
        (perturbBackground background increment)

    -- The one-parameter subgroup carries the signed rank-two action.  The sign
    -- appears on the scalar path parameter, so no fake signed tangent label is
    -- needed.
    exponentialIncrementSignedCovariant :
      ∀ action component t →
      let transformed =
            Signed.actSignedComponent (axisAction action) component
      in
      exponentialIncrement (Signed.component transformed) t
      ≡
      actIncrement action
        (exponentialIncrement component
          (Readout.applyBasisSign (Signed.sign transformed) t))

open CompactGaugeExponentialSourcePath public

sourcePath :
  ∀ {Background Increment Action actBackground axisAction} →
  CompactGaugeExponentialSourcePath
    Background Increment Action actBackground axisAction →
  Background → K.SymmetricTensorComponent4 → ℝ → Background
sourcePath geometry background component t =
  perturbBackground geometry background
    (exponentialIncrement geometry component t)

sourcePathCovariant :
  ∀ {Background Increment Action actBackground axisAction}
    (geometry :
      CompactGaugeExponentialSourcePath
        Background Increment Action actBackground axisAction) →
  ∀ action background component t →
  let transformed =
        Signed.actSignedComponent (axisAction action) component
  in
  sourcePath geometry
    (actBackground action background)
    (Signed.component transformed)
    t
  ≡
  actBackground action
    (sourcePath geometry background component
      (Readout.applyBasisSign (Signed.sign transformed) t))
sourcePathCovariant {axisAction = axisAction} geometry action background component t =
  let
    transformed =
      Signed.actSignedComponent (axisAction action) component
    signedParameter =
      Readout.applyBasisSign (Signed.sign transformed) t
    originalIncrement =
      exponentialIncrement geometry component signedParameter
  in
  trans
    (cong
      (perturbBackground geometry
        (actBackground action background))
      (exponentialIncrementSignedCovariant
        geometry action component t))
    (perturbBackgroundEquivariant
      geometry action background originalIncrement)

asInvariantSignedBasisPath :
  ∀ {Background Increment Action actBackground axisAction}
    (potential : Background → ℝ)
    (potentialInvariant :
      ∀ action background →
      potential (actBackground action background) ≡ potential background)
    (geometry :
      CompactGaugeExponentialSourcePath
        Background Increment Action actBackground axisAction) →
  Path.InvariantSignedBasisPath Background Action axisAction
asInvariantSignedBasisPath
    {actBackground = actBackground} {axisAction = axisAction}
    potential potentialInvariant geometry = record
  { Path.InvariantSignedBasisPath.actConfiguration = actBackground
  ; Path.InvariantSignedBasisPath.potential = potential
  ; Path.InvariantSignedBasisPath.potentialInvariant = potentialInvariant
  ; Path.InvariantSignedBasisPath.sourcePath = sourcePath geometry
  ; Path.InvariantSignedBasisPath.sourcePathCovariant =
      sourcePathCovariant geometry
  }

sourcePathCovarianceIsGroupActionAlgebra : Bool
sourcePathCovarianceIsGroupActionAlgebra = true

reflectionSignLivesInExponentialParameter : Bool
reflectionSignLivesInExponentialParameter = true

primitiveSourcePathCovarianceNoLongerRequired : Bool
primitiveSourcePathCovarianceNoLongerRequired = true
