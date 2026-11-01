{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedReadoutExact where

------------------------------------------------------------------------
-- SIGNED TEN-SLOT E1 COVARIANCE ON THE ACTUAL B_4 GENERATOR CARRIER.
--
-- The signed axis action is no longer an input.  It is the concrete action
-- induced by `BalabanClayT4HypercubicGeneratedActionExact.HypercubicGenerator`.
-- The only remaining theorem is covariance of the selected ten-slot readout
-- under that fixed action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; -ℝ_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

HypercubicSignedReadoutCovariance :
  (K.SymmetricTensorComponent4 → ℝ) → Set₁
HypercubicSignedReadoutCovariance readout =
  Readout.SignedTenSlotReadoutCovariance
    Hyper.HypercubicGenerator
    Axis.hypercubicSignedAxisAction
    readout

------------------------------------------------------------------------
-- The concrete covariance equations exposed in the forms downstream users
-- actually need.  These are all compiler output from one generator-covariance
-- record; no per-component symmetry assumptions are added.
------------------------------------------------------------------------

flip0Makes01Odd :
  ∀ {readout}
    (covariance : HypercubicSignedReadoutCovariance readout) →
  -ℝ (readout K.component01) ≡ readout K.component01
flip0Makes01Odd covariance =
  Readout.componentCovariant covariance Hyper.flip0 K.component01

flip0Keeps00 :
  ∀ {readout}
    (covariance : HypercubicSignedReadoutCovariance readout) →
  readout K.component00 ≡ readout K.component00
flip0Keeps00 covariance =
  Readout.componentCovariant covariance Hyper.flip0 K.component00

swap01Relates02And12 :
  ∀ {readout}
    (covariance : HypercubicSignedReadoutCovariance readout) →
  readout K.component12 ≡ readout K.component02
swap01Relates02And12 covariance =
  Readout.componentCovariant covariance Hyper.swap01 K.component02

swap12Relates01And02 :
  ∀ {readout}
    (covariance : HypercubicSignedReadoutCovariance readout) →
  readout K.component02 ≡ readout K.component01
swap12Relates01And02 covariance =
  Readout.componentCovariant covariance Hyper.swap12 K.component01

swap23Relates12And13 :
  ∀ {readout}
    (covariance : HypercubicSignedReadoutCovariance readout) →
  readout K.component13 ≡ readout K.component12
swap23Relates12And13 covariance =
  Readout.componentCovariant covariance Hyper.swap23 K.component12

hypercubicAxisActionChoiceStillFree : Bool
hypercubicAxisActionChoiceStillFree = false

remainingE1TensorLeafIsOneReadoutCovarianceTheoremOnActualB4Generators : Bool
remainingE1TensorLeafIsOneReadoutCovarianceTheoremOnActualB4Generators = true
