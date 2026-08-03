module DASHI.Physics.Closure.NSTriadKNPeriodicHardProjectorAlgebraExact where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Complete the Boolean support algebra for the repository's exact periodic
-- hard low/high projectors.  The high projector is the complement of the
-- existing low selector.  Both projectors are pointwise idempotent, disjoint,
-- and commute with Fourier differentiation and curl.  These support-level
-- facts are prerequisites for the physical energy identity; Hermitian L2
-- self-adjointness and hard/smooth multiplier comparison remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (nothing)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP

not : Bool → Bool
not true = false
not false = true

highProjector :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → LP.FourierField model → LP.FourierField model
highProjector model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = nothing
... | false = field mode

lowProjectorIdempotent :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  LP.lowProjector model cutoff
    (LP.lowProjector model cutoff field) mode
    ≡ LP.lowProjector model cutoff field mode
lowProjectorIdempotent model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

highProjectorIdempotent :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  highProjector model cutoff
    (highProjector model cutoff field) mode
    ≡ highProjector model cutoff field mode
highProjectorIdempotent model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

lowAfterHighIsZero :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  LP.lowProjector model cutoff
    (highProjector model cutoff field) mode
    ≡ nothing
lowAfterHighIsZero model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

highAfterLowIsZero :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  highProjector model cutoff
    (LP.lowProjector model cutoff field) mode
    ≡ nothing
highAfterLowIsZero model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

highProjectorCommutesWithDerivative :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  LP.fourierDerivative model
    (highProjector model cutoff field) mode
    ≡ highProjector model cutoff
      (LP.fourierDerivative model field) mode
highProjectorCommutesWithDerivative model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

highProjectorCommutesWithCurl :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  LP.fourierCurl model
    (highProjector model cutoff field) mode
    ≡ highProjector model cutoff
      (LP.fourierCurl model field) mode
highProjectorCommutesWithCurl model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

hardLowProjectorIdempotenceConstructed : Bool
hardLowProjectorIdempotenceConstructed = true

hardHighProjectorIdempotenceConstructed : Bool
hardHighProjectorIdempotenceConstructed = true

hardLowHighDisjointnessConstructed : Bool
hardLowHighDisjointnessConstructed = true

hardHighDerivativeCurlCommutationConstructed : Bool
hardHighDerivativeCurlCommutationConstructed = true

hardProjectorHermitianL2SelfAdjointnessClosed : Bool
hardProjectorHermitianL2SelfAdjointnessClosed = false

hardLowProjectorIdempotenceConstructedIsTrue :
  hardLowProjectorIdempotenceConstructed ≡ true
hardLowProjectorIdempotenceConstructedIsTrue = refl

hardHighProjectorIdempotenceConstructedIsTrue :
  hardHighProjectorIdempotenceConstructed ≡ true
hardHighProjectorIdempotenceConstructedIsTrue = refl

hardLowHighDisjointnessConstructedIsTrue :
  hardLowHighDisjointnessConstructed ≡ true
hardLowHighDisjointnessConstructedIsTrue = refl

hardHighDerivativeCurlCommutationConstructedIsTrue :
  hardHighDerivativeCurlCommutationConstructed ≡ true
hardHighDerivativeCurlCommutationConstructedIsTrue = refl

hardProjectorHermitianL2SelfAdjointnessClosedIsFalse :
  hardProjectorHermitianL2SelfAdjointnessClosed ≡ false
hardProjectorHermitianL2SelfAdjointnessClosedIsFalse = refl
