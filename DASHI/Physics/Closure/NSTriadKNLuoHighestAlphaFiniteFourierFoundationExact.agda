module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaFiniteFourierFoundationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Reuse the repository's machine-checked finite Fourier carrier rather than
-- leaving the foundational hard-projector algebra as an opaque Stage-0 leaf.
-- On every official finite mode list and cutoff this module packages:
--
-- * the selected coefficient-unitary Hermitian Parseval transport;
-- * hard-low and hard-high self-adjointness/idempotence;
-- * low/high disjointness;
-- * hard-high commutation with differentiation and curl.
--
-- This closes the finite projector foundation only.  It does not identify the
-- literal continuum torus integral with the finite coefficient realization.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (nothing)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPeriodicHardProjectorAlgebraExact as Hard
import DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact as Parseval
import DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact as Official

record HighestAlphaFiniteFourierFoundation
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (cutoff : Nat) : Set (lsuc r) where
  field
    hardProjectorOrthogonal :
      Parseval.HardProjectorOrthogonalCertificate model modes cutoff

    lowProjectorIdempotent :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      LP.lowProjector model cutoff
        (LP.lowProjector model cutoff field) mode
      ≡ LP.lowProjector model cutoff field mode

    highProjectorIdempotent :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      Hard.highProjector model cutoff
        (Hard.highProjector model cutoff field) mode
      ≡ Hard.highProjector model cutoff field mode

    lowAfterHighIsZero :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      LP.lowProjector model cutoff
        (Hard.highProjector model cutoff field) mode
      ≡ nothing

    highAfterLowIsZero :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      Hard.highProjector model cutoff
        (LP.lowProjector model cutoff field) mode
      ≡ nothing

    highProjectorCommutesWithDerivative :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      LP.fourierDerivative model
        (Hard.highProjector model cutoff field) mode
      ≡ Hard.highProjector model cutoff
          (LP.fourierDerivative model field) mode

    highProjectorCommutesWithCurl :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      LP.fourierCurl model
        (Hard.highProjector model cutoff field) mode
      ≡ Hard.highProjector model cutoff
          (LP.fourierCurl model field) mode

open HighestAlphaFiniteFourierFoundation public

highestAlphaFiniteFourierFoundation :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (cutoff : Nat) →
  HighestAlphaFiniteFourierFoundation model modes cutoff
highestAlphaFiniteFourierFoundation model modes cutoff = record
  { hardProjectorOrthogonal =
      Official.officialHardProjectorOrthogonal model modes cutoff
  ; lowProjectorIdempotent =
      Hard.lowProjectorIdempotent model cutoff
  ; highProjectorIdempotent =
      Hard.highProjectorIdempotent model cutoff
  ; lowAfterHighIsZero =
      Hard.lowAfterHighIsZero model cutoff
  ; highAfterLowIsZero =
      Hard.highAfterLowIsZero model cutoff
  ; highProjectorCommutesWithDerivative =
      Hard.highProjectorCommutesWithDerivative model cutoff
  ; highProjectorCommutesWithCurl =
      Hard.highProjectorCommutesWithCurl model cutoff
  }

finiteHermitianParsevalFoundationClosed : Bool
finiteHermitianParsevalFoundationClosed = true

hardProjectorOrthogonalityFoundationClosed : Bool
hardProjectorOrthogonalityFoundationClosed = true

hardProjectorDifferentialCommutationFoundationClosed : Bool
hardProjectorDifferentialCommutationFoundationClosed = true

continuumTorusIntegralIdentificationClosed : Bool
continuumTorusIntegralIdentificationClosed = false

finiteHermitianParsevalFoundationClosedIsTrue :
  finiteHermitianParsevalFoundationClosed ≡ true
finiteHermitianParsevalFoundationClosedIsTrue = refl

hardProjectorOrthogonalityFoundationClosedIsTrue :
  hardProjectorOrthogonalityFoundationClosed ≡ true
hardProjectorOrthogonalityFoundationClosedIsTrue = refl

hardProjectorDifferentialCommutationFoundationClosedIsTrue :
  hardProjectorDifferentialCommutationFoundationClosed ≡ true
hardProjectorDifferentialCommutationFoundationClosedIsTrue = refl
