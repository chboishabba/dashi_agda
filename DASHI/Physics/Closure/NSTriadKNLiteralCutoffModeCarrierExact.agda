module DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S1b / LITERAL MODE-LIST CARRIER WITHOUT VISCOSITY
--
-- R405 correctly identifies the same-object support fact needed by several
-- downstream constructions:
--
--   Audit.modes(systemAt N t) = nonzeroCutoffModes N.
--
-- But its `LiteralNonzeroCutoffTrajectory` record also carries positive
-- viscosity because R405 was written for the R403 retained-flux route.  S1b
-- only needs a time-independent finite mode list so R412 can differentiate one
-- fixed finite sum.  Importing the stronger R405 record here would therefore
-- consume S4 prematurely.
--
-- This owner extracts exactly the support coordinate and nothing else.  The
-- same equality still gives retained-mode nonzero proofs through R404, while
-- positive viscosity remains absent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404

F : C3.RealField _
F = Rational.rationalRealField

module LiteralModeCarrier
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  record LiteralCutoffModeCarrier
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set where
    field
      retainedModesExact :
        (N : Nat) (time : Time) →
        Audit.modes (Dyn.Base.systemAt (Dyn.forgetDynamics T) N time)
        ≡ Canonical.nonzeroCutoffModes N

  open LiteralCutoffModeCarrier public

  retainedModeNonzero :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (C : LiteralCutoffModeCarrier T) →
    (N : Nat) (time : Time) (mode : Z3.FourierMode) →
    mode Cube.∈ Audit.modes
      (Dyn.Base.systemAt (Dyn.forgetDynamics T) N time) →
    Z3.NonZeroMode mode
  retainedModeNonzero T C N time mode member =
    R404.nonzeroCutoffMemberNonzero
      (subst
        (λ modes → mode Cube.∈ modes)
        (retainedModesExact C N time)
        member)

literalModeListConstancyWithoutViscosity : Bool
literalModeListConstancyWithoutViscosity = true

literalModeListPaysRetainedNonzeroSupport : Bool
literalModeListPaysRetainedNonzeroSupport = true

positiveViscosityRequiredForModeListCarrier : Bool
positiveViscosityRequiredForModeListCarrier = false

literalModeListConstancyWithoutViscosityIsTrue :
  literalModeListConstancyWithoutViscosity ≡ true
literalModeListConstancyWithoutViscosityIsTrue = refl

literalModeListPaysRetainedNonzeroSupportIsTrue :
  literalModeListPaysRetainedNonzeroSupport ≡ true
literalModeListPaysRetainedNonzeroSupportIsTrue = refl

positiveViscosityRequiredForModeListCarrierIsFalse :
  positiveViscosityRequiredForModeListCarrier ≡ false
positiveViscosityRequiredForModeListCarrierIsFalse = refl
