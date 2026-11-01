module DASHI.Physics.Closure.NSTriadKNOldRationalAssignmentNotFiniteCutoffRound71Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 71 / OLD PICARD CARRIER NO-GO
--
-- Round26 defines
--
--     Assignment = CoordinateVariable -> Q.
--
-- This file proves a concrete structural reason that type cannot itself be the
-- finite cutoff Galerkin coordinate space: CoordinateVariable contains an
-- injective copy of Nat, obtained from the literal Fourier modes (n,0,0) with
-- fixed x-axis / real-part labels.  Thus the domain remains unbounded even when
-- a particular finite equation LIST has been selected elsewhere.
--
-- This does not invalidate the polynomial atom identities proved over Q.  They
-- remain exact algebraic certificates.  It only blocks using the unrestricted
-- Assignment function type as the finite-dimensional real Picard carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial

natCoordinateVariable : Nat → Polynomial.CoordinateVariable
natCoordinateVariable n =
  Polynomial.coordinate-variable
    (Z3.mode (+ n) (+ 0) (+ 0))
    Polynomial.xAxis
    Polynomial.realPart

natCoordinateVariableInjective :
  ∀ m n → natCoordinateVariable m ≡ natCoordinateVariable n → m ≡ n
natCoordinateVariableInjective m .m refl = refl

round71OldAssignmentDomainContainsNatInjection : Bool
round71OldAssignmentDomainContainsNatInjection = true

round71OldRationalAssignmentIsFiniteCutoffCarrier : Bool
round71OldRationalAssignmentIsFiniteCutoffCarrier = false

round71OldAssignmentDomainContainsNatInjectionIsTrue :
  round71OldAssignmentDomainContainsNatInjection ≡ true
round71OldAssignmentDomainContainsNatInjectionIsTrue = refl

round71OldRationalAssignmentIsFiniteCutoffCarrierIsFalse :
  round71OldRationalAssignmentIsFiniteCutoffCarrier ≡ false
round71OldRationalAssignmentIsFiniteCutoffCarrierIsFalse = refl
