module DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact where

------------------------------------------------------------------------
-- ROUND405 / LITERAL NONZERO-CUTOFF EQUALITY -> R403 SUPPORT REALIZATION
--
-- The only support information R403 needs is proof that every retained output
-- is nonzero.  R404 already derives that from membership in Round34's literal
-- `nonzeroCutoffModes N`.  Therefore a live R240 trajectory whose actual mode
-- list is equal to that canonical list automatically supplies R403 support.
--
-- This is the correct replacement for attempting to eliminate
-- `Audit.modesAreLiteralCutoff : Set`.  Round71's fixedAuditSystem has exactly
-- this mode list definitionally, so its specialization pays this seam by refl.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; Positive)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403

F : C3.RealField _
F = Rational.rationalRealField

module LiteralCutoffSupport
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Live = R403.LiveTrajectoryFlux Time initialTime integrateTo DerivativeOf

  record LiteralNonzeroCutoffTrajectory
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set where
    field
      retainedModesExact :
        (N : Nat) (t : Time) →
        Audit.modes (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t)
        ≡ Canonical.nonzeroCutoffModes N

      physicalViscosityPositive : Positive (Dyn.physicalViscosity T)

  open LiteralNonzeroCutoffTrajectory public

  retainedModeNonzeroFromLiteralCutoff :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : LiteralNonzeroCutoffTrajectory T) →
    (N : Nat) (t : Time) (mode : Z3.FourierMode) →
    mode Cube.∈ Audit.modes
      (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t) →
    Z3.NonZeroMode mode
  retainedModeNonzeroFromLiteralCutoff T R N t mode member =
    R404.nonzeroCutoffMemberNonzero
      (subst
        (λ modes → mode Cube.∈ modes)
        (retainedModesExact R N t)
        member)

  toRetainedSupportRealization :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    LiteralNonzeroCutoffTrajectory T →
    Live.RetainedSupportRealization T
  toRetainedSupportRealization T R = record
    { Live.retainedModeNonzero =
        retainedModeNonzeroFromLiteralCutoff T R
    ; Live.physicalViscosityPositive = physicalViscosityPositive R
    }

round405WeakAuditMarkerUsed : Bool
round405WeakAuditMarkerUsed = false

round405LiteralModeListEqualityPaysSupport : Bool
round405LiteralModeListEqualityPaysSupport = true

round405Round71ModeSupportDefinitionalTargetIdentified : Bool
round405Round71ModeSupportDefinitionalTargetIdentified = true
