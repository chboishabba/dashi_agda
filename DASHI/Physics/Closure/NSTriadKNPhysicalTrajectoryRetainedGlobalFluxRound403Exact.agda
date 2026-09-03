module DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact where

------------------------------------------------------------------------
-- ROUND403 / LIVE R240 TRAJECTORY -> SAME-OBJECT RETAINED R378 FLUX
--
-- The generic R240 trajectory intentionally cannot recover nonzero support from
-- Audit.zeroModeExcluded : Set.  Instead of pretending otherwise, expose the
-- exact missing carrier fact: every mode in the actual retained list is
-- nonzero.  With that one proof-bearing support realization, R240 already owns
-- all other data needed to build the Round30 physical wrapper at (N,t):
-- fixed E/I, the literal state system, all-mode transversality, and fixed
-- viscosity.
--
-- R400--R402 then construct every R290 pair-rate positivity witness from
-- positive viscosity.  This yields the instantaneous global R378 flux identity
-- on the SAME R379 debt, with no reciprocal or pair-positivity caller fields.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; Positive; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGramToPackageARound379Exact as R379
import DASHI.Physics.Closure.NSTriadKNPositiveViscosityRetainedGlobalGramFluxRound402Exact as R402

F : C3.RealField _
F = Rational.rationalRealField

module LiveTrajectoryFlux
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module G = R379.PhysicalGlobalGramToPackageA
    Time initialTime integrateTo DerivativeOf

  record RetainedSupportRealization
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set where
    field
      retainedModeNonzero :
        (N : Nat) (t : Time) (mode : Z3.FourierMode) →
        mode Cube.∈ Audit.modes
          (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t) →
        Z3.NonZeroMode mode

      physicalViscosityPositive : Positive (Dyn.physicalViscosity T)

  open RetainedSupportRealization public

  physicalSystemAt :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    RetainedSupportRealization T →
    Nat → Time →
    Field30.PhysicalFiniteComplex3GalerkinSystem F
  physicalSystemAt T R N t = record
    { Field30.physicalEmbedding = Dyn.Base.E (Dyn.forgetDynamics T)
    ; Field30.physicalInverseSquare = Dyn.Base.I (Dyn.forgetDynamics T)
    ; Field30.finiteSystem = state
    ; Field30.viscosity = Audit.viscosity state
    ; Field30.retainedModeNonzero = retainedModeNonzero R N t
    ; Field30.retainedVelocityTransverse =
        λ mode member → Dyn.Base.velocityTransverse
          (Dyn.forgetDynamics T) N t mode
    }
    where
    state = Dyn.Base.systemAt (Dyn.forgetDynamics T) N t

  stateViscosityPositive :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : RetainedSupportRealization T) →
    (N : Nat) (t : Time) →
    Positive (Field30.viscosity (physicalSystemAt T R N t))
  stateViscosityPositive T R N t =
    subst Positive
      (sym (Dyn.viscosityFixed T N t))
      (physicalViscosityPositive R)

  helicityDataAt :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : RetainedSupportRealization T) →
    (N : Nat) (t : Time) →
    R225.PhysicalFixedOutputHelicityData
      (Dyn.Base.E (Dyn.forgetDynamics T))
      (Dyn.Base.I (Dyn.forgetDynamics T))
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Dyn.Base.L (Dyn.forgetDynamics T))
      (Dyn.Base.H (Dyn.forgetDynamics T))
      (Audit.velocityAt
        (Dyn.Base.systemAt (Dyn.forgetDynamics T) N t))
  helicityDataAt T R N t =
    R225.physical-fixed-output-helicity-data
      (Dyn.Base.velocityTransverse (Dyn.forgetDynamics T) N t)

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : RetainedSupportRealization T)
      (N : Nat) (t : Time) where

    state = Dyn.Base.systemAt (Dyn.forgetDynamics T) N t
    PS = physicalSystemAt T R N t

    module Flux = R402.RetainedGlobalFlux
      PS
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Dyn.Base.L (Dyn.forgetDynamics T))
      (Dyn.Base.H (Dyn.forgetDynamics T))
      (helicityDataAt T R N t)
      (stateViscosityPositive T R N t)

    pairs = Flux.Global.globalPairs
      Flux.cutoff Flux.outputs Flux.retainedOutputPositivity

    weightedFluxTangent : ℚ
    weightedFluxTangent = R385.sumWeightedFluxTangent pairs

    weightedRemainder : ℚ
    weightedRemainder = R385.sumWeightedRemainder pairs

    literalR379DebtInstantaneousFlux :
      G.physicalGlobalGramDebt T N t
      ≡ (0ℚ - weightedFluxTangent) + weightedRemainder
    literalR379DebtInstantaneousFlux =
      let
        cutoffExact = Dyn.Base.systemCutoffAgreement
          (Dyn.forgetDynamics T) N t
        sameCutoff :
          R378.globalGramDebt
            (Dyn.Base.E (Dyn.forgetDynamics T))
            (Dyn.Base.S (Dyn.forgetDynamics T))
            (Audit.velocity state)
            N (Audit.modes state)
          ≡
          R378.globalGramDebt
            (Dyn.Base.E (Dyn.forgetDynamics T))
            (Dyn.Base.S (Dyn.forgetDynamics T))
            (Audit.velocity state)
            (Audit.cutoff state) (Audit.modes state)
        sameCutoff = cong
          (λ selectedCutoff →
            R378.globalGramDebt
              (Dyn.Base.E (Dyn.forgetDynamics T))
              (Dyn.Base.S (Dyn.forgetDynamics T))
              (Audit.velocity state)
              selectedCutoff (Audit.modes state))
          (sym cutoffExact)
      in
      trans sameCutoff Flux.literalRetainedGlobalGramFluxIdentity

round403GenericR240SupportRecoveredFromAuditMarkerAlone : Bool
round403GenericR240SupportRecoveredFromAuditMarkerAlone = false

round403OnlyExtraCarrierFactIsRetainedModeNonzero : Bool
round403OnlyExtraCarrierFactIsRetainedModeNonzero = true

round403PairRatePositivityCallerSupplied : Bool
round403PairRatePositivityCallerSupplied = false

round403LiteralR379DebtInstantaneousFluxClosed : Bool
round403LiteralR379DebtInstantaneousFluxClosed = true
