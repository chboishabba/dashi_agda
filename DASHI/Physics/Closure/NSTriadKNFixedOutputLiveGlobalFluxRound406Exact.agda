module DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact where

------------------------------------------------------------------------
-- ROUND406 / TIME-STABLE CANONICAL OUTPUT LIST FOR THE LIVE R378 FLUX
--
-- R403 attached the instantaneous flux identity to a live trajectory, but its
-- pair list was indexed by `Audit.modes(state_t)`.  R405 identifies that list
-- with the fixed literal `nonzeroCutoffModes N`.  For temporal differentiation
-- it is cleaner to construct the observable directly on this fixed list.
--
-- This owner does so.  At every time t:
--
--   outputs_N = nonzeroCutoffModes N
--
-- is independent of t.  R404 proves each output nonzero; R400 constructs every
-- local pair-rate positivity witness; R398 builds the exact global R290 list.
-- The resulting instantaneous identity is transported back to the SAME R379
-- physical Gram debt using only R405's exact output-list equality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGramToPackageARound379Exact as R379
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405

F : C3.RealField _
F = Rational.rationalRealField

module FixedLiveFlux
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R403.LiveTrajectoryFlux
    Time initialTime integrateTo DerivativeOf
  module G = R379.PhysicalGlobalGramToPackageA
    Time initialTime integrateTo DerivativeOf

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (N : Nat) (t : Time) where

    support = Support.toRetainedSupportRealization T R
    PS = Live.physicalSystemAt T support N t
    state = Dyn.Base.systemAt (Dyn.forgetDynamics T) N t
    outputs : List Z3.FourierMode
    outputs = Canonical.nonzeroCutoffModes N

    P : R225.PhysicalFixedOutputHelicityData
      (Dyn.Base.E (Dyn.forgetDynamics T))
      (Dyn.Base.I (Dyn.forgetDynamics T))
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Dyn.Base.L (Dyn.forgetDynamics T))
      (Dyn.Base.H (Dyn.forgetDynamics T))
      (Audit.velocity state)
    P = R225.physical-fixed-output-helicity-data
      (Dyn.Base.velocityTransverse (Dyn.forgetDynamics T) N t)

    module Global = R398.GlobalFluxLocal
      PS
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Dyn.Base.L (Dyn.forgetDynamics T))
      (Dyn.Base.H (Dyn.forgetDynamics T)) P

    module Rate = R400.PhysicalRate
      PS
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Live.stateViscosityPositive T support N t)

    buildCanonicalOutputPositivity :
      (selected : List Z3.FourierMode) →
      ((mode : Z3.FourierMode) →
        mode Cube.∈ selected → mode Cube.∈ outputs) →
      Global.OutputFibresPositiveOn N selected
    buildCanonicalOutputPositivity [] included = Global.positiveOutputsNil
    buildCanonicalOutputPositivity (output ∷ rest) included =
      Global.positiveOutputsCons
        (Rate.physicalOutputFibrePairRatesPositive
          N output
          (R404.nonzeroCutoffMemberNonzero
            (included output (Cube.here refl))))
        (buildCanonicalOutputPositivity rest
          (λ mode member → included mode (Cube.there member)))

    canonicalOutputPositivity :
      Global.OutputFibresPositiveOn N outputs
    canonicalOutputPositivity =
      buildCanonicalOutputPositivity outputs (λ mode member → member)

    pairs = Global.globalPairs N outputs canonicalOutputPositivity

    offDiagonalFlux : ℚ
    offDiagonalFlux = R385.sumWeightedFlux pairs

    offDiagonalFluxTangent : ℚ
    offDiagonalFluxTangent = R385.sumWeightedFluxTangent pairs

    weightedRemainder : ℚ
    weightedRemainder = R385.sumWeightedRemainder pairs

    canonicalDebt : ℚ
    canonicalDebt = R378.globalGramDebt
      (Dyn.Base.E (Dyn.forgetDynamics T))
      (Dyn.Base.S (Dyn.forgetDynamics T))
      (Audit.velocity state) N outputs

    canonicalDebtFluxIdentity :
      canonicalDebt
      ≡ (0ℚ - offDiagonalFluxTangent) + weightedRemainder
    canonicalDebtFluxIdentity =
      Global.literalGlobalGramFluxIdentity N outputs canonicalOutputPositivity

    r379DebtIsCanonicalDebt : G.physicalGlobalGramDebt T N t ≡ canonicalDebt
    r379DebtIsCanonicalDebt =
      cong
        (λ selectedOutputs →
          R378.globalGramDebt
            (Dyn.Base.E (Dyn.forgetDynamics T))
            (Dyn.Base.S (Dyn.forgetDynamics T))
            (Audit.velocity state) N selectedOutputs)
        (Support.retainedModesExact R N t)

    r379DebtFluxIdentity :
      G.physicalGlobalGramDebt T N t
      ≡ (0ℚ - offDiagonalFluxTangent) + weightedRemainder
    r379DebtFluxIdentity =
      trans r379DebtIsCanonicalDebt canonicalDebtFluxIdentity

round406OutputIndexListIndependentOfTime : Bool
round406OutputIndexListIndependentOfTime = true

round406PairRatePositivityConstructedFromPositiveViscosity : Bool
round406PairRatePositivityConstructedFromPositiveViscosity = true

round406LiteralR379DebtOnFixedOutputListHasR290FluxIdentity : Bool
round406LiteralR379DebtOnFixedOutputListHasR290FluxIdentity = true

round406ActualTimeDerivativeOfFluxProved : Bool
round406ActualTimeDerivativeOfFluxProved = false
