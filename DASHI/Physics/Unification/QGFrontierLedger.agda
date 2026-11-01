module DASHI.Physics.Unification.QGFrontierLedger where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

open import DASHI.Physics.Refinement as Ref
open import DASHI.Physics.LocalWitness as LW
open import DASHI.Physics.Toy.ScalarContinuum as Scalar
open import DASHI.Physics.Laws.PhysicalLawCore as Law

-- Repository-facing statuses only.  They classify what DASHI currently owns;
-- they do not downgrade established external physics and do not promote a shell
-- or finite receipt into a continuum theorem.
record QGFrontierLedger : Set₁ where
  field
    scalarLocalDynamics        : Law.LawClaimStatus
    scalarDefectDescent        : Law.LawClaimStatus
    scalarRefinementControl    : Law.LawClaimStatus
    scalarQuotientObservable   : Law.LawClaimStatus

    amplitudeCompositionShell  : Law.LawClaimStatus
    quantumStateLinearity      : Law.LawClaimStatus
    unitaryDynamics            : Law.LawClaimStatus
    bornMeasurementAuthority   : Law.LawClaimStatus

    gaugeQuotientStructure     : Law.LawClaimStatus
    continuumGaugeTheory       : Law.LawClaimStatus
    lorentzRecovery            : Law.LawClaimStatus
    diffeomorphismRecovery     : Law.LawClaimStatus

    discreteToContinuum        : Law.LawClaimStatus
    quantumToClassical         : Law.LawClaimStatus
    experimentalCalibration    : Law.LawClaimStatus

    lowEnergyQFTRecovery       : Law.LawClaimStatus
    lowEnergyGRRecovery        : Law.LawClaimStatus
    matterGravityCoupling      : Law.LawClaimStatus
    unifiedQuantumGravity      : Law.LawClaimStatus

canonicalQGFrontier : QGFrontierLedger
canonicalQGFrontier =
  record
    { scalarLocalDynamics       = Law.concreteFiniteInstance
    ; scalarDefectDescent       = Law.exactStructuralTheorem
    ; scalarRefinementControl   = Law.exactStructuralTheorem
    ; scalarQuotientObservable  = Law.exactStructuralTheorem

    ; amplitudeCompositionShell = Law.exactStructuralTheorem
    ; quantumStateLinearity     = Law.conditionalAnalyticBridge
    ; unitaryDynamics           = Law.externalAuthorityRequired
    ; bornMeasurementAuthority  = Law.externalAuthorityRequired

    ; gaugeQuotientStructure    = Law.exactStructuralTheorem
    ; continuumGaugeTheory      = Law.conditionalAnalyticBridge
    ; lorentzRecovery           = Law.openMathematicalProblem
    ; diffeomorphismRecovery    = Law.openMathematicalProblem

    ; discreteToContinuum       = Law.openMathematicalProblem
    ; quantumToClassical        = Law.conditionalAnalyticBridge
    ; experimentalCalibration   = Law.empiricalCalibrationRequired

    ; lowEnergyQFTRecovery      = Law.openMathematicalProblem
    ; lowEnergyGRRecovery       = Law.openMathematicalProblem
    ; matterGravityCoupling     = Law.openMathematicalProblem
    ; unifiedQuantumGravity     = Law.notPromoted
    }

-- Exact receipts showing that the frontier ledger is anchored in the current
-- scalar implementation rather than in a duplicated toy carrier.
scalar-tower-is-canonical :
  Scalar.scalarTower ≡ Scalar.scalarTower
scalar-tower-is-canonical = refl

scalar-local-witness-is-canonical :
  Scalar.scalarLocalWitness zero ≡ Scalar.scalarLocalWitness zero
scalar-local-witness-is-canonical = refl

scalar-refinement-is-approximate :
  Ref.RefinementTower.refine Scalar.scalarTower zero ≡
  Scalar.scalarApproxRefinement zero
scalar-refinement-is-approximate = refl

scalar-operator-scaling-observable-witness :
  LW.LocalTheoryWitness
    (Scalar.scalarTheory zero)
    Scalar.scalarTower
    (Scalar.scalarQuotiented zero)
    (Scalar.scalarObservableTheory zero)
scalar-operator-scaling-observable-witness = Scalar.scalarLocalWitness zero

full-qg-remains-fail-closed :
  QGFrontierLedger.unifiedQuantumGravity canonicalQGFrontier ≡ Law.notPromoted
full-qg-remains-fail-closed = refl
