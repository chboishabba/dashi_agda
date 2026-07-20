module DASHI.Physics.Unification.UnificationGate where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)

open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.CandidateFieldTheory as CFT
open import DASHI.Physics.Refinement as Ref
open import DASHI.Physics.QuantumHistory as QH
open import DASHI.Physics.Measurement as Meas
open import DASHI.Physics.ClassicalEmergence as CE
open import DASHI.Physics.Laws.PhysicalLawCore as Law
open import DASHI.Physics.Laws.EffectiveLimitHierarchy as Limit

-- The four gates are deliberately separate.  A candidate cannot promote by
-- possessing only a discrete transition system, only a symmetry action, or
-- only a benchmark fit.
record DiscretizationCorrect {ℓ : Level}
  (C : CFT.CandidateFieldTheory ℓ) : Set (lsuc ℓ) where
  field
    tower : Ref.RefinementTower ℓ

    classical-at-base :
      Ref.RefinementTower.TheoryAt tower zero ≡
      CFT.CandidateFieldTheory.classical C

    ContinuumState Grid Error ScaleLaw : Set ℓ
    interpolate :
      (n : Nat) →
      PT.State (Ref.RefinementTower.TheoryAt tower n) →
      ContinuumState

    errorAt :
      (n : Nat) →
      PT.State (Ref.RefinementTower.TheoryAt tower n) →
      Error

    controlled-limit : Set ℓ
    grid-independence : Set ℓ
    scaling-law       : ScaleLaw

record TrueSymmetryStructure {ℓ : Level}
  (C : CFT.CandidateFieldTheory ℓ) : Set (lsuc ℓ) where
  field
    quantum-covariance :
      QH.SymmetricQuantumHistory
        (CFT.CandidateFieldTheory.symmetric C)
        (CFT.CandidateFieldTheory.histories C)
        (CFT.CandidateFieldTheory.amplitudes C)
        (CFT.CandidateFieldTheory.quantumHist C)

    gauge-invariance-recovered : Set ℓ
    lorentz-invariance-recovered : Set ℓ
    diffeomorphism-invariance-recovered : Set ℓ

    symmetry-survives-refinement : Set ℓ
    observables-descend-to-quotient : Set ℓ

record QuantumStructure {ℓ : Level}
  (C : CFT.CandidateFieldTheory ℓ) : Set (lsuc ℓ) where
  field
    stateSpace : QH.LinearSpaceLike (CFT.CandidateFieldTheory.amplitudes C)

    norm-preserving-evolution : Set ℓ
    superposition-law         : Set ℓ
    interference-witness      : Set ℓ
    noncommuting-observables  : Set ℓ

    born : Meas.BornLike (CFT.CandidateFieldTheory.amplitudes C)

record MeasurementPrediction {ℓ : Level}
  (C : CFT.CandidateFieldTheory ℓ) : Set (lsuc ℓ) where
  field
    measurement :
      Meas.MeasurementTheory
        (CFT.CandidateFieldTheory.quotiented C)
        (CFT.CandidateFieldTheory.observables C)
        (CFT.CandidateFieldTheory.amplitudes C)

    quantumMeasurement :
      Meas.QuantumMeasurement
        (CE.QuantumEvolution.QState (CFT.CandidateFieldTheory.qEvolution C))
        (CFT.CandidateFieldTheory.amplitudes C)

    state-to-observable-agreement : Set ℓ
    repeated-trial-statistics     : Set ℓ
    refinement-stable-prediction  : Set ℓ
    falsifiable-observable        : Set ℓ
    experimental-match            : Set ℓ

-- This record is the explicit bridge across the deepest mismatch in the
-- thread: microscopic quantum evolution is information preserving, while the
-- effective classical dynamics may be contractive only after coarse
-- observation/environmental projection.
record UnitaryContractiveBridge {ℓ : Level}
  (C : CFT.CandidateFieldTheory ℓ) : Set (lsuc ℓ) where
  field
    effective :
      CE.ContractiveEmergence
        (CFT.CandidateFieldTheory.qEvolution C)
        (CFT.CandidateFieldTheory.classical C)

    microscopic-information-preserved : Set ℓ
    contraction-only-after-coarse-map  : Set ℓ
    stable-classical-sectors           : Set ℓ

record QGRecovery {ℓ : Level}
  (C : CFT.CandidateFieldTheory ℓ) : Set (lsuc ℓ) where
  field
    lawSurface : Law.PhysicalLawSurface
    continuumBoundary : Limit.ContinuumLimitBoundary
    empiricalAuthority : Law.EmpiricalAuthorityBoundary lawSurface

    discretization : DiscretizationCorrect C
    symmetry       : TrueSymmetryStructure C
    quantum        : QuantumStructure C
    measurement    : MeasurementPrediction C
    emergence      : UnitaryContractiveBridge C

    low-energy-QFT : Set ℓ
    low-energy-GR  : Set ℓ
    matter-gravity-coupling : Set ℓ
    anomaly-freedom : Set ℓ
    causal-unitary-consistency : Set ℓ

-- The only promotion constructor consumes every gate.  There is no Boolean or
-- status label from which a QG result can self-promote.
data UnifiedQuantumGravity {ℓ : Level}
  (C : CFT.CandidateFieldTheory ℓ) : Set (lsuc ℓ) where
  unified : QGRecovery C → UnifiedQuantumGravity C
