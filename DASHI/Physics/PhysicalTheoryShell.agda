module DASHI.Physics.PhysicalTheoryShell where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.Refinement as Ref
open import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Observable as Obs
open import DASHI.Physics.QuantumHistory as QH
open import DASHI.Physics.Measurement as Meas
open import DASHI.Physics.ClassicalEmergence as CE
open import DASHI.Physics.Benchmark as Bench
open import DASHI.Physics.CandidateFieldTheory as CFT

record PhysicalTheoryShell (ℓ : Level) : Set (lsuc ℓ) where
  field
    base       : PT.PhysicalTheory ℓ
    refinement : Ref.RefinementTower ℓ
    quotiented : SQ.QuotientedTheory ℓ
    observable : Obs.ObservableTheory quotiented
    prediction : Meas.PredictionTheory quotiented
    candidate  : CFT.CandidateFieldTheory ℓ
