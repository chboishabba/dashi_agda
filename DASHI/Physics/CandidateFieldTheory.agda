module DASHI.Physics.CandidateFieldTheory where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Observable as Obs
open import DASHI.Physics.QuantumHistory as QH
open import DASHI.Physics.ClassicalEmergence as CE
open import DASHI.Physics.Benchmark as Bench

record CandidateFieldTheory (ℓ : Level) : Set (lsuc ℓ) where
  field
    classical   : PT.PhysicalTheory ℓ
    symmetric   : SQ.SymmetricTheory ℓ
    quotiented  : SQ.QuotientedTheory ℓ
    observables : Obs.ObservableTheory quotiented

    histories   : QH.HistoryTheory ℓ
    amplitudes  : QH.AmplitudeCarrier ℓ
    quantumHist : QH.QuantumHistory histories amplitudes

    qEvolution  : CE.QuantumEvolution ℓ
    emergence   : CE.ApproxClassicalEmergence qEvolution classical

    benchmark   : Bench.BenchmarkTheory′ quotiented
