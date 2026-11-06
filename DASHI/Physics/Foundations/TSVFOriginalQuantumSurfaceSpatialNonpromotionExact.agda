{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalQuantumSurfaceSpatialNonpromotionExact where

-- S01-S04 formal nonpromotion control.
--
-- QuantumSurface's abstract fields alone cannot force a nontrivial
-- spatial propagation cone, dimension four or a Lorentz principal
-- symbol. One VALID source instance has a single possible ket,
-- single possible time and single operator. This is a countermodel
-- to claiming such geometry solely from the abstract record axioms,
-- not a claim about the intended physical original universe.
--
-- The physically selected TSVF needs extra independent source owners:
-- located physical probes, operator spatial support, calibrated clock,
-- quantitative transport estimates and a symbol/dimension theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Quantum.TSVF as TSVF

trivialValidTSVFQuantumSurface : TSVF.QuantumSurface
trivialValidTSVFQuantumSurface = record
  { TSVF.QuantumSurface.Scalar = ⊤
  ; TSVF.QuantumSurface.Weight = ⊤
  ; TSVF.QuantumSurface.Ket = ⊤
  ; TSVF.QuantumSurface.Bra = ⊤
  ; TSVF.QuantumSurface.Operator = ⊤
  ; TSVF.QuantumSurface.Time = ⊤
  ; TSVF.QuantumSurface.evolveKet = λ _ _ _ → tt
  ; TSVF.QuantumSurface.evolveBra = λ _ _ _ → tt
  ; TSVF.QuantumSurface.apply = λ _ _ → tt
  ; TSVF.QuantumSurface.pair = λ _ _ → tt
  ; TSVF.QuantumSurface.normSquared = λ _ → tt
  ; TSVF.QuantumSurface.divideWeight = λ _ _ → tt
  ; TSVF.QuantumSurface.Positive = λ _ → ⊤
  }

trivialSelectedEnsemble :
  TSVF.TSVFEnsemble trivialValidTSVFQuantumSurface
trivialSelectedEnsemble =
  TSVF.prePostSelected tt tt tt tt tt

trivialAllTimesIdentical :
  (first second :
    TSVF.QuantumSurface.Time trivialValidTSVFQuantumSurface) →
  first ≡ second
trivialAllTimesIdentical tt tt = refl

trivialAllKetsIdentical :
  (first second :
    TSVF.QuantumSurface.Ket trivialValidTSVFQuantumSurface) →
  first ≡ second
trivialAllKetsIdentical tt tt = refl

trivialAllOperatorsIdentical :
  (first second :
    TSVF.QuantumSurface.Operator trivialValidTSVFQuantumSurface) →
  first ≡ second
trivialAllOperatorsIdentical tt tt = refl

trivialNoDistinctTimeCoordinates :
  (first second :
    TSVF.QuantumSurface.Time trivialValidTSVFQuantumSurface) →
  (first ≡ second → ⊥) → ⊥
trivialNoDistinctTimeCoordinates first second separated =
  separated (trivialAllTimesIdentical first second)

trivialNoDistinctOperators :
  (first second :
    TSVF.QuantumSurface.Operator trivialValidTSVFQuantumSurface) →
  (first ≡ second → ⊥) → ⊥
trivialNoDistinctOperators first second separated =
  separated (trivialAllOperatorsIdentical first second)

-- A theorem "every QuantumSurface has a genuinely nontrivial
-- 3-space + 1-time propagation cone" would contradict this model.
-- This prevents using the abstract TSVF record to counterfeit the
-- physical P01/P02 geometry and identifies the true input boundary.
