module DASHI.Geometry.CausalSignaturePackageVacuityControlExact where

-- Attribution: existing source DASHI.Geometry.CausalForcesLorentz31;
-- independent mathematical concern: circular admissibility assumptions
-- and logically unconstrained witnesses. New bounded negative control:
-- every CausalSymmetryPackage field can be instantiated with Unit, even
-- without constructing a metric, cone, four-dimensionality or observer.
-- This DOES NOT refute other original finite/nonvacuous cone proofs.
-- User research motivation: check whether 3+1 was truly derived before
-- being promoted through KK, TSFV, SUSY/string or 369/YM.
-- ChatGPT-assisted original-source audit, 2026-11-18.

open import Data.Unit using (⊤; tt)
import DASHI.Geometry.CausalForcesLorentz31 as Source

-- The record's field TYPES are arbitrary Set targets accompanied by
-- their inhabitants. A fully trivial witness therefore exists.
trivialCausalSymmetryPackage : Source.CausalSymmetryPackage
trivialCausalSymmetryPackage = record
  { coneNontrivial = ⊤
  ; coneNontrivialWitness = tt
  ; arrowOrientation = ⊤
  ; arrowOrientationWitness = tt
  ; isotropyEvidence = ⊤
  ; isotropyWitness = tt
  ; finiteSpeed = ⊤
  ; finiteSpeedWitness = tt
  ; involution = ⊤
  ; involutionWitness = tt
  ; nondegenerateQuadratic = ⊤
  ; nondegenerateQuadraticWitness = tt
  ; quotientContraction = ⊤
  ; quotientContractionWitness = tt
  }

-- No metric, cone, time arrow, isotropy group or measured signature
-- was supplied to build the above object. The underlying author's
-- conditional algebraic outputs are not thereby false; their promotion
-- as a signature-neutral physical uniqueness theorem is the problem.
