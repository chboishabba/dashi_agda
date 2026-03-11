module DASHI.Physics.Closure.ContractionForcesQuadraticTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record ContractionForcesQuadraticTheorem : Setω where
  field
    dimension : Nat
    projection : PD.ProjectionDefect (QES.AdditiveVecℤ {dimension})
    projectionParallelogram :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    derivedQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    lorentzSignature : ⊤

canonicalContractionForcesQuadraticTheorem :
  (m : Nat) → ContractionForcesQuadraticTheorem
canonicalContractionForcesQuadraticTheorem m =
  let
    proj = QES.PDzero {m}
    pkg =
      PDP.fromEmergenceAxioms
        (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ proj
        (QES.QuadraticEmergenceShiftAxioms {m})
  in
  record
    { dimension = m
    ; projection = proj
    ; projectionParallelogram = pkg
    ; derivedQuadratic =
        proj₁
          (PDP.quadraticFromProjectionDefect
             (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ pkg)
    ; lorentzSignature = tt
    }
