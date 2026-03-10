module DASHI.Physics.Closure.ContractionForcesQuadraticTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record ContractionForcesQuadraticTheorem : Setω where
  field
    dimension : Nat
    projection : PD.ProjectionDefect (QES.AdditiveVecℤ {dimension})
    emergenceAxioms :
      QFE.QuadraticEmergenceAxioms
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ projection
    derivedQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    lorentzSignature : ⊤

canonicalContractionForcesQuadraticTheorem :
  (m : Nat) → ContractionForcesQuadraticTheorem
canonicalContractionForcesQuadraticTheorem m =
  record
    { dimension = m
    ; projection = QES.PDzero {m}
    ; emergenceAxioms = QES.QuadraticEmergenceShiftAxioms {m}
    ; derivedQuadratic =
        proj₁
          (QFE.QuadraticFormEmergence
             (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
             (QES.PDzero {m})
             (QES.QuadraticEmergenceShiftAxioms {m}))
    ; lorentzSignature = tt
    }
