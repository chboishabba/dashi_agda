module DASHI.Physics.Closure.ContractionForcesQuadraticTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; proj₁)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP

record ContractionForcesQuadraticTheorem : Setω where
  field
    dimension : Nat
    projection : PD.ProjectionDefect (QES.AdditiveVecℤ {dimension})
    projectionParallelogram :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    derivedQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    signature31Value : CTI.Signature
    signatureForced31 : signature31Value ≡ CTI.sig31

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
    ; signature31Value = S31OP.signature31
    ; signatureForced31 = refl
    }
