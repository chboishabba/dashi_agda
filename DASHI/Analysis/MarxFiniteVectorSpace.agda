module DASHI.Analysis.MarxFiniteVectorSpace where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set₁)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPowerRuleNormalisation
open import DASHI.Analysis.MarxScalarFrechetBridge
open import DASHI.Analysis.MarxHigherCalculus

------------------------------------------------------------------------
-- Literal finite coordinate vectors.

zeroVector :
  {A : MarxAlgebra} →
  (n : Nat) → Vec (Carrier A) n
zeroVector zero = []
zeroVector {A} (suc n) = zero A ∷ zeroVector n

addVector :
  {A : MarxAlgebra} →
  ∀ {n} →
  Vec (Carrier A) n →
  Vec (Carrier A) n →
  Vec (Carrier A) n
addVector [] [] = []
addVector {A} (x ∷ xs) (y ∷ ys) =
  _+_ A x y ∷ addVector xs ys

scaleVector :
  {A : MarxAlgebra} →
  ∀ {n} →
  Carrier A →
  Vec (Carrier A) n →
  Vec (Carrier A) n
scaleVector scalar [] = []
scaleVector {A} scalar (x ∷ xs) =
  _*_ A scalar x ∷ scaleVector scalar xs

addZeroLeftVector :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  ∀ {n} (v : Vec (Carrier A) n) →
  addVector (zeroVector n) v ≡ v
addZeroLeftVector L [] = refl
addZeroLeftVector {A} L (x ∷ xs) =
  cong₂ _∷_
    (MarxPowerAlgebraLaws.addZeroLeftLaw
      (MarxScalarModuleLaws.powerLaws L) x)
    (addZeroLeftVector L xs)

addZeroRightVector :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  ∀ {n} (v : Vec (Carrier A) n) →
  addVector v (zeroVector n) ≡ v
addZeroRightVector L [] = refl
addZeroRightVector {A} L (x ∷ xs) =
  cong₂ _∷_
    (MarxPowerAlgebraLaws.addZeroRightLaw
      (MarxScalarModuleLaws.powerLaws L) x)
    (addZeroRightVector L xs)

addAssocVector :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  ∀ {n}
    (u v w : Vec (Carrier A) n) →
  addVector (addVector u v) w
  ≡ addVector u (addVector v w)
addAssocVector L [] [] [] = refl
addAssocVector {A} L (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_
    (MarxPowerAlgebraLaws.addAssocLaw
      (MarxScalarModuleLaws.powerLaws L) x y z)
    (addAssocVector L xs ys zs)

scaleZeroVector :
  {A : MarxAlgebra} →
  ∀ {n} scalar →
  scaleVector scalar (zeroVector {A} n) ≡ zeroVector n
scaleZeroVector {n = zero} scalar = refl
scaleZeroVector {A} {n = suc n} scalar =
  cong₂ _∷_
    (mulZeroRight A scalar)
    (scaleZeroVector {A} {n} scalar)

scaleOneVector :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  ∀ {n} (v : Vec (Carrier A) n) →
  scaleVector (one A) v ≡ v
scaleOneVector L [] = refl
scaleOneVector {A} L (x ∷ xs) =
  cong₂ _∷_
    (mulOneLeft (MarxScalarModuleLaws.powerLaws L) x)
    (scaleOneVector L xs)

scaleDistributesAddVector :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  ∀ {n} scalar
    (u v : Vec (Carrier A) n) →
  scaleVector scalar (addVector u v)
  ≡ addVector (scaleVector scalar u) (scaleVector scalar v)
scaleDistributesAddVector L scalar [] [] = refl
scaleDistributesAddVector {A} L scalar (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_
    (MarxScalarModuleLaws.distribLeftLaw L scalar x y)
    (scaleDistributesAddVector L scalar xs ys)

finiteVectorModule :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n : Nat) →
  Module A
finiteVectorModule L n =
  record
    { Vector = Vec (Carrier _) n
    ; zeroV = zeroVector n
    ; _+V_ = addVector
    ; _•_ = scaleVector
    ; addZeroLeftV = addZeroLeftVector L
    ; addZeroRightV = addZeroRightVector L
    ; addAssocV = addAssocVector L
    ; scaleZeroV = scaleZeroVector
    ; scaleOneV = scaleOneVector L
    ; scaleDistributesAddV = scaleDistributesAddVector L
    }

------------------------------------------------------------------------
-- Canonical finite basis and coordinate functionals.

basisVector :
  {A : MarxAlgebra} →
  ∀ {n} →
  Fin n → Vec (Carrier A) n
basisVector {n = suc n} fzero =
  one _ ∷ zeroVector n
basisVector {A} {n = suc n} (fsuc i) =
  zero A ∷ basisVector i

lookupVector :
  {A : MarxAlgebra} →
  ∀ {n} →
  Fin n → Vec (Carrier A) n → Carrier A
lookupVector fzero (x ∷ xs) = x
lookupVector (fsuc i) (x ∷ xs) = lookupVector i xs

finiteVectorBasis :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n : Nat) →
  FiniteBasis (finiteVectorModule L n)
finiteVectorBasis L n =
  record
    { Index = Fin n
    ; basis = basisVector
    }

finiteCoordinateFunctional :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n : Nat) →
  CoordinateFunctional (finiteVectorModule L n)
finiteCoordinateFunctional L n =
  record
    { Row = Fin n
    ; coordinate = lookupVector
    }

finiteJacobianFromFrechet :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n : Nat) →
  {R : VectorLittleOStructure A
    (finiteVectorModule L n)
    (finiteVectorModule L n)} →
  {f : Vec (Carrier A) n → Vec (Carrier A) n} →
  {x : Vec (Carrier A) n} →
  FrechetDerivativeAt R f x →
  JacobianAt
    (finiteVectorBasis L n)
    (finiteCoordinateFunctional L n)
finiteJacobianFromFrechet L n =
  jacobianFromFrechet
    (finiteVectorBasis L n)
    (finiteCoordinateFunctional L n)
