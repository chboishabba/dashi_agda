module DASHI.Physics.SignatureClassificationBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import Ultrametric as UMetric
open import DASHI.Combinatorics.Entropy using (Involution)
open import DASHI.Physics.ContractionQuadraticBridge as CQ
open import DASHI.Geometry.RealIsotropy.Core as RIS
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS

record Signature : Set where
  field
    p : Nat
    q : Nat

record SymmetryPackage
  {S : Set}
  (U : UMetric.Ultrametric S)
  (T : S → S)
  : Set₁ where
  field
    inv : Involution S
    iso : RIS.RealIsotropy U T
    fs  : RFS.RealFiniteSpeed T

open SymmetryPackage public

record Quadratic⇒Signature : Set₁ where
  field
    classify :
      ∀ {S : Set} {U : UMetric.Ultrametric S} {T : S → S} →
      (out : CQ.QuadraticOutput) →
      (sym : SymmetryPackage U T) →
      Signature

open Quadratic⇒Signature public

record ContractionSymmetry⇒Signature
  {S : Set}
  (U : UMetric.Ultrametric S)
  (T : S → S)
  : Set₁ where
  field
    cq  : CQ.Contraction⇒Quadratic U T
    sym : SymmetryPackage U T
    qs  : Quadratic⇒Signature

  sig : Signature
  sig = classify qs (CQ.out cq) sym
