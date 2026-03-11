module DASHI.Physics.SignatureClassificationBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import Ultrametric as UMetric
open import DASHI.Combinatorics.Entropy using (Involution)
open import DASHI.Physics.ContractionQuadraticBridge as CQ
open import DASHI.Geometry.RealIsotropy.Core as RIS
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.SignatureUniqueness31 as SU

record SignatureClassification : Set₁ where
  field
    p : Nat
    q : Nat
    signatureValue : CTI.Signature
    signatureForced31 : signatureValue ≡ CTI.sig31
    signatureTheorem : SU.Signature31Theorem

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

record Quadratic⇒Signature : Set₂ where
  field
    classify :
      ∀ {S : Set} {U : UMetric.Ultrametric S} {T : S → S} →
      (out : CQ.QuadraticOutput) →
      (sym : SymmetryPackage U T) →
      SignatureClassification

open Quadratic⇒Signature public

record ContractionSymmetry⇒Signature
  {S : Set}
  (U : UMetric.Ultrametric S)
  (T : S → S)
  : Set₂ where
  field
    cq  : CQ.Contraction⇒Quadratic U T
    sym : SymmetryPackage U T
    qs  : Quadratic⇒Signature

  sig : SignatureClassification
  sig = classify qs (CQ.out cq) sym
