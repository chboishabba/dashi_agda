module DASHI.Algebra.Jacobian.InvertibilityStrata where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Local differential information and global inverse information occupy
-- distinct promotion strata.

data InvertibilityLevel : Set where
  derivativeNonsingular : InvertibilityLevel
  locallyInvertible : InvertibilityLevel
  finiteFibre : InvertibilityLevel
  globallyInjective : InvertibilityLevel
  globallyBijective : InvertibilityLevel
  polynomiallyInvertible : InvertibilityLevel

data InverseKind : Set where
  globalInverse : InverseKind
  localInverse : InverseKind
  section : InverseKind
  branchSelectedInverse : InverseKind
  approximateInverse : InverseKind
  fibreEnumeration : InverseKind

record InvertibilityReceipt
       (Map Point : Set) : Set₁ where
  field
    map : Map
    point : Point
    derivativeNonsingularWitness : Set
    localInverseWitness : Set
    finiteFibreWitness : Set
    globalInjectiveWitness : Set
    globalBijectiveWitness : Set
    polynomialInverseWitness : Set

open InvertibilityReceipt public

record PromotionBoundary : Set where
  constructor promotionBoundary
  field
    derivativeImpliesLocal : Bool
    derivativeImpliesGlobalInjective : Bool
    localImpliesGlobalInverse : Bool
    finiteFibreImpliesInjective : Bool
    branchReceiptRequired : Bool

open PromotionBoundary public

canonicalPromotionBoundary : PromotionBoundary
canonicalPromotionBoundary =
  promotionBoundary true false false false true

canonicalLocalDoesNotImplyGlobal :
  localImpliesGlobalInverse canonicalPromotionBoundary ≡ false
canonicalLocalDoesNotImplyGlobal = refl

record BranchSelection
       (X Y Branch : Set)
       (f : X → Y) : Set₁ where
  field
    target : Y
    branch : Branch
    selectedSource : X
    selectedSourceMapsToTarget : f selectedSource ≡ target
    historyReceipt : Set
    continuityReceipt : Set

open BranchSelection public
