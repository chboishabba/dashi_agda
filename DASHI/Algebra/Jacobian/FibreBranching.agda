module DASHI.Algebra.Jacobian.FibreBranching where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Reconstruction from an image is fibre-valued unless a unique branch is
-- separately proved or selected.

record Fibre
       {X Y : Set}
       (f : X → Y)
       (target : Y) : Set₁ where
  field
    source : X
    mapsToTarget : f source ≡ target

open Fibre public

record FibreWitnessSet
       {X Y : Set}
       (f : X → Y)
       (target : Y) : Set₁ where
  field
    first : Fibre f target
    second : Fibre f target
    third : Fibre f target
    firstSecondDistinct : Set
    firstThirdDistinct : Set
    secondThirdDistinct : Set

open FibreWitnessSet public

record ReconstructionBoundary : Set where
  constructor reconstructionBoundary
  field
    imageDeterminesUniqueSource : Bool
    branchReceiptRequired : Bool
    historyCanDistinguishBranches : Bool
    fibreEnumerationIsInverse : Bool

open ReconstructionBoundary public

canonicalReconstructionBoundary : ReconstructionBoundary
canonicalReconstructionBoundary =
  reconstructionBoundary false true true false

canonicalImageDoesNotDetermineUniqueSource :
  imageDeterminesUniqueSource canonicalReconstructionBoundary ≡ false
canonicalImageDoesNotDetermineUniqueSource = refl

record BranchResidual
       (Source Target Branch History Residual : Set) : Set₁ where
  field
    source : Source
    target : Target
    branch : Branch
    history : History
    residual : Residual

open BranchResidual public
