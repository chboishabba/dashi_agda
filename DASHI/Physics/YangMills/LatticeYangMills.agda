module DASHI.Physics.YangMills.LatticeYangMills where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives

data LatticeYangMillsObligation : Set where
  needsFiniteVolumeMeasure : LatticeYangMillsObligation
  needsTransferMatrixLane  : LatticeYangMillsObligation
  needsReflectionPositivity : LatticeYangMillsObligation
  needsContinuumLimitRoute : LatticeYangMillsObligation

canonicalLatticeYangMillsObligations : List LatticeYangMillsObligation
canonicalLatticeYangMillsObligations =
  needsFiniteVolumeMeasure
  ∷ needsTransferMatrixLane
  ∷ needsReflectionPositivity
  ∷ needsContinuumLimitRoute
  ∷ []

record LatticeYangMills (N : Nat) : Set₁ where
  field
    latticeShape : String
    edgeGroupDefined : Bool
    plaquetteHolonomyDefined : Bool
    wilsonActionDefined : Bool
    partitionFunctionDefined : Bool
    edgeGroupDefinedIsTrue : edgeGroupDefined ≡ true
    plaquetteHolonomyDefinedIsTrue : plaquetteHolonomyDefined ≡ true
    wilsonActionDefinedIsTrue : wilsonActionDefined ≡ true
    partitionFunctionDefinedIsTrue : partitionFunctionDefined ≡ true
    latticeGapExists : Bool
    latticeGapExistsIsFalse : latticeGapExists ≡ false
    openObligations : List LatticeYangMillsObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalLatticeYangMillsObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalLatticeYangMills : (N : Nat) → LatticeYangMills N
canonicalLatticeYangMills N = record
  { latticeShape = "hypercubic-4D"
  ; edgeGroupDefined = true
  ; plaquetteHolonomyDefined = true
  ; wilsonActionDefined = true
  ; partitionFunctionDefined = true
  ; edgeGroupDefinedIsTrue = refl
  ; plaquetteHolonomyDefinedIsTrue = refl
  ; wilsonActionDefinedIsTrue = refl
  ; partitionFunctionDefinedIsTrue = refl
  ; latticeGapExists = false
  ; latticeGapExistsIsFalse = refl
  ; openObligations = canonicalLatticeYangMillsObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
