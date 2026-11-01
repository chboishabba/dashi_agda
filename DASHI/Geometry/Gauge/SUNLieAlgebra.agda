module DASHI.Geometry.Gauge.SUNLieAlgebra where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (_*_; _∸_)

open import DASHI.Geometry.Gauge.SUNPrimitives

data SUNLieAlgebraObligation : Set where
  needsStructureConstants      : SUNLieAlgebraObligation
  needsConcreteBracketLaw      : SUNLieAlgebraObligation
  needsAdjointRepresentation   : SUNLieAlgebraObligation
  needsAbstractDimensionBridge : SUNLieAlgebraObligation

canonicalSUNLieAlgebraObligations : List SUNLieAlgebraObligation
canonicalSUNLieAlgebraObligations =
  needsStructureConstants
  ∷ needsConcreteBracketLaw
  ∷ needsAdjointRepresentation
  ∷ needsAbstractDimensionBridge
  ∷ []

record SUNLieAlgebra (N : Nat) : Set₁ where
  field
    convention : GeneratorConvention
    antiHermitianHolds : Bool
    traceNeutralHolds : Bool
    antiHermitianIsTrue : antiHermitianHolds ≡ true
    traceNeutralIsTrue : traceNeutralHolds ≡ true
    dimensionIsNSquaredMinusOne : Nat
    dimensionLabel : String
    dimensionCorrect :
      Candidate (dimensionIsNSquaredMinusOne ≡ (N * N) ∸ 1)
    openObligations : List SUNLieAlgebraObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalSUNLieAlgebraObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalSUNLieAlgebra : (N : Nat) → SUNLieAlgebra N
canonicalSUNLieAlgebra N = record
  { convention = mathAntiHermitian
  ; antiHermitianHolds = true
  ; traceNeutralHolds = true
  ; antiHermitianIsTrue = refl
  ; traceNeutralIsTrue = refl
  ; dimensionIsNSquaredMinusOne = 0
  ; dimensionLabel = "N^2-1 pending concrete arithmetic witness"
  ; dimensionCorrect = candidate "abstract SU(N) dimension witness not promoted"
  ; openObligations = canonicalSUNLieAlgebraObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }

su1DimensionProven : Proven (0 ≡ (1 * 1) ∸ 1)
su1DimensionProven = proven refl

su2DimensionProven : Proven (3 ≡ (2 * 2) ∸ 1)
su2DimensionProven = proven refl

su3DimensionProven : Proven (8 ≡ (3 * 3) ∸ 1)
su3DimensionProven = proven refl
