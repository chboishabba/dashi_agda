module DASHI.Analysis.NonArchimedeanCharacterBasisMatrixFaithfulnessReuseExact where

------------------------------------------------------------------------
-- CHARACTER-BASIS ACTION -> MATRIX EQUALITY REUSE
--
-- The repo already owns a finite-coordinate theorem in the Yang--Mills Gate-4
-- lane: equality of matrix actions implies literal matrix equality, proved by
-- evaluating on the standard coordinate basis.  The non-Archimedean spectral
-- lane should reuse that theorem rather than expand every DFT-conjugated matrix
-- entry independently.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoordinateMatrixEquivalenceExact as Coordinate

basisActionDeterminesFiniteMatrix :
  ∀ {Scalar n}
    (algebra : Coordinate.CommutativeSemiringLaws Scalar)
    {left right : Coordinate.FiniteMatrix Scalar n} →
  Coordinate.matrixAction algebra left ≡ Coordinate.matrixAction algebra right →
  left ≡ right
basisActionDeterminesFiniteMatrix = Coordinate.matrixActionInjective

record SpectralBasisActionWeld : Set₁ where
  field
    Scalar : Set
    n : Nat
    scalarLaws : Coordinate.CommutativeSemiringLaws Scalar
    conjugatedMatrix monomialMatrix : Coordinate.FiniteMatrix Scalar n
    sameAction :
      Coordinate.matrixAction scalarLaws conjugatedMatrix
      ≡ Coordinate.matrixAction scalarLaws monomialMatrix

open SpectralBasisActionWeld public

basisActionWeldClosesMatrixEquality :
  (weld : SpectralBasisActionWeld) →
  conjugatedMatrix weld ≡ monomialMatrix weld
basisActionWeldClosesMatrixEquality weld =
  basisActionDeterminesFiniteMatrix
    (scalarLaws weld)
    (sameAction weld)

record BasisActionReuseBoundary : Set where
  constructor basisActionReuseBoundary
  field
    finiteMatrixActionFaithfulnessOwnedInRepo : Bool
    entrywiseDFTExpansionIsRequiredPrimaryRoute : Bool
    basisActionEqualitySufficesForLiteralMatrixEquality : Bool
    sourceSpecificCharacterIdentificationStillRequired : Bool

canonicalBasisActionReuseBoundary : BasisActionReuseBoundary
canonicalBasisActionReuseBoundary =
  basisActionReuseBoundary true false true true

entrywiseExpansionPruned :
  BasisActionReuseBoundary.entrywiseDFTExpansionIsRequiredPrimaryRoute
    canonicalBasisActionReuseBoundary
  ≡ false
entrywiseExpansionPruned = refl
