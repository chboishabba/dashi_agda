module DASHI.Analysis.NonArchimedeanCharacterBasisMatrixFaithfulnessReuseExact where

------------------------------------------------------------------------
-- CHARACTER-BASIS ACTION -> MATRIX EQUALITY REUSE
--
-- The repo already owns a finite-coordinate theorem in the Yang--Mills Gate-4
-- lane: equality of matrix actions implies literal matrix equality, proved by
-- evaluating on the standard coordinate basis.  The non-Archimedean spectral
-- lane should reuse that theorem rather than expand every DFT-conjugated matrix
-- entry independently.
--
-- This wrapper also exposes the sharper form needed here: equality on every
-- basis vector already determines every matrix entry and therefore the matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCanonicalFreeBasisExact
  using (Fin; lookupVec)
import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoordinateMatrixEquivalenceExact as Coordinate

basisActionDeterminesFiniteMatrix :
  ∀ {Scalar n}
    (algebra : Coordinate.CommutativeSemiringLaws Scalar)
    {left right : Coordinate.FiniteMatrix Scalar n} →
  Coordinate.matrixAction algebra left ≡ Coordinate.matrixAction algebra right →
  left ≡ right
basisActionDeterminesFiniteMatrix = Coordinate.matrixActionInjective

basisVectorsDetermineFiniteMatrix :
  ∀ {Scalar n}
    (algebra : Coordinate.CommutativeSemiringLaws Scalar)
    {left right : Coordinate.FiniteMatrix Scalar n} →
  ((column : Fin n) →
    Coordinate.matrixAction algebra left
      (Coordinate.basisVector algebra column)
    ≡ Coordinate.matrixAction algebra right
      (Coordinate.basisVector algebra column)) →
  left ≡ right
basisVectorsDetermineFiniteMatrix algebra {left} {right} basisEquality =
  Coordinate.vecExt (λ row →
    Coordinate.vecExt (λ column →
      trans
        (sym (Coordinate.matrixActionOnBasisEntry
          algebra left row column))
        (trans
          (cong (λ vector → lookupVec vector row)
            (basisEquality column))
          (Coordinate.matrixActionOnBasisEntry
            algebra right row column))))

record SpectralBasisActionWeld : Set₁ where
  field
    Scalar : Set
    n : Nat
    scalarLaws : Coordinate.CommutativeSemiringLaws Scalar
    conjugatedMatrix monomialMatrix : Coordinate.FiniteMatrix Scalar n
    sameActionOnBasis :
      (column : Fin n) →
      Coordinate.matrixAction scalarLaws conjugatedMatrix
        (Coordinate.basisVector scalarLaws column)
      ≡ Coordinate.matrixAction scalarLaws monomialMatrix
        (Coordinate.basisVector scalarLaws column)

open SpectralBasisActionWeld public

basisActionWeldClosesMatrixEquality :
  (weld : SpectralBasisActionWeld) →
  conjugatedMatrix weld ≡ monomialMatrix weld
basisActionWeldClosesMatrixEquality weld =
  basisVectorsDetermineFiniteMatrix
    (scalarLaws weld)
    (sameActionOnBasis weld)

record BasisActionReuseBoundary : Set where
  constructor basisActionReuseBoundary
  field
    finiteMatrixActionFaithfulnessOwnedInRepo : Bool
    equalityOnCompleteBasisSuffices : Bool
    entrywiseDFTExpansionIsRequiredPrimaryRoute : Bool
    basisActionEqualitySufficesForLiteralMatrixEquality : Bool
    sourceSpecificCharacterIdentificationStillRequired : Bool

canonicalBasisActionReuseBoundary : BasisActionReuseBoundary
canonicalBasisActionReuseBoundary =
  basisActionReuseBoundary true true false true true

entrywiseExpansionPruned :
  BasisActionReuseBoundary.entrywiseDFTExpansionIsRequiredPrimaryRoute
    canonicalBasisActionReuseBoundary
  ≡ false
entrywiseExpansionPruned = refl

basisEqualityPromotesLiteralMatrixEquality :
  BasisActionReuseBoundary.equalityOnCompleteBasisSuffices
    canonicalBasisActionReuseBoundary
  ≡ true
basisEqualityPromotesLiteralMatrixEquality = refl
