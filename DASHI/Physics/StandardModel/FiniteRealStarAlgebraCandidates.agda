module DASHI.Physics.StandardModel.FiniteRealStarAlgebraCandidates where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Finite-dimensional semisimple real *-algebras are represented here by
-- finite sums of matrix factors over R, C, or H.  This is a structural
-- candidate universe only; it does not assert the Artin-Wedderburn theorem.
------------------------------------------------------------------------

data DivisionCarrier : Set where
  real complex quaternion : DivisionCarrier

record MatrixFactor : Set where
  constructor matrixFactor
  field
    carrier : DivisionCarrier
    rank : Nat

open MatrixFactor public

FiniteRealStarAlgebra : Set
FiniteRealStarAlgebra = List MatrixFactor

------------------------------------------------------------------------
-- Morita type forgets matrix rank while retaining the division carrier.
------------------------------------------------------------------------

MoritaType : Set
MoritaType = List DivisionCarrier

moritaFactor : MatrixFactor → DivisionCarrier
moritaFactor (matrixFactor K _) = K

moritaType : FiniteRealStarAlgebra → MoritaType
moritaType [] = []
moritaType (f ∷ fs) = moritaFactor f ∷ moritaType fs

------------------------------------------------------------------------
-- Gauge-family labels associated with the compact unitary groups of factors.
-- These labels are deliberately coarse: they expose the classification target
-- without claiming a Lie-group isomorphism theorem in this module.
------------------------------------------------------------------------

data CompactFamily : Set where
  orthogonalFamily unitaryFamily symplecticFamily : CompactFamily

compactFamily : MatrixFactor → CompactFamily
compactFamily (matrixFactor real _) = orthogonalFamily
compactFamily (matrixFactor complex _) = unitaryFamily
compactFamily (matrixFactor quaternion _) = symplecticFamily

------------------------------------------------------------------------
-- Canonical candidates used by the pruning layer.
------------------------------------------------------------------------

realOnly : FiniteRealStarAlgebra
realOnly = matrixFactor real 1 ∷ []

complexOnly : FiniteRealStarAlgebra
complexOnly = matrixFactor complex 1 ∷ []

quaternionOnly : FiniteRealStarAlgebra
quaternionOnly = matrixFactor quaternion 1 ∷ []

weakHyperchargeCandidate : FiniteRealStarAlgebra
weakHyperchargeCandidate =
  matrixFactor complex 1 ∷
  matrixFactor quaternion 1 ∷
  []

standardModelSpine : FiniteRealStarAlgebra
standardModelSpine =
  matrixFactor complex 1 ∷
  matrixFactor quaternion 1 ∷
  matrixFactor complex 3 ∷
  []

standardModelMoritaType :
  moritaType standardModelSpine ≡ complex ∷ quaternion ∷ complex ∷ []
standardModelMoritaType = refl

weakFactorFamily :
  compactFamily (matrixFactor quaternion 1) ≡ symplecticFamily
weakFactorFamily = refl

colourFactorFamily :
  compactFamily (matrixFactor complex 3) ≡ unitaryFamily
colourFactorFamily = refl
