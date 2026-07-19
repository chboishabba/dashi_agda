module DASHI.Physics.YangMills.BalabanSchurGenericInstance where

open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (refl)

open import DASHI.Analysis.BlockSchurStructure
open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore as Finite

------------------------------------------------------------------------
-- Exact adapter: the existing Bałaban finite one-step Schur object is an
-- instance of the domain-neutral structure, with no loss of determinant data.
------------------------------------------------------------------------

balabanBlockSchurStructure :
  ∀ {a s}
    {Vector : Set a}
    {Scalar : Set s} →
  Finite.BlockSchurData Vector Scalar →
  BlockSchurStructure Vector
balabanBlockSchurStructure B = record
  { aBlock = Finite.aBlock B
  ; bBlock = Finite.bBlock B
  ; cBlock = Finite.cBlock B
  ; dBlock = Finite.dBlock B
  ; aInverse = Finite.aInverse B
  ; add = Finite.add B
  ; subtract = Finite.subtract B
  ; compose = Finite.compose B
  ; crossCorrection =
      Finite.compose B
        (Finite.cBlock B)
        (Finite.compose B (Finite.aInverse B) (Finite.bBlock B))
  ; crossDefinition = refl
  ; schurComplement = Finite.schurComplement B
  ; schurDefinition = Finite.schurDefinition B
  }

balabanDeterminantFactorization :
  ∀ {a s}
    {Vector : Set a}
    {Scalar : Set s}
    (B : Finite.BlockSchurData Vector Scalar) →
  BlockDeterminantFactorization
    (balabanBlockSchurStructure B)
    Scalar
balabanDeterminantFactorization B = record
  { determinant = Finite.determinant B
  ; scalarMultiply = Finite.scalarMultiply B
  ; determinantFactorization = Finite.determinantFactorization B
  }
