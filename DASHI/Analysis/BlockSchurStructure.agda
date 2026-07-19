module DASHI.Analysis.BlockSchurStructure where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Structural Schur socket shared by finite RG and shell-transfer problems.
------------------------------------------------------------------------

record BlockSchurStructure
    {v : Level}
    (Vector : Set v) : Set (lsuc v) where
  field
    aBlock bBlock cBlock dBlock : Vector → Vector
    aInverse : Vector → Vector

    add subtract compose :
      (Vector → Vector) →
      (Vector → Vector) →
      Vector → Vector

    crossCorrection : Vector → Vector
    crossDefinition :
      crossCorrection ≡ compose cBlock (compose aInverse bBlock)

    schurComplement : Vector → Vector
    schurDefinition :
      schurComplement ≡ subtract dBlock crossCorrection

open BlockSchurStructure public

record BlockDeterminantFactorization
    {v s : Level}
    {Vector : Set v}
    (B : BlockSchurStructure Vector)
    (Scalar : Set s) : Set (lsuc (v ⊔ s)) where
  field
    determinant : (Vector → Vector) → Scalar
    scalarMultiply : Scalar → Scalar → Scalar

    determinantFactorization :
      determinant
        (add B
          (aBlock B)
          (add B (bBlock B) (add B (cBlock B) (dBlock B))))
      ≡
      scalarMultiply
        (determinant (aBlock B))
        (determinant (schurComplement B))

open BlockDeterminantFactorization public
