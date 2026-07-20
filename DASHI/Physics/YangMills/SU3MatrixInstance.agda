module DASHI.Physics.YangMills.SU3MatrixInstance where

------------------------------------------------------------------------
-- Named N = 3 specialization of the certified SU(N) matrix stack.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_*_; _∸_)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.SUNMatrixCarrier
open import DASHI.Physics.YangMills.SUNMatrixLieAlgebra
open import DASHI.Physics.YangMills.SUNMatrixLieGroup

SU3Dimension : Nat
SU3Dimension = 8

su3DimensionCorrect : SU3Dimension ≡ (3 * 3) ∸ 1
su3DimensionCorrect = refl

SU3MatrixTheory :
  ∀ {m c} (Matrix : Set m) (Complex : Set c) → Set (Level.suc (m Level.⊔ c))
SU3MatrixTheory Matrix Complex = CertifiedSUNMatrixTheory 3 Matrix Complex

su3MatrixGroup :
  ∀ {m c} {Matrix : Set m} {Complex : Set c} →
  (theory : CertifiedSUNMatrixTheory 3 Matrix Complex) →
  Group (SUNMatrixElement theory)
su3MatrixGroup = sunMatrixGroup

su3MatrixLieAlgebra :
  ∀ {m c} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory 3 Matrix Complex} →
  (lieTheory : CertifiedSUNMatrixLieTheory 3 groupTheory) →
  LieAlgebra (SUNMatrixLieElement lieTheory)
su3MatrixLieAlgebra = sunMatrixLieAlgebra

su3CompactSimpleLieGroup :
  ∀ {m c} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory 3 Matrix Complex}
    {lieTheory : CertifiedSUNMatrixLieTheory 3 groupTheory} →
  CertifiedSUNMatrixLieGroupAuthority 3 groupTheory lieTheory →
  CompactSimpleLieGroup
    (SUNMatrixElement groupTheory)
    (SUNMatrixLieElement lieTheory)
su3CompactSimpleLieGroup = sunCompactSimpleLieGroup

su3DimensionLevel : ProofLevel
su3DimensionLevel = computed

su3MatrixAssemblyLevel : ProofLevel
su3MatrixAssemblyLevel = machineChecked

su3FiniteMatrixAuthorityLevel : ProofLevel
su3FiniteMatrixAuthorityLevel = standardImported
