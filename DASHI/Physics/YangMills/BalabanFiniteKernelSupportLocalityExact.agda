module DASHI.Physics.YangMills.BalabanFiniteKernelSupportLocalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Michel Combes and Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- RG1c is useful for RG1d only if Green-kernel decay controls the response to
-- a perturbation supported far away.  The ordinary Schur bound in
-- BalabanFiniteMatrixL1ContractionExact requires a column bound everywhere.
-- Here we prove the sharper support-local version:
--
--   for every column j, either s_j = 0 or colmass(G,j) <= q_R
--       ==> ||G s||_1 <= q_R ||s||_1.
--
-- Thus Combes--Thomas only has to provide the exponentially small column bound
-- on the ACTUAL support of the remote source.  Near columns, where the kernel
-- need not be small, are harmless because their source coefficient is exactly
-- zero.  This is the finite algebraic bridge needed by the nonlinear
-- minimizer-response argument; it avoids replacing locality by a global
-- operator norm estimate.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1

applyKernelL1BoundOnSourceSupport : ∀ {Index : Set}
  (indices : List Index)
  (kernel : L1.SquareKernel Index)
  (vector : L1.Vector Index)
  q →
  0ℚ ≤ q →
  (∀ column →
    vector column ≡ 0ℚ
    ⊎ ColumnMass.squareColumnMass indices kernel column ≤ q) →
  L1.vectorL1 indices (L1.applyKernel indices kernel vector)
  ≤ q * L1.vectorL1 indices vector
applyKernelL1BoundOnSourceSupport indices kernel vector q qNonnegative supportBound =
  let
    fubini = L1.applyL1FubiniUpper indices kernel vector

    pointwise : ∀ column →
      ∣ vector column ∣
        * ColumnMass.squareColumnMass indices kernel column
      ≤ ∣ vector column ∣ * q
    pointwise column with supportBound column
    ... | inj₁ vectorZero rewrite vectorZero = ℚP.≤-refl
    ... | inj₂ columnBound =
      Norm.scaleNonnegative ∣ vector column ∣
        (ℚP.0≤∣p∣ (vector column))
        columnBound

    summed = Schur.sumPointwiseBelow indices _ _ pointwise

    factor :
      Sums.sumRational indices
        (λ column → ∣ vector column ∣ * q)
      ≡ q * L1.vectorL1 indices vector
    factor =
      trans
        (Sums.sumRationalCong indices _ _
          (λ column → ℚP.*-comm ∣ vector column ∣ q))
        (Sums.sumRationalScale q indices
          (λ column → ∣ vector column ∣))
  in
  ℚP.≤-trans fubini
    (subst
      (λ upper →
        Sums.sumRational indices
          (λ column →
            ∣ vector column ∣
              * ColumnMass.squareColumnMass indices kernel column)
        ≤ upper)
      factor summed)

finiteKernelSupportLocalityLevel : ProofLevel
finiteKernelSupportLocalityLevel = machineChecked
