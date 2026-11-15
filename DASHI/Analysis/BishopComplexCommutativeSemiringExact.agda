module DASHI.Analysis.BishopComplexCommutativeSemiringExact where

------------------------------------------------------------------------
-- THE ACTUAL STDLIB COMMUTATIVE SEMIRING ON ORIGINAL BISHOP COMPLEX.
--
-- Carrier: BishopComplexSeriesConvergenceExact.BishopComplex.
-- Equality: literal componentwise vendored Bishop real setoid.
-- Operations: BishopComplexAlgebraExact._+C_, _*C_, zeroC, oneC.
--
-- Every law is supplied by the explicit, original source proofs
-- in BishopComplexCommutativeSemiringLawsExact. No unproved fields.
------------------------------------------------------------------------

open import Algebra
open import Level using (0ℓ)
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws

originalBishopComplexEquivalence :
  IsEquivalence Complex._≈C_
originalBishopComplexEquivalence = record
  { refl = λ {x} → Complex.≈C-refl x
  ; sym = λ equivalent →
      BishopP.≃-symm (proj₁ equivalent)
      ,
      BishopP.≃-symm (proj₂ equivalent)
  ; trans = λ first second →
      BishopP.≃-trans (proj₁ first) (proj₁ second)
      ,
      BishopP.≃-trans (proj₂ first) (proj₂ second)
  }

originalBishopComplexAddMagma :
  IsMagma Complex._≈C_ Algebra._+C_
originalBishopComplexAddMagma = record
  { isEquivalence = originalBishopComplexEquivalence
  ; ∙-cong = Algebra.addCCongruent
  }

originalBishopComplexAddSemigroup :
  IsSemigroup Complex._≈C_ Algebra._+C_
originalBishopComplexAddSemigroup = record
  { isMagma = originalBishopComplexAddMagma
  ; assoc = Laws.complexAddAssociative
  }

originalBishopComplexAddMonoid :
  IsMonoid Complex._≈C_ Algebra._+C_ Algebra.zeroC
originalBishopComplexAddMonoid = record
  { isSemigroup = originalBishopComplexAddSemigroup
  ; identity =
      Laws.complexAddLeftIdentity
      ,
      Laws.complexAddRightIdentity
  }

originalBishopComplexAddCommutativeMonoid :
  IsCommutativeMonoid Complex._≈C_ Algebra._+C_ Algebra.zeroC
originalBishopComplexAddCommutativeMonoid = record
  { isMonoid = originalBishopComplexAddMonoid
  ; comm = Laws.complexAddCommutative
  }

originalBishopComplexSemiringWithoutZero :
  IsSemiringWithoutAnnihilatingZero
    Complex._≈C_ Algebra._+C_ Algebra._*C_
    Algebra.zeroC Algebra.oneC
originalBishopComplexSemiringWithoutZero = record
  { +-isCommutativeMonoid = originalBishopComplexAddCommutativeMonoid
  ; *-cong = Algebra.mulCCongruent
  ; *-assoc = Laws.complexMultiplyAssociative
  ; *-identity =
      Laws.complexMultiplyLeftIdentity
      ,
      Laws.complexMultiplyRightIdentity
  ; distrib =
      Laws.complexMultiplyDistributesLeft
      ,
      Laws.complexMultiplyDistributesRight
  }

originalBishopComplexIsSemiring :
  IsSemiring
    Complex._≈C_ Algebra._+C_ Algebra._*C_
    Algebra.zeroC Algebra.oneC
originalBishopComplexIsSemiring = record
  { isSemiringWithoutAnnihilatingZero =
      originalBishopComplexSemiringWithoutZero
  ; zero =
      Laws.complexMultiplyLeftZero
      ,
      Laws.complexMultiplyRightZero
  }

originalBishopComplexIsCommutativeSemiring :
  IsCommutativeSemiring
    Complex._≈C_ Algebra._+C_ Algebra._*C_
    Algebra.zeroC Algebra.oneC
originalBishopComplexIsCommutativeSemiring = record
  { isSemiring = originalBishopComplexIsSemiring
  ; *-comm = Laws.complexMultiplyCommutative
  }

originalBishopComplexCommutativeSemiring :
  CommutativeSemiring 0ℓ 0ℓ
originalBishopComplexCommutativeSemiring = record
  { isCommutativeSemiring =
      originalBishopComplexIsCommutativeSemiring
  }


-- Export the exact semiring projection for stdlib Semiring.Exp/Mult.
originalBishopComplexSemiring : Semiring 0ℓ 0ℓ
originalBishopComplexSemiring = record
  { isSemiring = originalBishopComplexIsSemiring
  }
