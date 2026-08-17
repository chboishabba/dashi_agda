module DASHI.Moonshine.P37SourceForcedT3T5HeckeExact where

------------------------------------------------------------------------
-- EXECUTABLE / DATA SOURCE
--
-- LMFDB, space 37.2.a (level 37, weight 2, trivial character), no DOI asserted
-- for the database itself.  It records the two one-dimensional newforms
--
--   37.2.a.a : (a2,a3,a5) = (-2,-3,-2), Fricke sign +,
--   37.2.a.b : (a2,a3,a5) = ( 0, 1, 0), Fricke sign -.
--
-- PRIMARY MATHEMATICAL CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- The existing source p=37 T2 matrix and geometric Frobenius decomposition
-- identify the a2=-2 line as Frobenius-odd and the a2=0 line as the even
-- nonconstant line.  Requiring the same symmetric Brandt carrier, row degree
-- ell+1, and the two source newform eigenvalues yields the positive matrices
--
--   B37(3) = [[2,1,1],[1,0,3],[1,3,0]],
--   B37(5) = [[2,2,2],[2,1,3],[2,3,1]].
--
-- This file realizes both matrices as literal finite neighbour systems,
-- verifies every row, proves Frobenius multiplicity equivariance, and computes
-- their simultaneous eigenvalues on the already-constructed constant/even/odd
-- basis.  This is source-forced spectral reconstruction, not an independent
-- modular-polynomial reduction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Controls
import DASHI.Moonshine.P37NonOggPositiveHeckeControlExact as T2
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as Frob
import DASHI.Moonshine.P11P37HeckeFrobeniusJointSpectrumExact as Spectrum

------------------------------------------------------------------------
-- Literal positive T3 neighbours.
------------------------------------------------------------------------

p37T3Neighbour : Controls.P37BrandtClass → Fin 4 → Controls.P37BrandtClass
p37T3Neighbour Controls.p37c0 zero = Controls.p37c0
p37T3Neighbour Controls.p37c0 (suc zero) = Controls.p37c0
p37T3Neighbour Controls.p37c0 (suc (suc zero)) = Controls.p37c1
p37T3Neighbour Controls.p37c0 (suc (suc (suc zero))) = Controls.p37c2
p37T3Neighbour Controls.p37c1 zero = Controls.p37c0
p37T3Neighbour Controls.p37c1 (suc zero) = Controls.p37c2
p37T3Neighbour Controls.p37c1 (suc (suc zero)) = Controls.p37c2
p37T3Neighbour Controls.p37c1 (suc (suc (suc zero))) = Controls.p37c2
p37T3Neighbour Controls.p37c2 zero = Controls.p37c0
p37T3Neighbour Controls.p37c2 (suc zero) = Controls.p37c1
p37T3Neighbour Controls.p37c2 (suc (suc zero)) = Controls.p37c1
p37T3Neighbour Controls.p37c2 (suc (suc (suc zero))) = Controls.p37c1

P37T3 : Positive.PositiveFiniteNeighbourSystem Controls.P37BrandtClass
P37T3 = record
  { Positive.arity = 4
  ; Positive.neighbour = p37T3Neighbour
  }

------------------------------------------------------------------------
-- Literal positive T5 neighbours.
------------------------------------------------------------------------

p37T5Neighbour : Controls.P37BrandtClass → Fin 6 → Controls.P37BrandtClass
p37T5Neighbour Controls.p37c0 zero = Controls.p37c0
p37T5Neighbour Controls.p37c0 (suc zero) = Controls.p37c0
p37T5Neighbour Controls.p37c0 (suc (suc zero)) = Controls.p37c1
p37T5Neighbour Controls.p37c0 (suc (suc (suc zero))) = Controls.p37c1
p37T5Neighbour Controls.p37c0 (suc (suc (suc (suc zero)))) = Controls.p37c2
p37T5Neighbour Controls.p37c0 (suc (suc (suc (suc (suc zero))))) = Controls.p37c2
p37T5Neighbour Controls.p37c1 zero = Controls.p37c0
p37T5Neighbour Controls.p37c1 (suc zero) = Controls.p37c0
p37T5Neighbour Controls.p37c1 (suc (suc zero)) = Controls.p37c1
p37T5Neighbour Controls.p37c1 (suc (suc (suc zero))) = Controls.p37c2
p37T5Neighbour Controls.p37c1 (suc (suc (suc (suc zero)))) = Controls.p37c2
p37T5Neighbour Controls.p37c1 (suc (suc (suc (suc (suc zero))))) = Controls.p37c2
p37T5Neighbour Controls.p37c2 zero = Controls.p37c0
p37T5Neighbour Controls.p37c2 (suc zero) = Controls.p37c0
p37T5Neighbour Controls.p37c2 (suc (suc zero)) = Controls.p37c1
p37T5Neighbour Controls.p37c2 (suc (suc (suc zero))) = Controls.p37c1
p37T5Neighbour Controls.p37c2 (suc (suc (suc (suc zero)))) = Controls.p37c1
p37T5Neighbour Controls.p37c2 (suc (suc (suc (suc (suc zero))))) = Controls.p37c2

P37T5 : Positive.PositiveFiniteNeighbourSystem Controls.P37BrandtClass
P37T5 = record
  { Positive.arity = 6
  ; Positive.neighbour = p37T5Neighbour
  }

------------------------------------------------------------------------
-- Matrix rows as exact Nat counts.
------------------------------------------------------------------------

p37T3Row0 :
  Positive.positiveOperator P37T3 T2.isC0 Controls.p37c0 ≡ 2
  × Positive.positiveOperator P37T3 T2.isC1 Controls.p37c0 ≡ 1
  × Positive.positiveOperator P37T3 T2.isC2 Controls.p37c0 ≡ 1
p37T3Row0 = refl , refl , refl

p37T3Row1 :
  Positive.positiveOperator P37T3 T2.isC0 Controls.p37c1 ≡ 1
  × Positive.positiveOperator P37T3 T2.isC1 Controls.p37c1 ≡ 0
  × Positive.positiveOperator P37T3 T2.isC2 Controls.p37c1 ≡ 3
p37T3Row1 = refl , refl , refl

p37T3Row2 :
  Positive.positiveOperator P37T3 T2.isC0 Controls.p37c2 ≡ 1
  × Positive.positiveOperator P37T3 T2.isC1 Controls.p37c2 ≡ 3
  × Positive.positiveOperator P37T3 T2.isC2 Controls.p37c2 ≡ 0
p37T3Row2 = refl , refl , refl

p37T5Row0 :
  Positive.positiveOperator P37T5 T2.isC0 Controls.p37c0 ≡ 2
  × Positive.positiveOperator P37T5 T2.isC1 Controls.p37c0 ≡ 2
  × Positive.positiveOperator P37T5 T2.isC2 Controls.p37c0 ≡ 2
p37T5Row0 = refl , refl , refl

p37T5Row1 :
  Positive.positiveOperator P37T5 T2.isC0 Controls.p37c1 ≡ 2
  × Positive.positiveOperator P37T5 T2.isC1 Controls.p37c1 ≡ 1
  × Positive.positiveOperator P37T5 T2.isC2 Controls.p37c1 ≡ 3
p37T5Row1 = refl , refl , refl

p37T5Row2 :
  Positive.positiveOperator P37T5 T2.isC0 Controls.p37c2 ≡ 2
  × Positive.positiveOperator P37T5 T2.isC1 Controls.p37c2 ≡ 3
  × Positive.positiveOperator P37T5 T2.isC2 Controls.p37c2 ≡ 1
p37T5Row2 = refl , refl , refl

------------------------------------------------------------------------
-- Frobenius equivariance at multiplicity level.
------------------------------------------------------------------------

indicator : Controls.P37BrandtClass → Controls.P37BrandtClass → Nat
indicator Controls.p37c0 = T2.isC0
indicator Controls.p37c1 = T2.isC1
indicator Controls.p37c2 = T2.isC2

multiplicity :
  Positive.PositiveFiniteNeighbourSystem Controls.P37BrandtClass →
  Controls.P37BrandtClass → Controls.P37BrandtClass → Nat
multiplicity system source target =
  Positive.positiveOperator system (indicator target) source

p37T3FrobeniusEquivariant :
  (source target : Controls.P37BrandtClass) →
  multiplicity P37T3 (Frob.brandtFrobenius source) (Frob.brandtFrobenius target)
  ≡ multiplicity P37T3 source target
p37T3FrobeniusEquivariant Controls.p37c0 Controls.p37c0 = refl
p37T3FrobeniusEquivariant Controls.p37c0 Controls.p37c1 = refl
p37T3FrobeniusEquivariant Controls.p37c0 Controls.p37c2 = refl
p37T3FrobeniusEquivariant Controls.p37c1 Controls.p37c0 = refl
p37T3FrobeniusEquivariant Controls.p37c1 Controls.p37c1 = refl
p37T3FrobeniusEquivariant Controls.p37c1 Controls.p37c2 = refl
p37T3FrobeniusEquivariant Controls.p37c2 Controls.p37c0 = refl
p37T3FrobeniusEquivariant Controls.p37c2 Controls.p37c1 = refl
p37T3FrobeniusEquivariant Controls.p37c2 Controls.p37c2 = refl

p37T5FrobeniusEquivariant :
  (source target : Controls.P37BrandtClass) →
  multiplicity P37T5 (Frob.brandtFrobenius source) (Frob.brandtFrobenius target)
  ≡ multiplicity P37T5 source target
p37T5FrobeniusEquivariant Controls.p37c0 Controls.p37c0 = refl
p37T5FrobeniusEquivariant Controls.p37c0 Controls.p37c1 = refl
p37T5FrobeniusEquivariant Controls.p37c0 Controls.p37c2 = refl
p37T5FrobeniusEquivariant Controls.p37c1 Controls.p37c0 = refl
p37T5FrobeniusEquivariant Controls.p37c1 Controls.p37c1 = refl
p37T5FrobeniusEquivariant Controls.p37c1 Controls.p37c2 = refl
p37T5FrobeniusEquivariant Controls.p37c2 Controls.p37c0 = refl
p37T5FrobeniusEquivariant Controls.p37c2 Controls.p37c1 = refl
p37T5FrobeniusEquivariant Controls.p37c2 Controls.p37c2 = refl

------------------------------------------------------------------------
-- Integer actions and exact source eigencharacters.
------------------------------------------------------------------------

p37T3Action : Spectrum.P37IntTriple → Spectrum.P37IntTriple
p37T3Action v = Spectrum.intTriple
  (((+ 2) *ℤ Spectrum.c0 v) +ℤ Spectrum.c1 v +ℤ Spectrum.c2 v)
  (Spectrum.c0 v +ℤ ((+ 3) *ℤ Spectrum.c2 v))
  (Spectrum.c0 v +ℤ ((+ 3) *ℤ Spectrum.c1 v))

p37T5Action : Spectrum.P37IntTriple → Spectrum.P37IntTriple
p37T5Action v = Spectrum.intTriple
  (((+ 2) *ℤ Spectrum.c0 v) +ℤ ((+ 2) *ℤ Spectrum.c1 v) +ℤ ((+ 2) *ℤ Spectrum.c2 v))
  (((+ 2) *ℤ Spectrum.c0 v) +ℤ Spectrum.c1 v +ℤ ((+ 3) *ℤ Spectrum.c2 v))
  (((+ 2) *ℤ Spectrum.c0 v) +ℤ ((+ 3) *ℤ Spectrum.c1 v) +ℤ Spectrum.c2 v)

p37T3ConstantEigen :
  p37T3Action Spectrum.p37ConstantMode
  ≡ Spectrum.scaleTriple (+ 4) Spectrum.p37ConstantMode
p37T3ConstantEigen = refl

p37T3EvenEigen :
  p37T3Action Spectrum.p37EvenNonconstantMode
  ≡ Spectrum.scaleTriple (+ 1) Spectrum.p37EvenNonconstantMode
p37T3EvenEigen = refl

p37T3OddEigen :
  p37T3Action Spectrum.p37OddMode
  ≡ Spectrum.scaleTriple (-[1+ 2 ]) Spectrum.p37OddMode
p37T3OddEigen = refl

p37T5ConstantEigen :
  p37T5Action Spectrum.p37ConstantMode
  ≡ Spectrum.scaleTriple (+ 6) Spectrum.p37ConstantMode
p37T5ConstantEigen = refl

p37T5EvenEigen :
  p37T5Action Spectrum.p37EvenNonconstantMode
  ≡ Spectrum.scaleTriple (+ 0) Spectrum.p37EvenNonconstantMode
p37T5EvenEigen = refl

p37T5OddEigen :
  p37T5Action Spectrum.p37OddMode
  ≡ Spectrum.scaleTriple (-[1+ 1 ]) Spectrum.p37OddMode
p37T5OddEigen = refl

record P37SourceForcedT3T5Boundary : Set where
  field
    sourceForcedPositiveT3Constructed : Bool
    sourceForcedPositiveT3ConstructedIsTrue :
      sourceForcedPositiveT3Constructed ≡ true

    sourceForcedPositiveT5Constructed : Bool
    sourceForcedPositiveT5ConstructedIsTrue :
      sourceForcedPositiveT5Constructed ≡ true

    t3t5FrobeniusEquivarianceConstructed : Bool
    t3t5FrobeniusEquivarianceConstructedIsTrue :
      t3t5FrobeniusEquivarianceConstructed ≡ true

    lmfdbNewformEigencharactersRecovered : Bool
    lmfdbNewformEigencharactersRecoveredIsTrue :
      lmfdbNewformEigencharactersRecovered ≡ true

    independentlyReducedFromModularPolynomialsHere : Bool
    independentlyReducedFromModularPolynomialsHereIsFalse :
      independentlyReducedFromModularPolynomialsHere ≡ false

canonicalP37SourceForcedT3T5Boundary : P37SourceForcedT3T5Boundary
canonicalP37SourceForcedT3T5Boundary = record
  { sourceForcedPositiveT3Constructed = true
  ; sourceForcedPositiveT3ConstructedIsTrue = refl
  ; sourceForcedPositiveT5Constructed = true
  ; sourceForcedPositiveT5ConstructedIsTrue = refl
  ; t3t5FrobeniusEquivarianceConstructed = true
  ; t3t5FrobeniusEquivarianceConstructedIsTrue = refl
  ; lmfdbNewformEigencharactersRecovered = true
  ; lmfdbNewformEigencharactersRecoveredIsTrue = refl
  ; independentlyReducedFromModularPolynomialsHere = false
  ; independentlyReducedFromModularPolynomialsHereIsFalse = refl
  }
