module DASHI.Physics.Closure.NSTriadKNExactFiniteComplexCauchySchwarzRound65 where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century results.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 65 / B1 SUBSTRATE REPAIR
--
-- The historical `FiniteComplexL2Laws` interface quantified over an arbitrary
-- `pairedSumSquared`.  That does not state finite Cauchy--Schwarz for the actual
-- Hermitian pairing and is too strong to instantiate in an ordinary ordered
-- real field: it asks *every* scalar to lie below the same norm product.
--
-- This module defines the literal finite Hermitian pairing over the repository's
-- exact Complex carrier, takes its literal squared modulus, and states the one
-- physically meaningful inequality
--
--   |sum_i conj(left_i) right_i|^2
--      <= (sum_i |left_i|^2) (sum_i |right_i|^2).
--
-- No rational surrogate and no unrelated real carrier are introduced.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2

finiteComplexInnerProduct :
  ∀ {i r} {Index : Set i} {F : C3.RealField r} →
  List Index →
  (Index → C3.Complex F) →
  (Index → C3.Complex F) →
  C3.Complex F
finiteComplexInnerProduct {F = F} [] left right = C3.complexZero F
finiteComplexInnerProduct {F = F} (index ∷ indices) left right =
  C3.complexAdd
    (C3.complexMultiply
      (C3.complexConjugate (left index))
      (right index))
    (finiteComplexInnerProduct indices left right)

finiteComplexInnerProductModulusSquared :
  ∀ {i r} {Index : Set i} {F : C3.RealField r} →
  List Index →
  (Index → C3.Complex F) →
  (Index → C3.Complex F) →
  C3.Carrier F
finiteComplexInnerProductModulusSquared support left right =
  L2.complexModulusSquared
    (finiteComplexInnerProduct support left right)

record ExactFiniteComplexCauchySchwarz
    {i r : Level}
    {Index : Set i}
    {F : C3.RealField r}
    (O : L2.OrderedRealExtension F)
    (support : List Index) : Set (lsuc (i ⊔ r)) where
  field
    finiteCauchySchwarz :
      ∀ left right →
      L2._≤_ O
        (finiteComplexInnerProductModulusSquared support left right)
        (C3.multiply F
          (L2.finiteComplexL2NormSquared support left)
          (L2.finiteComplexL2NormSquared support right))

open ExactFiniteComplexCauchySchwarz public

complexModulusSquaredNonnegative :
  ∀ {r} {F : C3.RealField r}
    (O : L2.OrderedRealExtension F)
    (value : C3.Complex F) →
  L2._≤_ O (C3.zero F) (L2.complexModulusSquared value)
complexModulusSquaredNonnegative {F = F} O value =
  L2.zeroBelowAdd O
    (L2.zeroBelowSquare O (C3.real value))
    (L2.zeroBelowSquare O (C3.imaginary value))

finiteComplexL2NormSquaredNonnegative :
  ∀ {i r} {Index : Set i} {F : C3.RealField r}
    (O : L2.OrderedRealExtension F)
    (support : List Index)
    (values : Index → C3.Complex F) →
  L2._≤_ O
    (C3.zero F)
    (L2.finiteComplexL2NormSquared support values)
finiteComplexL2NormSquaredNonnegative {F = F} O [] values =
  L2.leqReflexive O (C3.zero F)
finiteComplexL2NormSquaredNonnegative {F = F} O (index ∷ indices) values =
  L2.zeroBelowAdd O
    (complexModulusSquaredNonnegative O (values index))
    (finiteComplexL2NormSquaredNonnegative O indices values)

finiteComplexInnerProductMassNonnegative :
  ∀ {i r} {Index : Set i} {F : C3.RealField r}
    (O : L2.OrderedRealExtension F)
    (support : List Index)
    (left right : Index → C3.Complex F) →
  L2._≤_ O
    (C3.zero F)
    (finiteComplexInnerProductModulusSquared support left right)
finiteComplexInnerProductMassNonnegative O support left right =
  complexModulusSquaredNonnegative O
    (finiteComplexInnerProduct support left right)

round65ExactFiniteCauchySchwarzStatementConstructed : Bool
round65ExactFiniteCauchySchwarzStatementConstructed = true

round65ExactFiniteCauchySchwarzStatementConstructedIsTrue :
  round65ExactFiniteCauchySchwarzStatementConstructed ≡ true
round65ExactFiniteCauchySchwarzStatementConstructedIsTrue = refl
