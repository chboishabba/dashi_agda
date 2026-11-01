module DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Agda standard-library contributors; DASHI repository contributors.
-- Title: "Exact complex commutative-ring adapter for the periodic Fourier
-- carrier".
-- DOI: not applicable to this repository adapter.
--
-- PURPOSE
-- Complete the algebraic structure already proved componentwise in
-- NSTriadKNComplex3FieldAlgebra by packaging the literal Complex carrier as a
-- standard-library CommutativeRing.  The missing distributive laws are proved
-- by the existing non-reflective real polynomial solver.  The resulting
-- complex polynomial solver is then available to the weighted Fourier
-- integral and convolution proofs; no analytic or norm assumption is added.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Maybe.Base using (nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; trans)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra

complexAddInverseRight :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexAdd value (C3.complexNegate value) ≡ C3.complexZero F
complexAddInverseRight value =
  trans
    (Algebra.complexAddCommutative value (C3.complexNegate value))
    (Algebra.complexAddInverseLeft value)

complexMultiplyOneRight :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexMultiply value (C3.complexOne F) ≡ value
complexMultiplyOneRight {F = F} value =
  trans
    (Algebra.complexMultiplyCommutative value (C3.complexOne F))
    (Algebra.complexOneMultiply value)

complexDistributeLeft :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex F) →
  C3.complexMultiply a (C3.complexAdd b c)
  ≡ C3.complexAdd
      (C3.complexMultiply a b)
      (C3.complexMultiply a c)
complexDistributeLeft {F = F}
  (C3.complex ar ai)
  (C3.complex br bi)
  (C3.complex cr ci) =
  Algebra.complexExt
    (P.R.solve 6
      (λ ar ai br bi cr ci →
        P.multiplyReal ar ai
          (br P.R.⊕ cr) (bi P.R.⊕ ci)
        P.R.⊜
        (P.multiplyReal ar ai br bi
          P.R.⊕ P.multiplyReal ar ai cr ci))
      refl ar ai br bi cr ci)
    (P.R.solve 6
      (λ ar ai br bi cr ci →
        P.multiplyImaginary ar ai
          (br P.R.⊕ cr) (bi P.R.⊕ ci)
        P.R.⊜
        (P.multiplyImaginary ar ai br bi
          P.R.⊕ P.multiplyImaginary ar ai cr ci))
      refl ar ai br bi cr ci)
  where module P = Algebra.Polynomial F

complexDistributeRight :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex F) →
  C3.complexMultiply (C3.complexAdd a b) c
  ≡ C3.complexAdd
      (C3.complexMultiply a c)
      (C3.complexMultiply b c)
complexDistributeRight a b c =
  trans
    (Algebra.complexMultiplyCommutative (C3.complexAdd a b) c)
    (trans
      (complexDistributeLeft c a b)
      (cong₂ C3.complexAdd
        (Algebra.complexMultiplyCommutative c a)
        (Algebra.complexMultiplyCommutative c b)))

complexCommutativeRing :
  ∀ {r} (F : C3.RealField r) → CommutativeRing r r
complexCommutativeRing F = record
  { Carrier = C3.Complex F
  ; _≈_ = _≡_
  ; _+_ = C3.complexAdd
  ; _*_ = C3.complexMultiply
  ; -_ = C3.complexNegate
  ; 0# = C3.complexZero F
  ; 1# = C3.complexOne F
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence
                ; ∙-cong = cong₂ C3.complexAdd
                }
              ; assoc = Algebra.complexAddAssociative
              }
            ; identity =
                Algebra.complexAddZeroLeft , Algebra.complexAddZeroRight
            }
          ; inverse =
              Algebra.complexAddInverseLeft , complexAddInverseRight
          ; ⁻¹-cong = cong C3.complexNegate
          }
        ; comm = Algebra.complexAddCommutative
        }
      ; *-cong = cong₂ C3.complexMultiply
      ; *-assoc = Algebra.complexMultiplyAssociative
      ; *-identity = Algebra.complexOneMultiply , complexMultiplyOneRight
      ; distrib = complexDistributeRight , complexDistributeLeft
      }
    ; *-comm = Algebra.complexMultiplyCommutative
    }
  }

private
  solverRing :
    ∀ {r} (F : C3.RealField r) →
    RingCore.AlmostCommutativeRing r r
  solverRing F =
    RingCore.fromCommutativeRing
      (complexCommutativeRing F)
      (λ _ → nothing)

module Solver {r : Level} (F : C3.RealField r) =
  RingSolver (solverRing F)

complexCommutativeRingClosed : Bool
complexCommutativeRingClosed = true

complexPolynomialSolverConstructed : Bool
complexPolynomialSolverConstructed = true

complexCommutativeRingClosedIsTrue :
  complexCommutativeRingClosed ≡ true
complexCommutativeRingClosedIsTrue = refl

complexPolynomialSolverConstructedIsTrue :
  complexPolynomialSolverConstructed ≡ true
complexPolynomialSolverConstructedIsTrue = refl
