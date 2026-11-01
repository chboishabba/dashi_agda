module DASHI.Physics.Closure.NSTriadKNFiniteTriadCancellationAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNExactRingSolverBridge as Ring

------------------------------------------------------------------------
-- The six-term algebra behind Fourier triad energy conservation.
--
-- After the Leray projector is removed against a divergence-free output,
-- one geometric triad contributes the six ordered convection terms
--
--   (q·uₚ)<u_q,u_r> + (p·u_q)<u_p,u_r>
-- + (r·u_q)<u_r,u_p> + (q·u_r)<u_q,u_p>
-- + (p·u_r)<u_p,u_q> + (r·uₚ)<u_r,u_q>.
--
-- Symmetry of the vector pairing reduces this to the polynomial below.
-- This file proves the cancellation from *three separate* ingredients:
-- zero-sum wavevector coefficients and the three divergence-free equations.
-- It deliberately does not contain a conservation field or a modal-transfer
-- axiom.
--
-- For a diagonal input orbit p = q, the cutoff quotient retains only one
-- self-input occurrence rather than two.  The missing duplicate has factor
-- p·uₚ and is therefore zero once the concrete Fourier bridge proves the
-- diagonal divergence-free reduction.  That reduction remains a distinct
-- lemma: this six-term theorem is the off-diagonal normal form and must not
-- be applied to a diagonal orbit without that zero-term transport.
------------------------------------------------------------------------

private
  SOf : Algebra.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Algebra.orderedScalar K)

sixTermConvectionNumerator :
  (K : Algebra.ExactOrderedCommutativeRing) →
  SOf K → SOf K → SOf K →
  SOf K → SOf K → SOf K →
  SOf K → SOf K → SOf K →
  SOf K → SOf K → SOf K →
  SOf K
sixTermConvectionNumerator K pA qA rA pB qB rB pC qC rC
  pairAB pairAC pairBC =
  Scalar._+_ S
    (Scalar._+_ S
      (Scalar._*_ S qA pairBC)
      (Scalar._*_ S pB pairAC))
    (Scalar._+_ S
      (Scalar._+_ S
        (Scalar._*_ S rB pairAC)
        (Scalar._*_ S qC pairAB))
      (Scalar._+_ S
        (Scalar._*_ S pC pairAB)
        (Scalar._*_ S rA pairBC)))
  where
  S = Algebra.orderedScalar K

-- A zero-sum wavevector, evaluated against a fixed vector, supplies this
-- relation.  The concrete Fourier bridge will obtain the three instances
-- from `p + q + r = 0`; the diagonal divergence equations set pA, qB, and
-- rC to zero respectively.
record SixTermTriadRelations
    (K : Algebra.ExactOrderedCommutativeRing)
    (pA qA rA pB qB rB pC qC rC : SOf K) : Set where
  field
    sumAgainstA :
      Scalar._+_ (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K) pA qA) rA ≡
      Scalar.zero (Algebra.orderedScalar K)
    sumAgainstB :
      Scalar._+_ (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K) pB qB) rB ≡
      Scalar.zero (Algebra.orderedScalar K)
    sumAgainstC :
      Scalar._+_ (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K) pC qC) rC ≡
      Scalar.zero (Algebra.orderedScalar K)

    pDivergenceFree : pA ≡ Scalar.zero (Algebra.orderedScalar K)
    qDivergenceFree : qB ≡ Scalar.zero (Algebra.orderedScalar K)
    rDivergenceFree : rC ≡ Scalar.zero (Algebra.orderedScalar K)

open SixTermTriadRelations public

sumOfOtherTwoZero :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (a b c : SOf K) →
  a ≡ Scalar.zero (Algebra.orderedScalar K) →
  Scalar._+_ (Algebra.orderedScalar K)
    (Scalar._+_ (Algebra.orderedScalar K) a b) c ≡
  Scalar.zero (Algebra.orderedScalar K) →
  Scalar._+_ (Algebra.orderedScalar K) b c ≡
  Scalar.zero (Algebra.orderedScalar K)
sumOfOtherTwoZero K a b c aZero total =
  trans
    (sym (Algebra.addZeroLeft K (Scalar._+_ S b c)))
    (trans
      (sym (Algebra.addAssociative K (Scalar.zero S) b c))
      (trans
        (cong (λ x → Scalar._+_ S (Scalar._+_ S x b) c) (sym aZero))
        total))
  where
  S = Algebra.orderedScalar K

sixTermConvectionCancellation :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (pA qA rA pB qB rB pC qC rC : SOf K) →
  (pairAB pairAC pairBC : SOf K) →
  SixTermTriadRelations K pA qA rA pB qB rB pC qC rC →
  sixTermConvectionNumerator K pA qA rA pB qB rB pC qC rC
    pairAB pairAC pairBC ≡ Scalar.zero (Algebra.orderedScalar K)
sixTermConvectionCancellation K pA qA rA pB qB rB pC qC rC
  pairAB pairAC pairBC Rels =
  trans grouped (trans zeroFactors finalZero)
  where
  S = Algebra.orderedScalar K
  module Solver = Ring.Solver K

  qA+rA : Scalar._+_ S qA rA ≡ Scalar.zero S
  qA+rA = sumOfOtherTwoZero K pA qA rA
    (pDivergenceFree Rels) (sumAgainstA Rels)

  pB+rB : Scalar._+_ S pB rB ≡ Scalar.zero S
  pB+rB = sumOfOtherTwoZero K qB pB rB
    (qDivergenceFree Rels)
    (trans
      (cong (λ x → Scalar._+_ S x rB)
        (sym (Algebra.addCommutative K pB qB)))
      (sumAgainstB Rels))

  qC+pC : Scalar._+_ S qC pC ≡ Scalar.zero S
  qC+pC = trans
    (Algebra.addCommutative K qC pC)
    (trans
      (sym (Algebra.addZeroRight K (Scalar._+_ S pC qC)))
      (trans
        (cong (λ x → Scalar._+_ S (Scalar._+_ S pC qC) x)
          (sym (rDivergenceFree Rels)))
        (sumAgainstC Rels)))

  grouped :
    sixTermConvectionNumerator K pA qA rA pB qB rB pC qC rC
      pairAB pairAC pairBC ≡
    Scalar._+_ S
      (Scalar._+_ S
        (Scalar._*_ S (Scalar._+_ S qA rA) pairBC)
        (Scalar._*_ S (Scalar._+_ S pB rB) pairAC))
      (Scalar._*_ S (Scalar._+_ S qC pC) pairAB)
  grouped = Solver.solve 12
    (λ pA qA rA pB qB rB pC qC rC pairAB pairAC pairBC →
      ( (qA Solver.⊗ pairBC Solver.⊕ pB Solver.⊗ pairAC)
          Solver.⊕ ((rB Solver.⊗ pairAC Solver.⊕ qC Solver.⊗ pairAB)
          Solver.⊕ (pC Solver.⊗ pairAB Solver.⊕ rA Solver.⊗ pairBC))
      , ( (qA Solver.⊕ rA) Solver.⊗ pairBC
          Solver.⊕ ((pB Solver.⊕ rB) Solver.⊗ pairAC)
          Solver.⊕ ((qC Solver.⊕ pC) Solver.⊗ pairAB))))
    refl pA qA rA pB qB rB pC qC rC pairAB pairAC pairBC

  zeroFactors :
    Scalar._+_ S
      (Scalar._+_ S
        (Scalar._*_ S (Scalar._+_ S qA rA) pairBC)
        (Scalar._*_ S (Scalar._+_ S pB rB) pairAC))
      (Scalar._*_ S (Scalar._+_ S qC pC) pairAB) ≡
    Scalar._+_ S
      (Scalar._+_ S (Scalar._*_ S (Scalar.zero S) pairBC)
        (Scalar._*_ S (Scalar.zero S) pairAC))
      (Scalar._*_ S (Scalar.zero S) pairAB)
  zeroFactors = cong₂ (Scalar._+_ S)
    (cong₂ (Scalar._+_ S)
      (cong (λ x → Scalar._*_ S x pairBC) qA+rA)
      (cong (λ x → Scalar._*_ S x pairAC) pB+rB))
    (cong (λ x → Scalar._*_ S x pairAB) qC+pC)

  finalZero :
    Scalar._+_ S
      (Scalar._+_ S (Scalar._*_ S (Scalar.zero S) pairBC)
        (Scalar._*_ S (Scalar.zero S) pairAC))
      (Scalar._*_ S (Scalar.zero S) pairAB) ≡ Scalar.zero S
  finalZero =
    trans
      (cong₂ (Scalar._+_ S)
        (cong₂ (Scalar._+_ S)
          (Algebra.mulZeroLeft K pairBC)
          (Algebra.mulZeroLeft K pairAC))
        (Algebra.mulZeroLeft K pairAB))
      (trans
        (cong (λ x → Scalar._+_ S x (Scalar.zero S))
          (Algebra.addZeroLeft K (Scalar.zero S)))
        (Algebra.addZeroLeft K (Scalar.zero S)))
