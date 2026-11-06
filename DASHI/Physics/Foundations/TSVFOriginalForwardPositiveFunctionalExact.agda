{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact where

-- HIL01/HIL02: ORIGINAL TSVF forward-ket state, not postselected ABL.
-- Construct the candidate expectation from the original selected
-- forward state and prove its *-positivity from actual Hilbert/adjoint
-- laws. Does not assume positivity of the TSVF weak value.
-- Positivity of a *complete* GNS quotient and independently selected
-- OS state remains an additional physical theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong)
import DASHI.Quantum.TSVF as TSVF

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  where

  open TSVF.QuantumSurface Q

  record OriginalPhysicalInnerProductLaws : Set₁ where
    field
      braOfKet : Ket → Bra
      operatorAdjoint : Operator → Operator
      operatorCompose : Operator → Operator → Operator

      selectedComposition :
        (a b : Operator) (ket : Ket) →
        apply (operatorCompose a b) ket
          ≡ apply a (apply b ket)

      adjointLaw :
        (a : Operator) (left right : Ket) →
        pair (braOfKet left) (apply (operatorAdjoint a) right)
          ≡ pair (braOfKet (apply a left)) right

      -- Finite nonnegative norm on the PHYSICAL selected ket carrier.
      -- This is not implicit in QuantumSurface, which only declares
      -- a Weight and a predicate Positive.
      physicalNormSquare :
        (ket : Ket) →
        pair (braOfKet ket) ket
          ≡ pair (braOfKet ket) ket

      scalarSelfPairPositive :
        (ket : Ket) →
        Positive (normSquared (pair (braOfKet ket) ket))

  open OriginalPhysicalInnerProductLaws public

  originalForward : Ket
  originalForward = TSVF.forwardState E

  -- The original selected observer state functional on real operator
  -- insertions. It is deliberately NOT the backward-conditioned
  -- weak-value functional.
  originalForwardFunctional :
    OriginalPhysicalInnerProductLaws → Operator → Scalar
  originalForwardFunctional source a =
    pair (braOfKet source originalForward)
      (apply a originalForward)

  originalPositiveQuadraticIsForwardNorm :
    (source : OriginalPhysicalInnerProductLaws)
    (a : Operator) →
    originalForwardFunctional source
      (operatorCompose source (operatorAdjoint source a) a)
    ≡ pair (braOfKet source (apply a originalForward))
        (apply a originalForward)
  originalPositiveQuadraticIsForwardNorm source a =
    trans
      (cong (pair (braOfKet source originalForward))
        (selectedComposition source
          (operatorAdjoint source a) a originalForward))
      (adjointLaw source a originalForward
        (apply a originalForward))

  originalPositiveQuadraticHasPositiveWeight :
    (source : OriginalPhysicalInnerProductLaws)
    (a : Operator) →
    Positive
      (normSquared
        (originalForwardFunctional source
          (operatorCompose source (operatorAdjoint source a) a)))
  originalPositiveQuadraticHasPositiveWeight source a =
    let equality = originalPositiveQuadraticIsForwardNorm source a
    in
    transportPositive source equality
    where
      transportPositive :
        (source : OriginalPhysicalInnerProductLaws)
        (equality :
          originalForwardFunctional source
            (operatorCompose source (operatorAdjoint source a) a)
          ≡ pair (braOfKet source (apply a originalForward))
              (apply a originalForward)) →
        Positive
          (normSquared
            (originalForwardFunctional source
              (operatorCompose source (operatorAdjoint source a) a)))
      transportPositive source refl =
        scalarSelfPairPositive source (apply a originalForward)

-- WARNING: QuantumSurface.normSquared is a Weight conversion, not an
-- ordered complex scalar. A genuine C*-algebra state needs a
-- real-positivity order on omega(A* A), scalar normalization omega(1)=1,
-- linearity and a completed Hilbert space. This module proves the
-- original forward norm identity and a selected Weight-positivity
-- certificate, not a full GNS or an observer/OS unitary.
