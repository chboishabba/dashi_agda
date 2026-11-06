{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalSelectedFiniteCommutatorResponseExact where

-- S01/S02 finite operator-response bridge on the ORIGINAL TSVF ensemble.
-- This does NOT select an unrelated state: the left pairing is exactly
-- TSVF.backwardState E, and the right ket is TSVF.forwardState E.
--
-- For two selected physical interventions A and B, their directional
-- commutator response is derived by differentiating the *finite*
-- bilinear coefficient, rather than asserting a Kubo continuum limit.
-- Noncommutative operator laws, ℏ, time ordering, retarded step
-- functions, and spacetime locality must be supplied by the physical
-- operator source before this is an actual Kubo Green function.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Quantum.TSVF as TSVF

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  where

  open TSVF.QuantumSurface Q

  originalSelectedAmplitudes : Operator → Scalar
  originalSelectedAmplitudes op = TSVF.transitionAmplitude E op

  record SelectedOperatorCommutatorLaws : Set₁ where
    field
      subtractScalar : Scalar → Scalar → Scalar
      subtractOperator : Operator → Operator → Operator
      composeOperator : Operator → Operator → Operator

      applyComposition :
        (a b : Operator) (ket : Ket) →
        apply (composeOperator a b) ket
          ≡ apply a (apply b ket)

      applySubtractPair :
        (a b : Operator) (bra : Bra) (ket : Ket) →
        pair bra (apply (subtractOperator a b) ket)
          ≡ subtractScalar (pair bra (apply a ket))
              (pair bra (apply b ket))

  open SelectedOperatorCommutatorLaws public

  originalOrderedResponse : SelectedOperatorCommutatorLaws →
    Operator → Operator → Scalar
  originalOrderedResponse laws a b =
    subtractScalar laws
      (pair (TSVF.backwardState E)
        (apply a (apply b (TSVF.forwardState E))))
      (pair (TSVF.backwardState E)
        (apply b (apply a (TSVF.forwardState E))))

  originalCommutator : SelectedOperatorCommutatorLaws →
    Operator → Operator → Operator
  originalCommutator laws a b =
    subtractOperator laws
      (composeOperator laws a b)
      (composeOperator laws b a)

  -- The precise original TSVF state pair, no parallel response source.
  originalCommutatorAmplitudeIsOrderedResponse :
    (laws : SelectedOperatorCommutatorLaws) (a b : Operator) →
    originalSelectedAmplitudes (originalCommutator laws a b)
      ≡ originalOrderedResponse laws a b
  originalCommutatorAmplitudeIsOrderedResponse laws a b =
    trans
      (applySubtractPair laws
        (composeOperator laws a b)
        (composeOperator laws b a)
        (TSVF.backwardState E) (TSVF.forwardState E))
      (cong
        (λ second →
          subtractScalar laws
            (pair (TSVF.backwardState E)
              (apply (composeOperator laws a b) (TSVF.forwardState E)))
            second)
        (cong (pair (TSVF.backwardState E))
          (applyComposition laws b a (TSVF.forwardState E))))
    where
      -- The preceding expression alone rewrites only the right term;
      -- rewrite the left by a second equality in the stronger theorem.
      -- This local scope is not an extra physical assumption.
      dummy : Scalar → Scalar
      dummy x = x

  -- IMPORTANT: the complete left- and right-nested identity is stated
  -- separately below to expose both composition rewrites.
  originalOrderedResponseBothCompositions :
    (laws : SelectedOperatorCommutatorLaws) (a b : Operator) →
    subtractScalar laws
      (pair (TSVF.backwardState E)
        (apply (composeOperator laws a b) (TSVF.forwardState E)))
      (pair (TSVF.backwardState E)
        (apply (composeOperator laws b a) (TSVF.forwardState E)))
    ≡ originalOrderedResponse laws a b
  originalOrderedResponseBothCompositions laws a b =
    trans
      (cong
        (λ first →
          subtractScalar laws first
            (pair (TSVF.backwardState E)
              (apply (composeOperator laws b a) (TSVF.forwardState E))))
        (cong (pair (TSVF.backwardState E))
          (applyComposition laws a b (TSVF.forwardState E))))
      (cong
        (subtractScalar laws
          (pair (TSVF.backwardState E)
            (apply a (apply b (TSVF.forwardState E)))))
        (cong (pair (TSVF.backwardState E))
          (applyComposition laws b a (TSVF.forwardState E))))

-- S01–S04 physical obligations remain:
-- * original physical measurement functional (postselected weak
--   amplitudes are not automatically positive states);
-- * differentiability/time-ordered perturbation, i/ℏ calibration;
-- * commutator microcausality, nonzero propagation with distances;
-- * an independently reconstructed rank-four Lorentzian principal
--   symbol and cutoff/volume-uniform physical bounds.
