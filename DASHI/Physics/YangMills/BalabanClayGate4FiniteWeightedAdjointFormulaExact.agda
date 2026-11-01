module DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedAdjointFormulaExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedAdjointFubiniExact as Fubini

------------------------------------------------------------------------
-- Literal weighted adjoint entry formula.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik 140
-- (1911), 1--28. No DOI recorded.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- For fine weight p_b and coarse weight q_c, the weighted adjoint entry is
--
--   Q^*_{b,c} y = p_b^{-1} q_c (Q_{c,b})^* y.
--
-- This module derives the local weighted pairing identity from the ordinary
-- entry-adjoint identity and the scalar cancellation law.  The sibling Fubini
-- module then upgrades it to the global finite adjoint theorem.
------------------------------------------------------------------------

record WeightedAdjointEntryAlgebra
    (Input Output FineValue CoarseValue Scalar : Set) : Set₁ where
  field
    additive : Fubini.AdditiveCommutativeMonoid Scalar

    multiplyScalar : Scalar → Scalar → Scalar
    inputWeight inverseInputWeight : Input → Scalar
    outputWeight : Output → Scalar

    scaleFine : Scalar → FineValue → FineValue

    finePairing : FineValue → FineValue → Scalar
    coarsePairing : CoarseValue → CoarseValue → Scalar

    kernelEntry : Output → Input → FineValue → CoarseValue
    ordinaryAdjointEntry : Input → Output → CoarseValue → FineValue

    ordinaryEntryAdjoint : ∀ output input fine coarse →
      coarsePairing (kernelEntry output input fine) coarse
      ≡ finePairing fine (ordinaryAdjointEntry input output coarse)

    finePairingScaleRight : ∀ fine scalar value →
      finePairing fine (scaleFine scalar value)
      ≡ multiplyScalar scalar (finePairing fine value)

    weightCancellation : ∀ input output scalar →
      multiplyScalar (inputWeight input)
        (multiplyScalar (inverseInputWeight input)
          (multiplyScalar (outputWeight output) scalar))
      ≡ multiplyScalar (outputWeight output) scalar

open WeightedAdjointEntryAlgebra public

weightedAdjointEntry :
  ∀ {Input Output FineValue CoarseValue Scalar} →
  WeightedAdjointEntryAlgebra
    Input Output FineValue CoarseValue Scalar →
  Input → Output → CoarseValue → FineValue
weightedAdjointEntry algebra input output coarse =
  scaleFine algebra (inverseInputWeight algebra input)
    (scaleFine algebra (outputWeight algebra output)
      (ordinaryAdjointEntry algebra input output coarse))

primalLocalWeightedContribution :
  ∀ {Input Output FineValue CoarseValue Scalar} →
  WeightedAdjointEntryAlgebra
    Input Output FineValue CoarseValue Scalar →
  Output → Input → FineValue → CoarseValue → Scalar
primalLocalWeightedContribution algebra output input fine coarse =
  multiplyScalar algebra (outputWeight algebra output)
    (coarsePairing algebra
      (kernelEntry algebra output input fine) coarse)

adjointLocalWeightedContribution :
  ∀ {Input Output FineValue CoarseValue Scalar} →
  WeightedAdjointEntryAlgebra
    Input Output FineValue CoarseValue Scalar →
  Input → Output → FineValue → CoarseValue → Scalar
adjointLocalWeightedContribution algebra input output fine coarse =
  multiplyScalar algebra (inputWeight algebra input)
    (finePairing algebra fine
      (weightedAdjointEntry algebra input output coarse))

weightedAdjointEntryLocalIdentity :
  ∀ {Input Output FineValue CoarseValue Scalar}
    (algebra : WeightedAdjointEntryAlgebra
      Input Output FineValue CoarseValue Scalar)
    output input fine coarse →
  primalLocalWeightedContribution algebra output input fine coarse
  ≡ adjointLocalWeightedContribution algebra input output fine coarse
weightedAdjointEntryLocalIdentity algebra output input fine coarse =
  trans
    (cong (multiplyScalar algebra (outputWeight algebra output))
      (ordinaryEntryAdjoint algebra output input fine coarse))
    (sym
      (trans
        (cong (multiplyScalar algebra (inputWeight algebra input))
          (trans
            (finePairingScaleRight algebra fine
              (inverseInputWeight algebra input)
              (scaleFine algebra (outputWeight algebra output)
                (ordinaryAdjointEntry algebra input output coarse)))
            (cong
              (multiplyScalar algebra (inverseInputWeight algebra input))
              (finePairingScaleRight algebra fine
                (outputWeight algebra output)
                (ordinaryAdjointEntry algebra input output coarse)))))
        (weightCancellation algebra input output
          (finePairing algebra fine
            (ordinaryAdjointEntry algebra input output coarse)))))

asFiniteWeightedAdjointContributionData :
  ∀ {Input Output FineValue CoarseValue Scalar} →
  (inputs : List Input) → (outputs : List Output) →
  WeightedAdjointEntryAlgebra
    Input Output FineValue CoarseValue Scalar →
  Fubini.FiniteWeightedAdjointContributionData
    Input Output FineValue CoarseValue Scalar
asFiniteWeightedAdjointContributionData inputs outputs algebra = record
  { scalarAdditive = additive algebra
  ; inputs = inputs
  ; outputs = outputs
  ; primalWeightedContribution =
      primalLocalWeightedContribution algebra
  ; adjointWeightedContribution =
      adjointLocalWeightedContribution algebra
  ; localWeightedAdjointIdentity =
      weightedAdjointEntryLocalIdentity algebra
  }

weightedAdjointFormulaDefinitionLevel : ProofLevel
weightedAdjointFormulaDefinitionLevel = computed

weightedAdjointEntryLocalIdentityLevel : ProofLevel
weightedAdjointEntryLocalIdentityLevel = machineChecked

weightedAdjointFormulaToGlobalFubiniLevel : ProofLevel
weightedAdjointFormulaToGlobalFubiniLevel = machineChecked

physicalOrdinaryEntryAdjointInputsLevel : ProofLevel
physicalOrdinaryEntryAdjointInputsLevel = conditional

physicalFineCoarseWeightInvertibilityInputsLevel : ProofLevel
physicalFineCoarseWeightInvertibilityInputsLevel = conditional
