module DASHI.Physics.Closure.NSTriadKNConcreteWeightedSchurDecay where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (_≤_; _*_; _+_; z≤n)
open import Data.Nat.Properties using
  ( ≤-reflexive
  ; ≤-refl
  ; ≤-trans
  ; +-mono-≤
  ; *-mono-≤
  ; *-suc
  )
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNBipartiteWeightedSchurWitness as Schur
import DASHI.Physics.Closure.NSTriadKNConcreteClassifierCorrection as CorrectedClassifier
import DASHI.Physics.Closure.NSTriadKNConcreteCorrectedRefinement as CorrectedRefinement
import DASHI.Physics.Closure.NSTriadKNConcreteWeightedFiberFolds as Folds
import DASHI.Physics.Closure.NSTriadKNConcreteIndexClassifierBridge as ConcreteBridge
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailType
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialType
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionType
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel

------------------------------------------------------------------------
-- Finite weighted sums.
--
-- This is the only generic estimate used below.  It says that a finite
-- fiber whose entries are pointwise bounded by b has total mass at most
-- b times the size of the fiber.  No analytic kernel estimate is hidden in
-- this lemma.
------------------------------------------------------------------------

sumFinUpperBound :
  {n : Nat} ->
  (f : Fin n -> Nat) ->
  (bound : Nat) ->
  ((i : Fin n) -> f i ≤ bound) ->
  Schur.sumFin f ≤ bound * n
sumFinUpperBound {n = zero} f bound pointwise = z≤n
sumFinUpperBound {n = suc n} f bound pointwise =
  ≤-trans
    (+-mono-≤
      (pointwise fzero)
      (sumFinUpperBound
        (λ i -> f (fsuc i))
        bound
        (λ i -> pointwise (fsuc i))))
    (≤-reflexive (sym (*-suc bound n)))

sumFinMulUpperBound :
  {n : Nat} ->
  (factor : Nat) ->
  (f : Fin n -> Nat) ->
  (bound : Nat) ->
  ((i : Fin n) -> f i ≤ bound) ->
  Schur.sumFin (λ i -> factor * f i) ≤ factor * (bound * n)
sumFinMulUpperBound factor f bound pointwise =
  ≤-trans
    (≤-reflexive (Folds.sumFinMulLeft factor f))
    (*-mono-≤
      (≤-refl {factor})
      (sumFinUpperBound f bound pointwise))

------------------------------------------------------------------------
-- Concrete geometric weights and the two lifted orientation inequalities.
-- The classifier-incidence premises remain explicit inputs: the tagged Fin
-- constructors alone do not prove that a given pair lands in the required
-- depth-separation class.

concreteSourceWeight :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
concreteSourceWeight f = WeightModel.weightOf (ConcreteBridge.sourceEntryCode f)

concreteTargetWeight :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
concreteTargetWeight t = WeightModel.weightOf (ConcreteBridge.targetEntryCode t)

concreteFTToAdversarialWeightOrientation :
  {N : Nat} ->
  ConcreteBridge.ConcreteFTToAdversarialPremise N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialType.AdversarialTail d N) ->
  suc N * concreteTargetWeight
    (Relation.adversarialTailIndex d t)
    ≤ concreteSourceWeight
      (Relation.forcedTailFiniteIndex c h)
concreteFTToAdversarialWeightOrientation {N = N} premise c h d t =
  WeightModel.ftAdvWeightSeparation
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h))
    (ConcreteBridge.targetEntryCode
      (Relation.adversarialTailIndex d t))
    (premise c h d t)

concreteFTToTransitionWeightOrientation :
  {N : Nat} ->
  ConcreteBridge.ConcreteFTToTransitionPremise N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionType.TransitionTail d N) ->
  suc N * concreteTargetWeight
    (Relation.transitionTailIndex d t)
    ≤ concreteSourceWeight
      (Relation.forcedTailFiniteIndex c h)
concreteFTToTransitionWeightOrientation {N = N} premise c h d t =
  WeightModel.ftTransWeightSeparation
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h))
    (ConcreteBridge.targetEntryCode
      (Relation.transitionTailIndex d t))
    (premise c h d t)

correctedConcreteFTToAdversarialWeightOrientation :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialType.AdversarialTail d N) ->
  WeightModel.ForcedTailSource
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h)) ->
  WeightModel.AdversarialTarget
    N
    (ConcreteBridge.targetEntryCode
      (Relation.adversarialTailIndex d t)) ->
  suc N * concreteTargetWeight (Relation.adversarialTailIndex d t) ≤
    concreteSourceWeight (Relation.forcedTailFiniteIndex c h)
correctedConcreteFTToAdversarialWeightOrientation {N = N} c h d t source target =
  CorrectedClassifier.correctedFTToAdversarialWeightSeparation
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h))
    (ConcreteBridge.targetEntryCode
      (Relation.adversarialTailIndex d t))
    source
    target

correctedConcreteFTToTransitionWeightOrientation :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionType.TransitionTail d N) ->
  WeightModel.ForcedTailSource
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h)) ->
  WeightModel.TransitionTarget
    N
    (ConcreteBridge.targetEntryCode
      (Relation.transitionTailIndex d t)) ->
  suc N * concreteTargetWeight (Relation.transitionTailIndex d t) ≤
    concreteSourceWeight (Relation.forcedTailFiniteIndex c h)
correctedConcreteFTToTransitionWeightOrientation {N = N} c h d t source target =
  CorrectedClassifier.correctedFTToTransitionWeightSeparation
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h))
    (ConcreteBridge.targetEntryCode
      (Relation.transitionTailIndex d t))
    source
    target

correctedConcreteFTToAdversarialWeightOrientationFromIncidence :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  {h : ForcedTailType.ForcedTailHead c N} ->
  {d : Adversarial.AdversarialClass} ->
  {t : AdversarialType.AdversarialTail d N} ->
  CorrectedRefinement.CorrectedFTToAdversarialIncidence N c h d t ->
  suc N * concreteTargetWeight (Relation.adversarialTailIndex d t) ≤
    concreteSourceWeight (Relation.forcedTailFiniteIndex c h)
correctedConcreteFTToAdversarialWeightOrientationFromIncidence inc =
  CorrectedRefinement.correctedFTToAdversarialWeightOrientationFromIncidence inc

correctedConcreteFTToTransitionWeightOrientationFromIncidence :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  {h : ForcedTailType.ForcedTailHead c N} ->
  {d : Transition.TransitionClass} ->
  {t : TransitionType.TransitionTail d N} ->
  CorrectedRefinement.CorrectedFTToTransitionIncidence N c h d t ->
  suc N * concreteTargetWeight (Relation.transitionTailIndex d t) ≤
    concreteSourceWeight (Relation.forcedTailFiniteIndex c h)
correctedConcreteFTToTransitionWeightOrientationFromIncidence inc =
  CorrectedRefinement.correctedFTToTransitionWeightOrientationFromIncidence inc

------------------------------------------------------------------------
-- Cross-profile blocks.
--
-- The concrete relation has six mixed-family blocks.  Their kernel counts
-- reduce definitionally to zero.  Multiplying by an arbitrary target or
-- source weight preserves that zero, so these are genuine weighted bounds,
-- not unit-weight special cases.
------------------------------------------------------------------------

forcedTailRowAdversarialCrossZero :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : ForcedTail.ForcedTailClass) ->
  (d : Adversarial.AdversarialClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.forcedTailFiniteIndex c h)
        (Relation.adversarialTailIndex d i) *
      targetWeight (Relation.adversarialTailIndex d i))
    ≡ 0
forcedTailRowAdversarialCrossZero targetWeight c d h =
  trans
    (Folds.sumFinCong
      (λ i ->
        cong
          (λ k -> k * targetWeight (Relation.adversarialTailIndex d i))
          (Folds.forcedTailAdversarialCountZero c d h i)))
    (Folds.weightedZeroBlock
      0
      refl
      (λ i -> targetWeight (Relation.adversarialTailIndex d i)))

forcedTailRowAdversarialCrossZeroBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : ForcedTail.ForcedTailClass) ->
  (d : Adversarial.AdversarialClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.forcedTailFiniteIndex c h)
        (Relation.adversarialTailIndex d i) *
      targetWeight (Relation.adversarialTailIndex d i))
    ≤ 0
forcedTailRowAdversarialCrossZeroBound targetWeight c d h =
  ≤-reflexive (forcedTailRowAdversarialCrossZero targetWeight c d h)

forcedTailRowTransitionCrossZero :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : ForcedTail.ForcedTailClass) ->
  (d : Transition.TransitionClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.forcedTailFiniteIndex c h)
        (Relation.transitionTailIndex d i) *
      targetWeight (Relation.transitionTailIndex d i))
    ≡ 0
forcedTailRowTransitionCrossZero targetWeight c d h =
  trans
    (Folds.sumFinCong
      (λ i ->
        cong
          (λ k -> k * targetWeight (Relation.transitionTailIndex d i))
          (Folds.forcedTailTransitionCountZero c d h i)))
    (Folds.weightedZeroBlock
      0
      refl
      (λ i -> targetWeight (Relation.transitionTailIndex d i)))

forcedTailRowTransitionCrossZeroBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : ForcedTail.ForcedTailClass) ->
  (d : Transition.TransitionClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.forcedTailFiniteIndex c h)
        (Relation.transitionTailIndex d i) *
      targetWeight (Relation.transitionTailIndex d i))
    ≤ 0
forcedTailRowTransitionCrossZeroBound targetWeight c d h =
  ≤-reflexive (forcedTailRowTransitionCrossZero targetWeight c d h)

adversarialRowForcedTailCrossZero :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Adversarial.AdversarialClass) ->
  (d : ForcedTail.ForcedTailClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.adversarialFiniteIndex c h)
        (Relation.forcedTailTailIndex d i) *
      targetWeight (Relation.forcedTailTailIndex d i))
    ≡ 0
adversarialRowForcedTailCrossZero targetWeight c d h =
  trans
    (Folds.sumFinCong
      (λ i ->
        cong
          (λ k -> k * targetWeight (Relation.forcedTailTailIndex d i))
          (Folds.adversarialForcedTailCountZero c d h i)))
    (Folds.weightedZeroBlock
      0
      refl
      (λ i -> targetWeight (Relation.forcedTailTailIndex d i)))

adversarialRowForcedTailCrossZeroBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Adversarial.AdversarialClass) ->
  (d : ForcedTail.ForcedTailClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.adversarialFiniteIndex c h)
        (Relation.forcedTailTailIndex d i) *
      targetWeight (Relation.forcedTailTailIndex d i))
    ≤ 0
adversarialRowForcedTailCrossZeroBound targetWeight c d h =
  ≤-reflexive (adversarialRowForcedTailCrossZero targetWeight c d h)

adversarialRowTransitionCrossZero :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Adversarial.AdversarialClass) ->
  (d : Transition.TransitionClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.adversarialFiniteIndex c h)
        (Relation.transitionTailIndex d i) *
      targetWeight (Relation.transitionTailIndex d i))
    ≡ 0
adversarialRowTransitionCrossZero targetWeight c d h =
  trans
    (Folds.sumFinCong
      (λ i ->
        cong
          (λ k -> k * targetWeight (Relation.transitionTailIndex d i))
          (Folds.adversarialTransitionCountZero c d h i)))
    (Folds.weightedZeroBlock
      0
      refl
      (λ i -> targetWeight (Relation.transitionTailIndex d i)))

adversarialRowTransitionCrossZeroBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Adversarial.AdversarialClass) ->
  (d : Transition.TransitionClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.adversarialFiniteIndex c h)
        (Relation.transitionTailIndex d i) *
      targetWeight (Relation.transitionTailIndex d i))
    ≤ 0
adversarialRowTransitionCrossZeroBound targetWeight c d h =
  ≤-reflexive (adversarialRowTransitionCrossZero targetWeight c d h)

transitionRowForcedTailCrossZero :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Transition.TransitionClass) ->
  (d : ForcedTail.ForcedTailClass) ->
  (h : TransitionType.TransitionHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.transitionFiniteIndex c h)
        (Relation.forcedTailTailIndex d i) *
      targetWeight (Relation.forcedTailTailIndex d i))
    ≡ 0
transitionRowForcedTailCrossZero targetWeight c d h =
  trans
    (Folds.sumFinCong
      (λ i ->
        cong
          (λ k -> k * targetWeight (Relation.forcedTailTailIndex d i))
          (Folds.transitionForcedTailCountZero c d h i)))
    (Folds.weightedZeroBlock
      0
      refl
      (λ i -> targetWeight (Relation.forcedTailTailIndex d i)))

transitionRowForcedTailCrossZeroBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Transition.TransitionClass) ->
  (d : ForcedTail.ForcedTailClass) ->
  (h : TransitionType.TransitionHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.transitionFiniteIndex c h)
        (Relation.forcedTailTailIndex d i) *
      targetWeight (Relation.forcedTailTailIndex d i))
    ≤ 0
transitionRowForcedTailCrossZeroBound targetWeight c d h =
  ≤-reflexive (transitionRowForcedTailCrossZero targetWeight c d h)

transitionRowAdversarialCrossZero :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Transition.TransitionClass) ->
  (d : Adversarial.AdversarialClass) ->
  (h : TransitionType.TransitionHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.transitionFiniteIndex c h)
        (Relation.adversarialTailIndex d i) *
      targetWeight (Relation.adversarialTailIndex d i))
    ≡ 0
transitionRowAdversarialCrossZero targetWeight c d h =
  trans
    (Folds.sumFinCong
      (λ i ->
        cong
          (λ k -> k * targetWeight (Relation.adversarialTailIndex d i))
          (Folds.transitionAdversarialCountZero c d h i)))
    (Folds.weightedZeroBlock
      0
      refl
      (λ i -> targetWeight (Relation.adversarialTailIndex d i)))

transitionRowAdversarialCrossZeroBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Transition.TransitionClass) ->
  (d : Adversarial.AdversarialClass) ->
  (h : TransitionType.TransitionHead c N) ->
  Schur.sumFin
    (λ i ->
      Relation.concreteNonResidualPairIncidenceCount
        (Relation.transitionFiniteIndex c h)
        (Relation.adversarialTailIndex d i) *
      targetWeight (Relation.adversarialTailIndex d i))
    ≤ 0
transitionRowAdversarialCrossZeroBound targetWeight c d h =
  ≤-reflexive (transitionRowAdversarialCrossZero targetWeight c d h)

------------------------------------------------------------------------
-- Same-class diagonal blocks.
--
-- These bounds are constructive but deliberately conditional on the exact
-- pointwise weight ceiling on the concrete fiber.  They use the concrete
-- class cardinality formulas and expose, rather than assume, the missing
-- decay estimate.
------------------------------------------------------------------------

forcedTailRowDiagonalBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c d : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (bound : Nat) ->
  ((i : ForcedTailType.ForcedTailTail d N) ->
    targetWeight (Relation.forcedTailTailIndex d i) ≤ bound) ->
  Schur.sumFin
    (λ i ->
      Relation.forcedTailPairIncidenceCount c d *
      targetWeight (Relation.forcedTailTailIndex d i))
    ≤ Relation.forcedTailPairIncidenceCount c d *
      (bound * ForcedTail.forcedTailTailCountBound d N)
forcedTailRowDiagonalBound targetWeight c d h bound pointwise =
  sumFinMulUpperBound
    (Relation.forcedTailPairIncidenceCount c d)
    (λ i -> targetWeight (Relation.forcedTailTailIndex d i))
    bound
    pointwise

adversarialRowDiagonalBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c d : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  (bound : Nat) ->
  ((i : AdversarialType.AdversarialTail d N) ->
    targetWeight (Relation.adversarialTailIndex d i) ≤ bound) ->
  Schur.sumFin
    (λ i ->
      Relation.adversarialPairIncidenceCount c d *
      targetWeight (Relation.adversarialTailIndex d i))
    ≤ Relation.adversarialPairIncidenceCount c d *
      (bound * Adversarial.adversarialColumnCountBound d N)
adversarialRowDiagonalBound targetWeight c d h bound pointwise =
  sumFinMulUpperBound
    (Relation.adversarialPairIncidenceCount c d)
    (λ i -> targetWeight (Relation.adversarialTailIndex d i))
    bound
    pointwise

transitionRowDiagonalBound :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c d : Transition.TransitionClass) ->
  (h : TransitionType.TransitionHead c N) ->
  (bound : Nat) ->
  ((i : TransitionType.TransitionTail d N) ->
    targetWeight (Relation.transitionTailIndex d i) ≤ bound) ->
  Schur.sumFin
    (λ i ->
      Relation.transitionPairIncidenceCount c d *
      targetWeight (Relation.transitionTailIndex d i))
    ≤ Relation.transitionPairIncidenceCount c d *
      (bound * Transition.transitionColumnCountBound d N)
transitionRowDiagonalBound targetWeight c d h bound pointwise =
  sumFinMulUpperBound
    (Relation.transitionPairIncidenceCount c d)
    (λ i -> targetWeight (Relation.transitionTailIndex d i))
    bound
    pointwise

------------------------------------------------------------------------
-- Full proxy-fold row decay.
--
-- The preceding diagonal lemmas bound one surviving class block.  The
-- weighted candidate normal form proves that every other block in the
-- concrete proxy fold is definitionally zero, so the same estimate lifts to
-- the actual folded row sum.  The ceiling is deliberately explicit: it is a
-- weight inequality, not a retained-triad or physical-support assumption.
------------------------------------------------------------------------

forcedTailWeightedRowDecayFromCeiling :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (bound : Nat) ->
  ((i : ForcedTailType.ForcedTailTail c N) ->
    targetWeight (Relation.forcedTailTailIndex c i) ≤ bound) ->
  Folds.weightedConcreteRowSum targetWeight
    (Relation.forcedTailFiniteIndex c h) ≤
  Relation.forcedTailPairIncidenceCount c c *
    (bound * ForcedTail.forcedTailTailCountBound c N)
forcedTailWeightedRowDecayFromCeiling targetWeight c h bound ceiling =
  ≤-trans
    (≤-reflexive
      (trans
        (Folds.weightedConcreteRowSumNormalForm
          targetWeight
          (Relation.forcedTailFiniteIndex c h))
        (trans
          (Folds.weightedRowCandidateNormalFormProof
            targetWeight
            (Relation.forcedTailFiniteIndex c h))
          (sym
            (Folds.weightedForcedTailRowBlock
              targetWeight
              c
              c
              h)))))
    (forcedTailRowDiagonalBound
      targetWeight
      c
      c
      h
      bound
      ceiling)

adversarialWeightedRowDecayFromCeiling :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  (bound : Nat) ->
  ((i : AdversarialType.AdversarialTail c N) ->
    targetWeight (Relation.adversarialTailIndex c i) ≤ bound) ->
  Folds.weightedConcreteRowSum targetWeight
    (Relation.adversarialFiniteIndex c h) ≤
  Relation.adversarialPairIncidenceCount c c *
    (bound * Adversarial.adversarialColumnCountBound c N)
adversarialWeightedRowDecayFromCeiling targetWeight c h bound ceiling =
  ≤-trans
    (≤-reflexive
      (trans
        (Folds.weightedConcreteRowSumNormalForm
          targetWeight
          (Relation.adversarialFiniteIndex c h))
        (trans
          (Folds.weightedRowCandidateNormalFormProof
            targetWeight
            (Relation.adversarialFiniteIndex c h))
          (sym
            (Folds.weightedAdversarialRowBlock
              targetWeight
              c
              c
              h)))))
    (adversarialRowDiagonalBound
      targetWeight
      c
      c
      h
      bound
      ceiling)

transitionWeightedRowDecayFromCeiling :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c : Transition.TransitionClass) ->
  (h : TransitionType.TransitionHead c N) ->
  (bound : Nat) ->
  ((i : TransitionType.TransitionTail c N) ->
    targetWeight (Relation.transitionTailIndex c i) ≤ bound) ->
  Folds.weightedConcreteRowSum targetWeight
    (Relation.transitionFiniteIndex c h) ≤
  Relation.transitionPairIncidenceCount c c *
    (bound * Transition.transitionColumnCountBound c N)
transitionWeightedRowDecayFromCeiling targetWeight c h bound ceiling =
  ≤-trans
    (≤-reflexive
      (trans
        (Folds.weightedConcreteRowSumNormalForm
          targetWeight
          (Relation.transitionFiniteIndex c h))
        (trans
          (Folds.weightedRowCandidateNormalFormProof
            targetWeight
            (Relation.transitionFiniteIndex c h))
          (sym
            (Folds.weightedTransitionRowBlock
              targetWeight
              c
              c
              h)))))
    (transitionRowDiagonalBound
      targetWeight
      c
      c
      h
      bound
      ceiling)

------------------------------------------------------------------------
-- Column-oriented diagonal blocks.
------------------------------------------------------------------------

forcedTailColumnDiagonalBound :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c d : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailTail c N) ->
  (bound : Nat) ->
  ((i : ForcedTailType.ForcedTailHead d N) ->
    sourceWeight (Relation.forcedTailFiniteIndex d i) ≤ bound) ->
  Schur.sumFin
    (λ i ->
      Relation.forcedTailPairIncidenceCount d c *
      sourceWeight (Relation.forcedTailFiniteIndex d i))
    ≤ Relation.forcedTailPairIncidenceCount d c *
      (bound * ForcedTail.forcedTailHeadCountBound d N)
forcedTailColumnDiagonalBound sourceWeight c d h bound pointwise =
  sumFinMulUpperBound
    (Relation.forcedTailPairIncidenceCount d c)
    (λ i -> sourceWeight (Relation.forcedTailFiniteIndex d i))
    bound
    pointwise

adversarialColumnDiagonalBound :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c d : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialTail c N) ->
  (bound : Nat) ->
  ((i : AdversarialType.AdversarialHead d N) ->
    sourceWeight (Relation.adversarialFiniteIndex d i) ≤ bound) ->
  Schur.sumFin
    (λ i ->
      Relation.adversarialPairIncidenceCount d c *
      sourceWeight (Relation.adversarialFiniteIndex d i))
    ≤ Relation.adversarialPairIncidenceCount d c *
      (bound * Adversarial.adversarialRowCountBound d N)
adversarialColumnDiagonalBound sourceWeight c d h bound pointwise =
  sumFinMulUpperBound
    (Relation.adversarialPairIncidenceCount d c)
    (λ i -> sourceWeight (Relation.adversarialFiniteIndex d i))
    bound
    pointwise

transitionColumnDiagonalBound :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c d : Transition.TransitionClass) ->
  (h : TransitionType.TransitionTail c N) ->
  (bound : Nat) ->
  ((i : TransitionType.TransitionHead d N) ->
    sourceWeight (Relation.transitionFiniteIndex d i) ≤ bound) ->
  Schur.sumFin
    (λ i ->
      Relation.transitionPairIncidenceCount d c *
      sourceWeight (Relation.transitionFiniteIndex d i))
    ≤ Relation.transitionPairIncidenceCount d c *
      (bound * Transition.transitionRowCountBound d N)
transitionColumnDiagonalBound sourceWeight c d h bound pointwise =
  sumFinMulUpperBound
    (Relation.transitionPairIncidenceCount d c)
    (λ i -> sourceWeight (Relation.transitionFiniteIndex d i))
    bound
    pointwise

------------------------------------------------------------------------
-- Full proxy-fold column decay, dual to the row lemmas above.
------------------------------------------------------------------------

forcedTailWeightedColumnDecayFromCeiling :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailTail c N) ->
  (bound : Nat) ->
  ((i : ForcedTailType.ForcedTailHead c N) ->
    sourceWeight (Relation.forcedTailFiniteIndex c i) ≤ bound) ->
  Folds.weightedConcreteColumnSum sourceWeight
    (Relation.forcedTailTailIndex c h) ≤
  Relation.forcedTailPairIncidenceCount c c *
    (bound * ForcedTail.forcedTailHeadCountBound c N)
forcedTailWeightedColumnDecayFromCeiling sourceWeight c h bound ceiling =
  ≤-trans
    (≤-reflexive
      (trans
        (Folds.weightedConcreteColumnSumNormalForm
          sourceWeight
          (Relation.forcedTailTailIndex c h))
        (trans
          (Folds.weightedColumnCandidateNormalFormProof
            sourceWeight
            (Relation.forcedTailTailIndex c h))
          (sym
            (Folds.weightedForcedTailColumnBlock
              sourceWeight
              c
              c
              h)))))
    (forcedTailColumnDiagonalBound
      sourceWeight
      c
      c
      h
      bound
      ceiling)

adversarialWeightedColumnDecayFromCeiling :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialTail c N) ->
  (bound : Nat) ->
  ((i : AdversarialType.AdversarialHead c N) ->
    sourceWeight (Relation.adversarialFiniteIndex c i) ≤ bound) ->
  Folds.weightedConcreteColumnSum sourceWeight
    (Relation.adversarialTailIndex c h) ≤
  Relation.adversarialPairIncidenceCount c c *
    (bound * Adversarial.adversarialRowCountBound c N)
adversarialWeightedColumnDecayFromCeiling sourceWeight c h bound ceiling =
  ≤-trans
    (≤-reflexive
      (trans
        (Folds.weightedConcreteColumnSumNormalForm
          sourceWeight
          (Relation.adversarialTailIndex c h))
        (trans
          (Folds.weightedColumnCandidateNormalFormProof
            sourceWeight
            (Relation.adversarialTailIndex c h))
          (sym
            (Folds.weightedAdversarialColumnBlock
              sourceWeight
              c
              c
              h)))))
    (adversarialColumnDiagonalBound
      sourceWeight
      c
      c
      h
      bound
      ceiling)

transitionWeightedColumnDecayFromCeiling :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c : Transition.TransitionClass) ->
  (h : TransitionType.TransitionTail c N) ->
  (bound : Nat) ->
  ((i : TransitionType.TransitionHead c N) ->
    sourceWeight (Relation.transitionFiniteIndex c i) ≤ bound) ->
  Folds.weightedConcreteColumnSum sourceWeight
    (Relation.transitionTailIndex c h) ≤
  Relation.transitionPairIncidenceCount c c *
    (bound * Transition.transitionRowCountBound c N)
transitionWeightedColumnDecayFromCeiling sourceWeight c h bound ceiling =
  ≤-trans
    (≤-reflexive
      (trans
        (Folds.weightedConcreteColumnSumNormalForm
          sourceWeight
          (Relation.transitionTailIndex c h))
        (trans
          (Folds.weightedColumnCandidateNormalFormProof
            sourceWeight
            (Relation.transitionTailIndex c h))
          (sym
            (Folds.weightedTransitionColumnBlock
              sourceWeight
              c
              c
              h)))))
    (transitionColumnDiagonalBound
      sourceWeight
      c
      c
      h
      bound
      ceiling)

------------------------------------------------------------------------
-- Remaining concrete analytic obligation.
--
-- The concrete class decomposition above is now available to a genuine
-- Schur proof.  This record names the exact two inequalities still needed;
-- it intentionally has no inhabitant here.
------------------------------------------------------------------------

record ConcreteWeightedSchurDecayObligation (N : Nat) : Set₁ where
  constructor mkConcreteWeightedSchurDecayObligation
  field
    sourceWeight :
      Relation.ConcreteNonResidualFiniteIndex N -> Nat

    targetWeight :
      Relation.ConcreteNonResidualTailIndex N -> Nat

    rowConstant : Nat
    columnConstant : Nat

    weightedRowDecay :
      (f : Relation.ConcreteNonResidualFiniteIndex N) ->
      Folds.weightedConcreteRowSum targetWeight f ≤
      rowConstant * sourceWeight f

    weightedColumnDecay :
      (t : Relation.ConcreteNonResidualTailIndex N) ->
      Folds.weightedConcreteColumnSum sourceWeight t ≤
      columnConstant * targetWeight t

    weightedSchurProduct :
      rowConstant * columnConstant ≤ (suc N) * (suc N)

------------------------------------------------------------------------
-- Aggregate composition from class-local geometric budgets.
--
-- The six decay lemmas above already eliminate the finite sums.  This
-- record isolates the remaining analytic input: a uniform ceiling for each
-- tagged family and the comparison of its resulting block mass with the
-- global row/column budget.  It is intentionally an input record; no
-- physical retained-triad estimate is inferred from the proxy count.
------------------------------------------------------------------------

record ConcreteWeightedSchurBudgets (N : Nat) : Set₁ where
  constructor mkConcreteWeightedSchurBudgets
  field
    sourceWeight :
      Relation.ConcreteNonResidualFiniteIndex N -> Nat

    targetWeight :
      Relation.ConcreteNonResidualTailIndex N -> Nat

    rowConstant : Nat
    columnConstant : Nat

    forcedTailRowCeiling :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailType.ForcedTailHead c N) -> Nat
    forcedTailRowPointwise :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailType.ForcedTailHead c N) ->
      (i : ForcedTailType.ForcedTailTail c N) ->
      targetWeight (Relation.forcedTailTailIndex c i)
        ≤ forcedTailRowCeiling c h
    forcedTailRowBudget :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailType.ForcedTailHead c N) ->
      Relation.forcedTailPairIncidenceCount c c *
        (forcedTailRowCeiling c h * ForcedTail.forcedTailTailCountBound c N)
        ≤
      rowConstant * sourceWeight (Relation.forcedTailFiniteIndex c h)

    adversarialRowCeiling :
      (c : Adversarial.AdversarialClass) ->
      (h : AdversarialType.AdversarialHead c N) -> Nat
    adversarialRowPointwise :
      (c : Adversarial.AdversarialClass) ->
      (h : AdversarialType.AdversarialHead c N) ->
      (i : AdversarialType.AdversarialTail c N) ->
      targetWeight (Relation.adversarialTailIndex c i)
        ≤ adversarialRowCeiling c h
    adversarialRowBudget :
      (c : Adversarial.AdversarialClass) ->
      (h : AdversarialType.AdversarialHead c N) ->
      Relation.adversarialPairIncidenceCount c c *
        (adversarialRowCeiling c h * Adversarial.adversarialColumnCountBound c N)
        ≤
      rowConstant * sourceWeight (Relation.adversarialFiniteIndex c h)

    transitionRowCeiling :
      (c : Transition.TransitionClass) ->
      (h : TransitionType.TransitionHead c N) -> Nat
    transitionRowPointwise :
      (c : Transition.TransitionClass) ->
      (h : TransitionType.TransitionHead c N) ->
      (i : TransitionType.TransitionTail c N) ->
      targetWeight (Relation.transitionTailIndex c i)
        ≤ transitionRowCeiling c h
    transitionRowBudget :
      (c : Transition.TransitionClass) ->
      (h : TransitionType.TransitionHead c N) ->
      Relation.transitionPairIncidenceCount c c *
        (transitionRowCeiling c h * Transition.transitionColumnCountBound c N)
        ≤
      rowConstant * sourceWeight (Relation.transitionFiniteIndex c h)

    forcedTailColumnCeiling :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailType.ForcedTailTail c N) -> Nat
    forcedTailColumnPointwise :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailType.ForcedTailTail c N) ->
      (i : ForcedTailType.ForcedTailHead c N) ->
      sourceWeight (Relation.forcedTailFiniteIndex c i)
        ≤ forcedTailColumnCeiling c h
    forcedTailColumnBudget :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailType.ForcedTailTail c N) ->
      Relation.forcedTailPairIncidenceCount c c *
        (forcedTailColumnCeiling c h * ForcedTail.forcedTailHeadCountBound c N)
        ≤
      columnConstant * targetWeight (Relation.forcedTailTailIndex c h)

    adversarialColumnCeiling :
      (c : Adversarial.AdversarialClass) ->
      (h : AdversarialType.AdversarialTail c N) -> Nat
    adversarialColumnPointwise :
      (c : Adversarial.AdversarialClass) ->
      (h : AdversarialType.AdversarialTail c N) ->
      (i : AdversarialType.AdversarialHead c N) ->
      sourceWeight (Relation.adversarialFiniteIndex c i)
        ≤ adversarialColumnCeiling c h
    adversarialColumnBudget :
      (c : Adversarial.AdversarialClass) ->
      (h : AdversarialType.AdversarialTail c N) ->
      Relation.adversarialPairIncidenceCount c c *
        (adversarialColumnCeiling c h * Adversarial.adversarialRowCountBound c N)
        ≤
      columnConstant * targetWeight (Relation.adversarialTailIndex c h)

    transitionColumnCeiling :
      (c : Transition.TransitionClass) ->
      (h : TransitionType.TransitionTail c N) -> Nat
    transitionColumnPointwise :
      (c : Transition.TransitionClass) ->
      (h : TransitionType.TransitionTail c N) ->
      (i : TransitionType.TransitionHead c N) ->
      sourceWeight (Relation.transitionFiniteIndex c i)
        ≤ transitionColumnCeiling c h
    transitionColumnBudget :
      (c : Transition.TransitionClass) ->
      (h : TransitionType.TransitionTail c N) ->
      Relation.transitionPairIncidenceCount c c *
        (transitionColumnCeiling c h * Transition.transitionRowCountBound c N)
        ≤
      columnConstant * targetWeight (Relation.transitionTailIndex c h)

    weightedSchurProduct :
      rowConstant * columnConstant ≤ (suc N) * (suc N)

-- The budget record is the theorem-facing premise surface.  This alias gives
-- callers a name which makes the conditional status explicit without
-- weakening any of the typed inequalities above.
ConcreteWeightedSchurBudgetPremises : Nat -> Set₁
ConcreteWeightedSchurBudgetPremises = ConcreteWeightedSchurBudgets

concreteWeightedSchurDecayFromBudgets :
  {N : Nat} ->
  (budgets : ConcreteWeightedSchurBudgets N) ->
  ConcreteWeightedSchurDecayObligation N
concreteWeightedSchurDecayFromBudgets {N = N} budgets =
  mkConcreteWeightedSchurDecayObligation
    (ConcreteWeightedSchurBudgets.sourceWeight budgets)
    (ConcreteWeightedSchurBudgets.targetWeight budgets)
    (ConcreteWeightedSchurBudgets.rowConstant budgets)
    (ConcreteWeightedSchurBudgets.columnConstant budgets)
    rowDecay
    columnDecay
    (ConcreteWeightedSchurBudgets.weightedSchurProduct budgets)
  where
  sourceWeight = ConcreteWeightedSchurBudgets.sourceWeight budgets
  targetWeight = ConcreteWeightedSchurBudgets.targetWeight budgets

  rowDecay :
    (f : Relation.ConcreteNonResidualFiniteIndex N) ->
    Folds.weightedConcreteRowSum targetWeight f ≤
    ConcreteWeightedSchurBudgets.rowConstant budgets * sourceWeight f
  rowDecay (Relation.forcedTailFiniteIndex c h) =
    ≤-trans
      (forcedTailWeightedRowDecayFromCeiling
        targetWeight c h
        (ConcreteWeightedSchurBudgets.forcedTailRowCeiling budgets c h)
        (ConcreteWeightedSchurBudgets.forcedTailRowPointwise budgets c h))
      (ConcreteWeightedSchurBudgets.forcedTailRowBudget budgets c h)
  rowDecay (Relation.adversarialFiniteIndex c h) =
    ≤-trans
      (adversarialWeightedRowDecayFromCeiling
        targetWeight c h
        (ConcreteWeightedSchurBudgets.adversarialRowCeiling budgets c h)
        (ConcreteWeightedSchurBudgets.adversarialRowPointwise budgets c h))
      (ConcreteWeightedSchurBudgets.adversarialRowBudget budgets c h)
  rowDecay (Relation.transitionFiniteIndex c h) =
    ≤-trans
      (transitionWeightedRowDecayFromCeiling
        targetWeight c h
        (ConcreteWeightedSchurBudgets.transitionRowCeiling budgets c h)
        (ConcreteWeightedSchurBudgets.transitionRowPointwise budgets c h))
      (ConcreteWeightedSchurBudgets.transitionRowBudget budgets c h)

  columnDecay :
    (t : Relation.ConcreteNonResidualTailIndex N) ->
    Folds.weightedConcreteColumnSum sourceWeight t ≤
    ConcreteWeightedSchurBudgets.columnConstant budgets * targetWeight t
  columnDecay (Relation.forcedTailTailIndex c h) =
    ≤-trans
      (forcedTailWeightedColumnDecayFromCeiling
        sourceWeight c h
        (ConcreteWeightedSchurBudgets.forcedTailColumnCeiling budgets c h)
        (ConcreteWeightedSchurBudgets.forcedTailColumnPointwise budgets c h))
      (ConcreteWeightedSchurBudgets.forcedTailColumnBudget budgets c h)
  columnDecay (Relation.adversarialTailIndex c h) =
    ≤-trans
      (adversarialWeightedColumnDecayFromCeiling
        sourceWeight c h
        (ConcreteWeightedSchurBudgets.adversarialColumnCeiling budgets c h)
        (ConcreteWeightedSchurBudgets.adversarialColumnPointwise budgets c h))
      (ConcreteWeightedSchurBudgets.adversarialColumnBudget budgets c h)
  columnDecay (Relation.transitionTailIndex c h) =
    ≤-trans
      (transitionWeightedColumnDecayFromCeiling
        sourceWeight c h
        (ConcreteWeightedSchurBudgets.transitionColumnCeiling budgets c h)
        (ConcreteWeightedSchurBudgets.transitionColumnPointwise budgets c h))
      (ConcreteWeightedSchurBudgets.transitionColumnBudget budgets c h)

------------------------------------------------------------------------
-- Constructive product handoff.
--
-- The decay record still has no inhabitant because its row/column fields are
-- the missing analytic estimates.  If those estimates are supplied by a
-- future proof, this alias exports the already-proved Nat product witness
-- without asserting any additional decay or operator fact.

consumeConcreteWeightedSchurDecay :
  {N : Nat} ->
  (obligation : ConcreteWeightedSchurDecayObligation N) ->
  Schur.BipartiteWeightedSchurProductBoundWitness
    (ConcreteWeightedSchurDecayObligation.rowConstant obligation)
    (ConcreteWeightedSchurDecayObligation.columnConstant obligation)
    ((suc N) * (suc N))
consumeConcreteWeightedSchurDecay obligation =
  Schur.mkBipartiteWeightedSchurProductBoundWitness
    (ConcreteWeightedSchurDecayObligation.weightedSchurProduct obligation)
