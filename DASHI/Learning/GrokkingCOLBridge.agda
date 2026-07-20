module DASHI.Learning.GrokkingCOLBridge where

open import DASHI.Core.Prelude
open import DASHI.Geometry.COL using (COL; iterate; E-monotone-iter)
open import DASHI.Learning.GrokkingOperatorContract

------------------------------------------------------------------------
-- Learning / COL cross-pollination
--
-- A level-indexed family of learning operators becomes a COL system when:
--
--   * total MDL is used as the level energy;
--   * the learning update is used as the within-level kernel;
--   * an explicit obstruction detector is stable under that update; and
--   * a witness-respecting capacity lift is supplied.
--
-- This is the precise typed seam between the machine-learning tranche and the
-- existing Contraction–Obstruction–Lift architecture.  It does not assert that
-- every optimiser supplies an obstruction detector or a valid lift.
------------------------------------------------------------------------

record LearningCOLBundle (S : Nat -> Set) : Set1 where
  field
    learner : (n : Nat) -> LearningOperator (S n)
    Obs     : (n : Nat) -> S n -> Bool
    lift    : (n : Nat) -> S n -> S (suc n)

    obs-stable :
      (n : Nat) (x : S n) ->
      Obs n x ≡ true ->
      Obs n (LearningOperator.step (learner n) x) ≡ true

    embed-ok : (n : Nat) (x : S n) -> ⊤

open LearningCOLBundle public

asCOL : forall {S : Nat -> Set} -> LearningCOLBundle S -> COL S
asCOL B = record
  { E = λ n -> LearningOperator.totalMDL (learner B n)
  ; K = λ n -> LearningOperator.step (learner B n)
  ; Obs = Obs B
  ; lift = lift B
  ; contract = λ n x -> LearningOperator.mdlMonotone (learner B n) x
  ; obs-stable = obs-stable B
  ; embed-ok = embed-ok B
  }

------------------------------------------------------------------------
-- Imported consequence: repeated within-level learning cannot exceed the
-- initial total MDL under the supplied LearningOperator contract.
------------------------------------------------------------------------

learning-MDL-monotone-iter :
  forall {S : Nat -> Set} (B : LearningCOLBundle S) ->
  (n : Nat) (k : Nat) (x : S n) ->
  LearningOperator.totalMDL (learner B n)
    (iterate (LearningOperator.step (learner B n)) k x)
  ≤ LearningOperator.totalMDL (learner B n) x
learning-MDL-monotone-iter B = E-monotone-iter (asCOL B)

------------------------------------------------------------------------
-- The missing theorem between AdamW-style regularisation and literal MDL is
-- made explicit rather than silently assumed.
------------------------------------------------------------------------

record RegularisationCodingBridge (S : Set) : Set1 where
  field
    learner      : LearningOperator S
    proxyPenalty : S -> Nat

    -- A concrete coding theorem must justify interpreting the empirical
    -- regularisation proxy as the model-description component.
    proxy-is-model-code :
      (s : S) ->
      proxyPenalty s ≡ LearningOperator.modelCode learner s

open RegularisationCodingBridge public

------------------------------------------------------------------------
-- Likewise, an observed test-accuracy transition is not itself a contraction
-- proof.  This record names the extra witness required to connect a measured
-- first-passage event to the operator decomposition.
------------------------------------------------------------------------

record GrokkingMechanismWitness : Set where
  field
    observation   : GrokkingObservation
    decomposition : GrokkingDecomposition

open GrokkingMechanismWitness public
