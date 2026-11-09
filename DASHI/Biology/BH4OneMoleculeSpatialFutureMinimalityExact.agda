module DASHI.Biology.BH4OneMoleculeSpatialFutureMinimalityExact where

-- Genuine finite, source-structured physical EVENT MODEL.
-- One pterin moiety occupies one of three distinct located/redox
-- states: source BH4, target BH4, target oxidized pterin.
-- The BH4<->oxidized-pterin event is lumped and NOT identified
-- with full QDPR chemical species/kinetics (the dedicated RHEA:32253
-- owner keeps qDHB, NADH, H+ and NAD+ explicit).
--
-- Exact result: a target-oxidized readout plus the selected actions
-- induces THREE distinguishable future classes, even though the
-- global cofactor moiety count is always one. This is a proved
-- minimal future quotient for this selected finite physical slice.

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SharedSourceTargetRedoxDynamicsExact as Redox

data LocatedRedoxState : Set where
  sourceReduced : LocatedRedoxState
  targetReduced : LocatedRedoxState
  targetOxidized : LocatedRedoxState

data ControlledAction : Set where
  hold : ControlledAction
  deliverToTarget : ControlledAction
  oxidizeAtTarget : ControlledAction
  recycleAtTarget : ControlledAction

step : ControlledAction → LocatedRedoxState → LocatedRedoxState
step hold s = s
step deliverToTarget sourceReduced = targetReduced
step deliverToTarget targetReduced = targetReduced
step deliverToTarget targetOxidized = targetOxidized
step oxidizeAtTarget sourceReduced = sourceReduced
step oxidizeAtTarget targetReduced = targetOxidized
step oxidizeAtTarget targetOxidized = targetOxidized
step recycleAtTarget sourceReduced = sourceReduced
step recycleAtTarget targetReduced = targetReduced
step recycleAtTarget targetOxidized = targetReduced

encode : LocatedRedoxState → Redox.SharedSourceTargetRedox
encode sourceReduced = Redox.shared-source-target-redox 1 0 0
encode targetReduced = Redox.shared-source-target-redox 0 1 0
encode targetOxidized = Redox.shared-source-target-redox 0 0 1

asOriginalUpdate : ControlledAction → Redox.RedoxTransportAction
asOriginalUpdate hold = Redox.gateClosed
asOriginalUpdate deliverToTarget = Redox.deliver
asOriginalUpdate oxidizeAtTarget = Redox.oxidize
asOriginalUpdate recycleAtTarget = Redox.recycle

-- The three states are not merely a new abstraction: they are
-- definitionally an invariant subset of the previously constructed
-- SAME shared target BH4/BH2 physical-event transition model.
selectedOriginalPhysicalStepCommutes :
  (action : ControlledAction)
  (state : LocatedRedoxState) →
  encode (step action state)
    ≡ Redox.update (asOriginalUpdate action) (encode state)
selectedOriginalPhysicalStepCommutes hold sourceReduced = refl
selectedOriginalPhysicalStepCommutes hold targetReduced = refl
selectedOriginalPhysicalStepCommutes hold targetOxidized = refl
selectedOriginalPhysicalStepCommutes deliverToTarget sourceReduced = refl
selectedOriginalPhysicalStepCommutes deliverToTarget targetReduced = refl
selectedOriginalPhysicalStepCommutes deliverToTarget targetOxidized = refl
selectedOriginalPhysicalStepCommutes oxidizeAtTarget sourceReduced = refl
selectedOriginalPhysicalStepCommutes oxidizeAtTarget targetReduced = refl
selectedOriginalPhysicalStepCommutes oxidizeAtTarget targetOxidized = refl
selectedOriginalPhysicalStepCommutes recycleAtTarget sourceReduced = refl
selectedOriginalPhysicalStepCommutes recycleAtTarget targetReduced = refl
selectedOriginalPhysicalStepCommutes recycleAtTarget targetOxidized = refl

run : List ControlledAction → LocatedRedoxState → LocatedRedoxState
run [] state = state
run (action ∷ rest) state = run rest (step action state)

readout : LocatedRedoxState → Bool
readout sourceReduced = false
readout targetReduced = false
readout targetOxidized = true

FutureEquivalent : LocatedRedoxState → LocatedRedoxState → Set
FutureEquivalent x y =
  (history : List ControlledAction) →
  readout (run history x) ≡ readout (run history y)

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

futureEquivalentImpliesIdenticalPhysicalState :
  (x y : LocatedRedoxState) →
  FutureEquivalent x y → x ≡ y
futureEquivalentImpliesIdenticalPhysicalState sourceReduced sourceReduced eq = refl
futureEquivalentImpliesIdenticalPhysicalState sourceReduced targetReduced eq =
  ⊥-elim (falseNotTrue (eq (oxidizeAtTarget ∷ [])))
futureEquivalentImpliesIdenticalPhysicalState sourceReduced targetOxidized eq =
  ⊥-elim (falseNotTrue (eq []))
futureEquivalentImpliesIdenticalPhysicalState targetReduced sourceReduced eq =
  ⊥-elim (falseNotTrue (sym (eq (oxidizeAtTarget ∷ []))))
futureEquivalentImpliesIdenticalPhysicalState targetReduced targetReduced eq = refl
futureEquivalentImpliesIdenticalPhysicalState targetReduced targetOxidized eq =
  ⊥-elim (falseNotTrue (eq []))
futureEquivalentImpliesIdenticalPhysicalState targetOxidized sourceReduced eq =
  ⊥-elim (falseNotTrue (sym (eq [])))
futureEquivalentImpliesIdenticalPhysicalState targetOxidized targetReduced eq =
  ⊥-elim (falseNotTrue (sym (eq [])))
futureEquivalentImpliesIdenticalPhysicalState targetOxidized targetOxidized eq = refl

identicalPhysicalStateImpliesFutureEquivalent :
  (x y : LocatedRedoxState) →
  x ≡ y → FutureEquivalent x y
identicalPhysicalStateImpliesFutureEquivalent x .x refl history = refl

allSelectedPhysicalMoietiesEqualOne :
  (state : LocatedRedoxState) →
  Redox.totalBiopterin (encode state) ≡ 1
allSelectedPhysicalMoietiesEqualOne sourceReduced = refl
allSelectedPhysicalMoietiesEqualOne targetReduced = refl
allSelectedPhysicalMoietiesEqualOne targetOxidized = refl

-- A scalar-only future observer cannot even distinguish sourceReduced
-- from targetReduced, despite the oxidizeAtTarget experiment separating
-- them. The lemma above proves no two of the three classes can merge.
globalMoietyCountCannotPredictAllSelectedFutures :
  (predict : Nat → Bool)
  ((state : LocatedRedoxState) (history : List ControlledAction) →
    readout (run history state)
      ≡ predict
        (Redox.totalBiopterin (encode state))) →
  ⊥
globalMoietyCountCannotPredictAllSelectedFutures predict factor =
  falseNotTrue
    (trans
      (factor sourceReduced (oxidizeAtTarget ∷ []))
      (trans
        (cong predict
          (trans
            (allSelectedPhysicalMoietiesEqualOne sourceReduced)
            (sym (allSelectedPhysicalMoietiesEqualOne targetReduced))))
        (sym (factor targetReduced (oxidizeAtTarget ∷ [])))))
