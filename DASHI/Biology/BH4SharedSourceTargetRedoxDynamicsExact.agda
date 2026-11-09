module DASHI.Biology.BH4SharedSourceTargetRedoxDynamicsExact where

-- Constructive minimal physical CHAIN: accessible source BH4, target BH4,
-- and target BH2 are one shared redox/transport material inventory.
-- Source transport changes the SAME target BH4 subsequently used by
-- oxidation/recycling. There is no isolated per-edge duplicated state.
--
-- The elementary update is a nonnegative exact-integer event semantics,
-- NOT source-measured concentration kinetics or a Kitzerow disease model.
-- Physical-source/compartment obligations remain in existing BH4 owners.

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.BH4CompartmentKineticStateExact as Kinetics
import DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact as Finite

record SharedSourceTargetRedox : Set where
  constructor shared-source-target-redox
  field
    sourceBH4 : Nat
    targetBH4 : Nat
    targetBH2 : Nat

open SharedSourceTargetRedox public

totalBiopterin : SharedSourceTargetRedox → Nat
totalBiopterin (shared-source-target-redox a b c) = a + (b + c)

-- Physical direction: source-to-target cofactor transfer.
-- A membrane gate is represented by the selected action, not silently
-- inferred from two source and target compartment labels.
deliverBH4 : SharedSourceTargetRedox → SharedSourceTargetRedox
deliverBH4 (shared-source-target-redox zero b c) =
  shared-source-target-redox zero b c
deliverBH4 (shared-source-target-redox (suc a) b c) =
  shared-source-target-redox a (suc b) c

-- Selected redox reactions at the SAME target region:
-- BH4 -> BH2 and BH2 -> BH4 are event-level cofactor redox changes.
-- Each full biochemical mechanism includes further reagents, electrons
-- and products; these are NOT complete balanced Rhea reaction columns.
oxidizeTarget : SharedSourceTargetRedox → SharedSourceTargetRedox
oxidizeTarget (shared-source-target-redox a zero c) =
  shared-source-target-redox a zero c
oxidizeTarget (shared-source-target-redox a (suc b) c) =
  shared-source-target-redox a b (suc c)

recycleTarget : SharedSourceTargetRedox → SharedSourceTargetRedox
recycleTarget (shared-source-target-redox a b zero) =
  shared-source-target-redox a b zero
recycleTarget (shared-source-target-redox a b (suc c)) =
  shared-source-target-redox a (suc b) c

externalBH4Supply : Nat → SharedSourceTargetRedox → SharedSourceTargetRedox
externalBH4Supply q (shared-source-target-redox a b c) =
  shared-source-target-redox (q + a) b c

deliveryConservesBiopterin :
  (s : SharedSourceTargetRedox) →
  totalBiopterin (deliverBH4 s) ≡ totalBiopterin s
deliveryConservesBiopterin (shared-source-target-redox zero b c) = refl
deliveryConservesBiopterin (shared-source-target-redox (suc a) b c) =
  +-suc a (b + c)

oxidationConservesBiopterin :
  (s : SharedSourceTargetRedox) →
  totalBiopterin (oxidizeTarget s) ≡ totalBiopterin s
oxidationConservesBiopterin (shared-source-target-redox a zero c) = refl
oxidationConservesBiopterin (shared-source-target-redox a (suc b) c) =
  cong (λ t → a + t) (+-suc b c)

recyclingConservesBiopterin :
  (s : SharedSourceTargetRedox) →
  totalBiopterin (recycleTarget s) ≡ totalBiopterin s
recyclingConservesBiopterin (shared-source-target-redox a b zero) = refl
recyclingConservesBiopterin (shared-source-target-redox a b (suc c)) =
  cong (λ t → a + t) (sym (+-suc b c))

externalSupplyBalancesBiopterin :
  (q : Nat) (s : SharedSourceTargetRedox) →
  totalBiopterin (externalBH4Supply q s)
    ≡ totalBiopterin s + q
externalSupplyBalancesBiopterin q (shared-source-target-redox a b c) =
  trans (+-assoc q a (b + c))
        (+-comm q (a + (b + c)))

data RedoxTransportAction : Set where
  gateClosed : RedoxTransportAction
  deliver : RedoxTransportAction
  oxidize : RedoxTransportAction
  recycle : RedoxTransportAction
  inject : Nat → RedoxTransportAction

update : RedoxTransportAction →
  SharedSourceTargetRedox → SharedSourceTargetRedox
update gateClosed s = s
update deliver s = deliverBH4 s
update oxidize s = oxidizeTarget s
update recycle s = recycleTarget s
update (inject q) s = externalBH4Supply q s

injected : RedoxTransportAction → Nat
injected gateClosed = 0
injected deliver = 0
injected oxidize = 0
injected recycle = 0
injected (inject q) = q

oneStepOpenSystemBalance :
  (action : RedoxTransportAction)
  (s : SharedSourceTargetRedox) →
  totalBiopterin (update action s)
    ≡ totalBiopterin s + injected action
oneStepOpenSystemBalance gateClosed s =
  sym (+-identityʳ (totalBiopterin s))
oneStepOpenSystemBalance deliver s =
  trans (deliveryConservesBiopterin s)
        (sym (+-identityʳ (totalBiopterin s)))
oneStepOpenSystemBalance oxidize s =
  trans (oxidationConservesBiopterin s)
        (sym (+-identityʳ (totalBiopterin s)))
oneStepOpenSystemBalance recycle s =
  trans (recyclingConservesBiopterin s)
        (sym (+-identityʳ (totalBiopterin s)))
oneStepOpenSystemBalance (inject q) s =
  externalSupplyBalancesBiopterin q s

-- Chronological source-controlled evolution.
run : List RedoxTransportAction →
  SharedSourceTargetRedox → SharedSourceTargetRedox
run [] s = s
run (action ∷ rest) s = run rest (update action s)

totalInput : List RedoxTransportAction → Nat
totalInput [] = 0
totalInput (action ∷ rest) = injected action + totalInput rest

allControlledHistoriesPreserveOpenBiopterinBalance :
  (actions : List RedoxTransportAction)
  (s : SharedSourceTargetRedox) →
  totalBiopterin (run actions s)
    ≡ totalBiopterin s + totalInput actions
allControlledHistoriesPreserveOpenBiopterinBalance [] s =
  sym (+-identityʳ (totalBiopterin s))
allControlledHistoriesPreserveOpenBiopterinBalance
  (action ∷ rest) s =
  trans
    (allControlledHistoriesPreserveOpenBiopterinBalance rest
      (update action s))
    (trans
      (cong (λ n → n + totalInput rest)
        (oneStepOpenSystemBalance action s))
      (+-assoc (totalBiopterin s)
        (injected action) (totalInput rest)))

-- Deliver, THEN oxidize: the target observes the *same* BH4 molecule
-- delivered from the source. Reverse action order cannot oxidize a
-- missing cofactor at the target.
originalState : SharedSourceTargetRedox
originalState = shared-source-target-redox 1 0 0

deliveredThenOxidized oxidizedThenDelivered : SharedSourceTargetRedox
deliveredThenOxidized = run (deliver ∷ oxidize ∷ []) originalState
oxidizedThenDelivered = run (oxidize ∷ deliver ∷ []) originalState

deliveredThenOxidizedBH2 :
  targetBH2 deliveredThenOxidized ≡ 1
deliveredThenOxidizedBH2 = refl

oxidizedThenDeliveredBH2 :
  targetBH2 oxidizedThenDelivered ≡ 0
oxidizedThenDeliveredBH2 = refl

zeroIsNotOne : 0 ≡ 1 → ⊥
zeroIsNotOne ()

deliveryAndOxidationDoNotCommute :
  deliveredThenOxidized ≡ oxidizedThenDelivered → ⊥
deliveryAndOxidationDoNotCommute equality =
  zeroIsNotOne
    (trans (sym oxidizedThenDeliveredBH2)
      (trans (sym (cong targetBH2 equality))
        deliveredThenOxidizedBH2))

-- Original source-qualified BI0 physical owners remain distinct:
selectedPhysicalBH4PoolType : Set
selectedPhysicalBH4PoolType = System.BH4PoolState

selectedQuantitativeKineticsType : Set
selectedQuantitativeKineticsType = Kinetics.BH4ParameterEvidence

finiteIonTransportDonorType : Set
finiteIonTransportDonorType = Finite.IonPairState
