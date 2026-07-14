module DASHI.Physics.Closure.NSTriadKNEncodedRetainedFiberFormula where

-- Constructive finite-fiber formula for the declared Nat incidence carriers.
-- This is deliberately an encoded/proxy theorem: it enumerates residue tags
-- and does not identify the unit weight with the physical amplitude/coherence
-- weight from the exact real-valued operator definition.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailType
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialType
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionType
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula

------------------------------------------------------------------------
-- Finite residue enumeration.

allFin : {n : Nat} -> List (Fin n)
allFin {n = zero} = []
allFin {n = suc n} = zero ∷ map suc allFin

unitWeight : {A : Set} -> A -> Nat
unitWeight _ = suc zero

mapUnitWeightSumInvariant :
  {A B : Set} ->
  (f : A -> B) ->
  (xs : List A) ->
  KernelFormula.weightedListSum unitWeight (map f xs)
    ≡ KernelFormula.weightedListSum unitWeight xs
mapUnitWeightSumInvariant f [] = refl
mapUnitWeightSumInvariant f (x ∷ xs) =
  cong (_+_ (suc zero)) (mapUnitWeightSumInvariant f xs)

allFinUnitWeightSum :
  (n : Nat) ->
  KernelFormula.weightedListSum unitWeight (allFin {n = n}) ≡ n
allFinUnitWeightSum zero = refl
allFinUnitWeightSum (suc n) =
  trans
    (cong (_+_ (suc zero))
      (mapUnitWeightSumInvariant suc (allFin {n = n})))
    (cong suc (allFinUnitWeightSum n))

------------------------------------------------------------------------
-- Encoded residue fibers.  Mixed profile classes are empty, matching the
-- class-diagonal proxy count in PairIncidenceRelation.

encodedForcedTailFiber :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  ForcedTailType.ForcedTailHead c N ->
  ForcedTailType.ForcedTailTail c N ->
  List (Relation.ConcreteNonResidualTriadIncidence N)
encodedForcedTailFiber c h t =
  map
    (λ r → Relation.forcedTailIncidence c
      (ForcedTailType.mkForcedTailTriadIncidence h t r))
    (allFin {n = ForcedTail.forcedTailFiberConstant c})

encodedAdversarialFiber :
  {N : Nat} ->
  (c : Adversarial.AdversarialClass) ->
  AdversarialType.AdversarialHead c N ->
  AdversarialType.AdversarialTail c N ->
  List (Relation.ConcreteNonResidualTriadIncidence N)
encodedAdversarialFiber c h t =
  map
    (λ r → Relation.adversarialIncidence c
      (AdversarialType.mkAdversarialTriadIncidence h t r))
    (allFin {n = AdversarialType.adversarialFiberConstant c})

encodedTransitionFiber :
  {N : Nat} ->
  (c : Transition.TransitionClass) ->
  TransitionType.TransitionHead c N ->
  TransitionType.TransitionTail c N ->
  List (Relation.ConcreteNonResidualTriadIncidence N)
encodedTransitionFiber c h t =
  map
    (λ r → Relation.transitionIncidence c
      (TransitionType.mkTransitionTriadIncidence h t r))
    (allFin {n = TransitionType.transitionFiberConstant c})

encodedFiber :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Relation.ConcreteNonResidualTailIndex N ->
  List (Relation.ConcreteNonResidualTriadIncidence N)
encodedFiber
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.tailEnd t) with c
... | ForcedTail.tailEnd = encodedForcedTailFiber ForcedTail.tailEnd h t
... | _ = []
encodedFiber
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.nearTail t) with c
... | ForcedTail.nearTail = encodedForcedTailFiber ForcedTail.nearTail h t
... | _ = []
encodedFiber
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.transition t) with c
... | ForcedTail.transition = encodedForcedTailFiber ForcedTail.transition h t
... | _ = []
encodedFiber
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.degenerate t) with c
... | ForcedTail.degenerate = encodedForcedTailFiber ForcedTail.degenerate h t
... | _ = []
encodedFiber (Relation.forcedTailFiniteIndex c h) (Relation.adversarialTailIndex d t) = []
encodedFiber (Relation.forcedTailFiniteIndex c h) (Relation.transitionTailIndex d t) = []

encodedFiber (Relation.adversarialFiniteIndex c h) (Relation.forcedTailTailIndex d t) = []
encodedFiber
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex Adversarial.sparseAdmissible t) with c
... | Adversarial.sparseAdmissible = encodedAdversarialFiber Adversarial.sparseAdmissible h t
... | _ = []
encodedFiber
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex Adversarial.angularDegenerate t) with c
... | Adversarial.angularDegenerate = encodedAdversarialFiber Adversarial.angularDegenerate h t
... | _ = []
encodedFiber
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex Adversarial.boundarySmallShell t) with c
... | Adversarial.boundarySmallShell = encodedAdversarialFiber Adversarial.boundarySmallShell h t
... | _ = []
encodedFiber (Relation.adversarialFiniteIndex c h) (Relation.transitionTailIndex d t) = []

encodedFiber (Relation.transitionFiniteIndex c h) (Relation.forcedTailTailIndex d t) = []
encodedFiber (Relation.transitionFiniteIndex c h) (Relation.adversarialTailIndex d t) = []
encodedFiber
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.thinTransition t) with c
... | Transition.thinTransition = encodedTransitionFiber Transition.thinTransition h t
... | _ = []
encodedFiber
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.balancedTransition t) with c
... | Transition.balancedTransition = encodedTransitionFiber Transition.balancedTransition h t
... | _ = []
encodedFiber
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.rowThickTransition t) with c
... | Transition.rowThickTransition = encodedTransitionFiber Transition.rowThickTransition h t
... | _ = []
encodedFiber
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.columnThickTransition t) with c
... | Transition.columnThickTransition = encodedTransitionFiber Transition.columnThickTransition h t
... | _ = []

encodedFiberAggregate :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
encodedFiberAggregate f t =
  KernelFormula.weightedListSum unitWeight (encodedFiber f t)

encodedForcedTailFiberAggregate :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (t : ForcedTailType.ForcedTailTail c N) ->
  KernelFormula.weightedListSum unitWeight
    (encodedForcedTailFiber c h t)
    ≡ ForcedTail.forcedTailFiberConstant c
encodedForcedTailFiberAggregate c h t =
  trans
    (mapUnitWeightSumInvariant
      (λ r → Relation.forcedTailIncidence c
        (ForcedTailType.mkForcedTailTriadIncidence h t r))
      (allFin {n = ForcedTail.forcedTailFiberConstant c}))
    (allFinUnitWeightSum (ForcedTail.forcedTailFiberConstant c))

encodedAdversarialFiberAggregate :
  {N : Nat} ->
  (c : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  (t : AdversarialType.AdversarialTail c N) ->
  KernelFormula.weightedListSum unitWeight
    (encodedAdversarialFiber c h t)
    ≡ AdversarialType.adversarialFiberConstant c
encodedAdversarialFiberAggregate c h t =
  trans
    (mapUnitWeightSumInvariant
      (λ r → Relation.adversarialIncidence c
        (AdversarialType.mkAdversarialTriadIncidence h t r))
      (allFin {n = AdversarialType.adversarialFiberConstant c}))
    (allFinUnitWeightSum (AdversarialType.adversarialFiberConstant c))

encodedTransitionFiberAggregate :
  {N : Nat} ->
  (c : Transition.TransitionClass) ->
  (h : TransitionType.TransitionHead c N) ->
  (t : TransitionType.TransitionTail c N) ->
  KernelFormula.weightedListSum unitWeight
    (encodedTransitionFiber c h t)
    ≡ TransitionType.transitionFiberConstant c
encodedTransitionFiberAggregate c h t =
  trans
    (mapUnitWeightSumInvariant
      (λ r → Relation.transitionIncidence c
        (TransitionType.mkTransitionTriadIncidence h t r))
      (allFin {n = TransitionType.transitionFiberConstant c}))
    (allFinUnitWeightSum (TransitionType.transitionFiberConstant c))

encodedFiberAggregateEqualsPairIncidenceCount :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  encodedFiberAggregate f t
    ≡ Relation.concreteNonResidualPairIncidenceCount f t
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.tailEnd t) with c
... | ForcedTail.tailEnd = encodedForcedTailFiberAggregate {N = N} ForcedTail.tailEnd h t
... | ForcedTail.nearTail = refl
... | ForcedTail.transition = refl
... | ForcedTail.degenerate = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.nearTail t) with c
... | ForcedTail.nearTail = encodedForcedTailFiberAggregate {N = N} ForcedTail.nearTail h t
... | ForcedTail.tailEnd = refl
... | ForcedTail.transition = refl
... | ForcedTail.degenerate = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.transition t) with c
... | ForcedTail.transition = encodedForcedTailFiberAggregate {N = N} ForcedTail.transition h t
... | ForcedTail.tailEnd = refl
... | ForcedTail.nearTail = refl
... | ForcedTail.degenerate = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex ForcedTail.degenerate t) with c
... | ForcedTail.degenerate = encodedForcedTailFiberAggregate {N = N} ForcedTail.degenerate h t
... | ForcedTail.tailEnd = refl
... | ForcedTail.nearTail = refl
... | ForcedTail.transition = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N} (Relation.forcedTailFiniteIndex c h) (Relation.adversarialTailIndex d t) = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N} (Relation.forcedTailFiniteIndex c h) (Relation.transitionTailIndex d t) = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N} (Relation.adversarialFiniteIndex c h) (Relation.forcedTailTailIndex d t) = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex Adversarial.sparseAdmissible t) with c
... | Adversarial.sparseAdmissible = encodedAdversarialFiberAggregate {N = N} Adversarial.sparseAdmissible h t
... | Adversarial.angularDegenerate = refl
... | Adversarial.boundarySmallShell = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex Adversarial.angularDegenerate t) with c
... | Adversarial.angularDegenerate = encodedAdversarialFiberAggregate {N = N} Adversarial.angularDegenerate h t
... | Adversarial.sparseAdmissible = refl
... | Adversarial.boundarySmallShell = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex Adversarial.boundarySmallShell t) with c
... | Adversarial.boundarySmallShell = encodedAdversarialFiberAggregate {N = N} Adversarial.boundarySmallShell h t
... | Adversarial.sparseAdmissible = refl
... | Adversarial.angularDegenerate = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N} (Relation.adversarialFiniteIndex c h) (Relation.transitionTailIndex d t) = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N} (Relation.transitionFiniteIndex c h) (Relation.forcedTailTailIndex d t) = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N} (Relation.transitionFiniteIndex c h) (Relation.adversarialTailIndex d t) = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.thinTransition t) with c
... | Transition.thinTransition = encodedTransitionFiberAggregate {N = N} Transition.thinTransition h t
... | Transition.balancedTransition = refl
... | Transition.rowThickTransition = refl
... | Transition.columnThickTransition = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.balancedTransition t) with c
... | Transition.balancedTransition = encodedTransitionFiberAggregate {N = N} Transition.balancedTransition h t
... | Transition.thinTransition = refl
... | Transition.rowThickTransition = refl
... | Transition.columnThickTransition = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.rowThickTransition t) with c
... | Transition.rowThickTransition = encodedTransitionFiberAggregate {N = N} Transition.rowThickTransition h t
... | Transition.thinTransition = refl
... | Transition.balancedTransition = refl
... | Transition.columnThickTransition = refl
encodedFiberAggregateEqualsPairIncidenceCount {N = N}
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex Transition.columnThickTransition t) with c
... | Transition.columnThickTransition = encodedTransitionFiberAggregate {N = N} Transition.columnThickTransition h t
... | Transition.thinTransition = refl
... | Transition.balancedTransition = refl
... | Transition.rowThickTransition = refl

encodedKernelFormulaUsesFiniteWeightedFiber :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  encodedFiberAggregate f t
    ≡ KernelFormula.weightedListSum unitWeight (encodedFiber f t)
encodedKernelFormulaUsesFiniteWeightedFiber f t = refl

encodedRetainedFiberFormulaClosed : Bool
encodedRetainedFiberFormulaClosed = true

encodedRetainedFiberFormulaClosedIsTrue :
  encodedRetainedFiberFormulaClosed ≡ true
encodedRetainedFiberFormulaClosedIsTrue = refl

-- This flag is intentionally separate from the physical formula gate.
physicalRetainedFiberFormulaClosed : Bool
physicalRetainedFiberFormulaClosed = false

physicalRetainedFiberFormulaClosedIsFalse :
  physicalRetainedFiberFormulaClosed ≡ false
physicalRetainedFiberFormulaClosedIsFalse = refl
