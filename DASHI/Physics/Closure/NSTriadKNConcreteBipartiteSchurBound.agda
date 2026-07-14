module DASHI.Physics.Closure.NSTriadKNConcreteBipartiteSchurBound where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_≤_; _*_; _+_; z≤n)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNBipartiteWeightedSchurWitness as Schur
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailType
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialType
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionType
import DASHI.Physics.Closure.NSTriadKNConcreteCorrectedRefinement as CorrectedRefinement
import DASHI.Physics.Closure.NSTriadKNConcreteIndexClassifierBridge as ConcreteBridge
import DASHI.Physics.Closure.NSTriadKNConcreteWeightedFiberFolds as WeightedFibers
import DASHI.Physics.Closure.NSTriadKNConcreteWeightedSchurDecay as Decay
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel

------------------------------------------------------------------------
-- Every concrete class block is constant over its dependent Fin fiber.
-- The resulting identities are the exact finite-sum part of the Schur
-- argument; no decay or operator estimate is hidden in these lemmas.

forcedTailRowBlock :
  {N : Nat} ->
  (c d : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  Schur.sumFin
    {n = ForcedTail.forcedTailTailCountBound d N}
    (λ i -> Relation.concreteNonResidualPairIncidenceCount
      (Relation.forcedTailFiniteIndex {shellIndex = N} c h)
      (Relation.forcedTailTailIndex {shellIndex = N} d i))
  ≡ Relation.forcedTailPairIncidenceCount c d *
    ForcedTail.forcedTailTailCountBound d N
forcedTailRowBlock c d h =
  Schur.sumFinConstant
    (Relation.forcedTailPairIncidenceCount c d)

adversarialRowBlock :
  {N : Nat} ->
  (c d : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  Schur.sumFin
    {n = Adversarial.adversarialColumnCountBound d N}
    (λ i -> Relation.concreteNonResidualPairIncidenceCount
      (Relation.adversarialFiniteIndex {shellIndex = N} c h)
      (Relation.adversarialTailIndex {shellIndex = N} d i))
  ≡ Relation.adversarialPairIncidenceCount c d *
    Adversarial.adversarialColumnCountBound d N
adversarialRowBlock c d h =
  Schur.sumFinConstant
    (Relation.adversarialPairIncidenceCount c d)

transitionRowBlock :
  {N : Nat} ->
  (c d : Transition.TransitionClass) ->
  (h : TransitionType.TransitionHead c N) ->
  Schur.sumFin
    {n = Transition.transitionColumnCountBound d N}
    (λ i -> Relation.concreteNonResidualPairIncidenceCount
      (Relation.transitionFiniteIndex {shellIndex = N} c h)
      (Relation.transitionTailIndex {shellIndex = N} d i))
  ≡ Relation.transitionPairIncidenceCount c d *
    Transition.transitionColumnCountBound d N
transitionRowBlock c d h =
  Schur.sumFinConstant
    (Relation.transitionPairIncidenceCount c d)

forcedTailColumnBlock :
  {N : Nat} ->
  (c d : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailTail c N) ->
  Schur.sumFin
    {n = ForcedTail.forcedTailHeadCountBound d N}
    (λ i -> Relation.concreteNonResidualPairIncidenceCount
      (Relation.forcedTailFiniteIndex {shellIndex = N} d i)
      (Relation.forcedTailTailIndex {shellIndex = N} c h))
  ≡ Relation.forcedTailPairIncidenceCount d c *
    ForcedTail.forcedTailHeadCountBound d N
forcedTailColumnBlock c d h =
  Schur.sumFinConstant
    (Relation.forcedTailPairIncidenceCount d c)

adversarialColumnBlock :
  {N : Nat} ->
  (c d : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialTail c N) ->
  Schur.sumFin
    {n = Adversarial.adversarialRowCountBound d N}
    (λ i -> Relation.concreteNonResidualPairIncidenceCount
      (Relation.adversarialFiniteIndex {shellIndex = N} d i)
      (Relation.adversarialTailIndex {shellIndex = N} c h))
  ≡ Relation.adversarialPairIncidenceCount d c *
    Adversarial.adversarialRowCountBound d N
adversarialColumnBlock c d h =
  Schur.sumFinConstant
    (Relation.adversarialPairIncidenceCount d c)

transitionColumnBlock :
  {N : Nat} ->
  (c d : Transition.TransitionClass) ->
  (h : TransitionType.TransitionTail c N) ->
  Schur.sumFin
    {n = Transition.transitionRowCountBound d N}
    (λ i -> Relation.concreteNonResidualPairIncidenceCount
      (Relation.transitionFiniteIndex {shellIndex = N} d i)
      (Relation.transitionTailIndex {shellIndex = N} c h))
  ≡ Relation.transitionPairIncidenceCount d c *
    Transition.transitionRowCountBound d N
transitionColumnBlock c d h =
  Schur.sumFinConstant
    (Relation.transitionPairIncidenceCount d c)

------------------------------------------------------------------------
-- The remaining global fold is explicit and fail-closed.  The block
-- identities above are proved; this target records the additional fold
-- normalization needed to assemble all 11 fibers into row/column identities.

record ConcreteRowColumnSumIdentityTarget (shellIndex : Nat) : Set₁ where
  constructor mkConcreteRowColumnSumIdentityTarget
  field
    rowSumEqualsCandidate :
      (f : Relation.ConcreteNonResidualFiniteIndex shellIndex) ->
      Schur.concreteRowSum f ≡ Schur.concreteRowContribution f
    columnSumEqualsCandidate :
      (t : Relation.ConcreteNonResidualTailIndex shellIndex) ->
      Schur.concreteColumnSum t ≡ Schur.concreteColumnContribution t

open ConcreteRowColumnSumIdentityTarget public

------------------------------------------------------------------------
-- The 11-fiber fold is normalized by congruence rather than `rewrite`.
-- This keeps the dependent Fin fibers explicit while allowing the already
-- proved constant/zero block identities to be composed without postulates.

rowFold : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat
rowFold a b c d e f g h i j k =
  (a + b) + (c + d) + ((e + f) + g) + ((h + i) + (j + k))

columnFold : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat
columnFold a b c d e f g h i j k =
  (a + b) + (c + d) + ((e + f) + g) + ((h + i) + (j + k))

rowFoldCong :
  {a a' b b' c c' d d' e e' f f' g g' h h' i i' j j' k k' : Nat} ->
  a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' ->
  e ≡ e' -> f ≡ f' -> g ≡ g' -> h ≡ h' ->
  i ≡ i' -> j ≡ j' -> k ≡ k' ->
  rowFold a b c d e f g h i j k ≡
  rowFold a' b' c' d' e' f' g' h' i' j' k'
rowFoldCong refl refl refl refl refl refl refl refl refl refl refl = refl

columnFoldCong :
  {a a' b b' c c' d d' e e' f f' g g' h h' i i' j j' k k' : Nat} ->
  a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' ->
  e ≡ e' -> f ≡ f' -> g ≡ g' -> h ≡ h' ->
  i ≡ i' -> j ≡ j' -> k ≡ k' ->
  columnFold a b c d e f g h i j k ≡
  columnFold a' b' c' d' e' f' g' h' i' j' k'
columnFoldCong refl refl refl refl refl refl refl refl refl refl refl = refl

rowFoldAtA : {x : Nat} -> rowFold x 0 0 0 0 0 0 0 0 0 0 ≡ x
rowFoldAtA {x = 0} = refl
rowFoldAtA {x = Nat.suc x} = cong Nat.suc rowFoldAtA

rowFoldAtB : {x : Nat} -> rowFold 0 x 0 0 0 0 0 0 0 0 0 ≡ x
rowFoldAtB {x = 0} = refl
rowFoldAtB {x = Nat.suc x} = cong Nat.suc rowFoldAtB

rowFoldAtC : {x : Nat} -> rowFold 0 0 x 0 0 0 0 0 0 0 0 ≡ x
rowFoldAtC {x = 0} = refl
rowFoldAtC {x = Nat.suc x} = cong Nat.suc rowFoldAtC

rowFoldAtD : {x : Nat} -> rowFold 0 0 0 x 0 0 0 0 0 0 0 ≡ x
rowFoldAtD {x = 0} = refl
rowFoldAtD {x = Nat.suc x} = cong Nat.suc rowFoldAtD

rowFoldAtE : {x : Nat} -> rowFold 0 0 0 0 x 0 0 0 0 0 0 ≡ x
rowFoldAtE {x = 0} = refl
rowFoldAtE {x = Nat.suc x} = cong Nat.suc rowFoldAtE

rowFoldAtF : {x : Nat} -> rowFold 0 0 0 0 0 x 0 0 0 0 0 ≡ x
rowFoldAtF {x = 0} = refl
rowFoldAtF {x = Nat.suc x} = cong Nat.suc rowFoldAtF

rowFoldAtG : {x : Nat} -> rowFold 0 0 0 0 0 0 x 0 0 0 0 ≡ x
rowFoldAtG {x = 0} = refl
rowFoldAtG {x = Nat.suc x} = cong Nat.suc rowFoldAtG

rowFoldAtH : {x : Nat} -> rowFold 0 0 0 0 0 0 0 x 0 0 0 ≡ x
rowFoldAtH {x = 0} = refl
rowFoldAtH {x = Nat.suc x} = cong Nat.suc rowFoldAtH

rowFoldAtI : {x : Nat} -> rowFold 0 0 0 0 0 0 0 0 x 0 0 ≡ x
rowFoldAtI {x = 0} = refl
rowFoldAtI {x = Nat.suc x} = cong Nat.suc rowFoldAtI

rowFoldAtJ : {x : Nat} -> rowFold 0 0 0 0 0 0 0 0 0 x 0 ≡ x
rowFoldAtJ {x = 0} = refl
rowFoldAtJ {x = Nat.suc x} = cong Nat.suc rowFoldAtJ

rowFoldAtK : {x : Nat} -> rowFold 0 0 0 0 0 0 0 0 0 0 x ≡ x
rowFoldAtK {x = 0} = refl
rowFoldAtK {x = Nat.suc x} = cong Nat.suc rowFoldAtK

rawA : {N : Nat} -> Nat
rawA {N} = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.tailEnd N} (λ _ -> 0)
rawB : {N : Nat} -> Nat
rawB {N} = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.nearTail N} (λ _ -> 0)
rawC : {N : Nat} -> Nat
rawC {N} = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.transition N} (λ _ -> 0)
rawD : {N : Nat} -> Nat
rawD {N} = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.degenerate N} (λ _ -> 0)
rawE : {N : Nat} -> Nat
rawE {N} = Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.sparseAdmissible N} (λ _ -> 0)
rawF : {N : Nat} -> Nat
rawF {N} = Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.angularDegenerate N} (λ _ -> 0)
rawG : {N : Nat} -> Nat
rawG {N} = Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.boundarySmallShell N} (λ _ -> 0)
rawH : {N : Nat} -> Nat
rawH {N} = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.thinTransition N} (λ _ -> 0)
rawI : {N : Nat} -> Nat
rawI {N} = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.balancedTransition N} (λ _ -> 0)
rawJ : {N : Nat} -> Nat
rawJ {N} = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.rowThickTransition N} (λ _ -> 0)
rawK : {N : Nat} -> Nat
rawK {N} = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.columnThickTransition N} (λ _ -> 0)

rowA : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowA {N = N} (Relation.forcedTailFiniteIndex c h) with c
... | ForcedTail.tailEnd = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.tailEnd N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex ForcedTail.tailEnd h) (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.tailEnd i))
... | _ = rawA {N = N}
rowA {N = N} (Relation.adversarialFiniteIndex c h) = rawA {N = N}
rowA {N = N} (Relation.transitionFiniteIndex c h) = rawA {N = N}
rowB : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowB {N = N} (Relation.forcedTailFiniteIndex c h) with c
... | ForcedTail.nearTail = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.nearTail N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex ForcedTail.nearTail h) (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.nearTail i))
... | _ = rawB {N = N}
rowB {N = N} (Relation.adversarialFiniteIndex c h) = rawB {N = N}
rowB {N = N} (Relation.transitionFiniteIndex c h) = rawB {N = N}
rowC : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowC {N = N} (Relation.forcedTailFiniteIndex c h) with c
... | ForcedTail.transition = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.transition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex ForcedTail.transition h) (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.transition i))
... | _ = rawC {N = N}
rowC {N = N} (Relation.adversarialFiniteIndex c h) = rawC {N = N}
rowC {N = N} (Relation.transitionFiniteIndex c h) = rawC {N = N}
rowD : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowD {N = N} (Relation.forcedTailFiniteIndex c h) with c
... | ForcedTail.degenerate = Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.degenerate N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex ForcedTail.degenerate h) (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.degenerate i))
... | _ = rawD {N = N}
rowD {N = N} (Relation.adversarialFiniteIndex c h) = rawD {N = N}
rowD {N = N} (Relation.transitionFiniteIndex c h) = rawD {N = N}
rowE : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowE {N = N} (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible h) = Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.sparseAdmissible N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible h) (Relation.adversarialTailIndex {shellIndex = N} Adversarial.sparseAdmissible i))
rowE {N = N} (Relation.forcedTailFiniteIndex c h) = rawE {N = N}
rowE {N = N} (Relation.adversarialFiniteIndex c h) = rawE {N = N}
rowE {N = N} (Relation.transitionFiniteIndex c h) = rawE {N = N}
rowF : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowF {N = N} (Relation.adversarialFiniteIndex Adversarial.angularDegenerate h) = Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.angularDegenerate N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.adversarialFiniteIndex Adversarial.angularDegenerate h) (Relation.adversarialTailIndex {shellIndex = N} Adversarial.angularDegenerate i))
rowF {N = N} (Relation.forcedTailFiniteIndex c h) = rawF {N = N}
rowF {N = N} (Relation.adversarialFiniteIndex c h) = rawF {N = N}
rowF {N = N} (Relation.transitionFiniteIndex c h) = rawF {N = N}
rowG : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowG {N = N} (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell h) = Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.boundarySmallShell N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell h) (Relation.adversarialTailIndex {shellIndex = N} Adversarial.boundarySmallShell i))
rowG {N = N} (Relation.forcedTailFiniteIndex c h) = rawG {N = N}
rowG {N = N} (Relation.adversarialFiniteIndex c h) = rawG {N = N}
rowG {N = N} (Relation.transitionFiniteIndex c h) = rawG {N = N}
rowH : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowH {N = N} (Relation.transitionFiniteIndex Transition.thinTransition h) = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.thinTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex Transition.thinTransition h) (Relation.transitionTailIndex {shellIndex = N} Transition.thinTransition i))
rowH {N = N} (Relation.forcedTailFiniteIndex c h) = rawH {N = N}
rowH {N = N} (Relation.adversarialFiniteIndex c h) = rawH {N = N}
rowH {N = N} (Relation.transitionFiniteIndex c h) = rawH {N = N}
rowI : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowI {N = N} (Relation.transitionFiniteIndex Transition.balancedTransition h) = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.balancedTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex Transition.balancedTransition h) (Relation.transitionTailIndex {shellIndex = N} Transition.balancedTransition i))
rowI {N = N} (Relation.forcedTailFiniteIndex c h) = rawI {N = N}
rowI {N = N} (Relation.adversarialFiniteIndex c h) = rawI {N = N}
rowI {N = N} (Relation.transitionFiniteIndex c h) = rawI {N = N}
rowJ : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowJ {N = N} (Relation.transitionFiniteIndex Transition.rowThickTransition h) = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.rowThickTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex Transition.rowThickTransition h) (Relation.transitionTailIndex {shellIndex = N} Transition.rowThickTransition i))
rowJ {N = N} (Relation.forcedTailFiniteIndex c h) = rawJ {N = N}
rowJ {N = N} (Relation.adversarialFiniteIndex c h) = rawJ {N = N}
rowJ {N = N} (Relation.transitionFiniteIndex c h) = rawJ {N = N}
rowK : {N : Nat} -> Relation.ConcreteNonResidualFiniteIndex N -> Nat
rowK {N = N} (Relation.transitionFiniteIndex Transition.columnThickTransition h) = Schur.sumFin {n = Transition.transitionColumnCountBound Transition.columnThickTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex Transition.columnThickTransition h) (Relation.transitionTailIndex {shellIndex = N} Transition.columnThickTransition i))
rowK {N = N} (Relation.forcedTailFiniteIndex c h) = rawK {N = N}
rowK {N = N} (Relation.adversarialFiniteIndex c h) = rawK {N = N}
rowK {N = N} (Relation.transitionFiniteIndex c h) = rawK {N = N}

concreteRowSumAsFold :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  Schur.concreteRowSum f ≡
  rowFold (rowA f) (rowB f) (rowC f) (rowD f) (rowE f) (rowF f)
    (rowG f) (rowH f) (rowI f) (rowJ f) (rowK f)
concreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.tailEnd h) = refl
concreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.nearTail h) = refl
concreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.transition h) = refl
concreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.degenerate h) = refl
concreteRowSumAsFold
  (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible h) = refl
concreteRowSumAsFold
  (Relation.adversarialFiniteIndex Adversarial.angularDegenerate h) = refl
concreteRowSumAsFold
  (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell h) = refl
concreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.thinTransition h) = refl
concreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.balancedTransition h) = refl
concreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.rowThickTransition h) = refl
concreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.columnThickTransition h) = refl

rowFoldCongFor :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  {a' b' c' d' e' f' g' h' i' j' k' : Nat} ->
  rowA f ≡ a' -> rowB f ≡ b' -> rowC f ≡ c' -> rowD f ≡ d' ->
  rowE f ≡ e' -> rowF f ≡ f' -> rowG f ≡ g' -> rowH f ≡ h' ->
  rowI f ≡ i' -> rowJ f ≡ j' -> rowK f ≡ k' ->
  rowFold (rowA f) (rowB f) (rowC f) (rowD f) (rowE f) (rowF f)
    (rowG f) (rowH f) (rowI f) (rowJ f) (rowK f) ≡
  rowFold a' b' c' d' e' f' g' h' i' j' k'
rowFoldCongFor f refl refl refl refl refl refl refl refl refl refl refl = refl

rowFoldCongForExplicit :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  (a' b' c' d' e' f' g' h' i' j' k' : Nat) ->
  rowA f ≡ a' -> rowB f ≡ b' -> rowC f ≡ c' -> rowD f ≡ d' ->
  rowE f ≡ e' -> rowF f ≡ f' -> rowG f ≡ g' -> rowH f ≡ h' ->
  rowI f ≡ i' -> rowJ f ≡ j' -> rowK f ≡ k' ->
  rowFold (rowA f) (rowB f) (rowC f) (rowD f) (rowE f) (rowF f)
    (rowG f) (rowH f) (rowI f) (rowJ f) (rowK f) ≡
  rowFold a' b' c' d' e' f' g' h' i' j' k'
rowFoldCongForExplicit f a' b' c' d' e' f' g' h' i' j' k'
  refl refl refl refl refl refl refl refl refl refl refl = refl

zeroA : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.tailEnd N}
  (λ _ -> 0) ≡ 0
zeroA {N} = Schur.sumFinZero {n = ForcedTail.forcedTailTailCountBound ForcedTail.tailEnd N}
zeroB : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.nearTail N}
  (λ _ -> 0) ≡ 0
zeroB {N} = Schur.sumFinZero {n = ForcedTail.forcedTailTailCountBound ForcedTail.nearTail N}
zeroC : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.transition N}
  (λ _ -> 0) ≡ 0
zeroC {N} = Schur.sumFinZero {n = ForcedTail.forcedTailTailCountBound ForcedTail.transition N}
zeroD : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailTailCountBound ForcedTail.degenerate N}
  (λ _ -> 0) ≡ 0
zeroD {N} = Schur.sumFinZero {n = ForcedTail.forcedTailTailCountBound ForcedTail.degenerate N}
zeroE : {N : Nat} -> Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.sparseAdmissible N}
  (λ _ -> 0) ≡ 0
zeroE {N} = Schur.sumFinZero {n = Adversarial.adversarialColumnCountBound Adversarial.sparseAdmissible N}
zeroF : {N : Nat} -> Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.angularDegenerate N}
  (λ _ -> 0) ≡ 0
zeroF {N} = Schur.sumFinZero {n = Adversarial.adversarialColumnCountBound Adversarial.angularDegenerate N}
zeroG : {N : Nat} -> Schur.sumFin {n = Adversarial.adversarialColumnCountBound Adversarial.boundarySmallShell N}
  (λ _ -> 0) ≡ 0
zeroG {N} = Schur.sumFinZero {n = Adversarial.adversarialColumnCountBound Adversarial.boundarySmallShell N}
zeroH : {N : Nat} -> Schur.sumFin {n = Transition.transitionColumnCountBound Transition.thinTransition N}
  (λ _ -> 0) ≡ 0
zeroH {N} = Schur.sumFinZero {n = Transition.transitionColumnCountBound Transition.thinTransition N}
zeroI : {N : Nat} -> Schur.sumFin {n = Transition.transitionColumnCountBound Transition.balancedTransition N}
  (λ _ -> 0) ≡ 0
zeroI {N} = Schur.sumFinZero {n = Transition.transitionColumnCountBound Transition.balancedTransition N}
zeroJ : {N : Nat} -> Schur.sumFin {n = Transition.transitionColumnCountBound Transition.rowThickTransition N}
  (λ _ -> 0) ≡ 0
zeroJ {N} = Schur.sumFinZero {n = Transition.transitionColumnCountBound Transition.rowThickTransition N}
zeroK : {N : Nat} -> Schur.sumFin {n = Transition.transitionColumnCountBound Transition.columnThickTransition N}
  (λ _ -> 0) ≡ 0
zeroK {N} = Schur.sumFinZero {n = Transition.transitionColumnCountBound Transition.columnThickTransition N}

------------------------------------------------------------------------
-- Global row/column identities.  The concrete sums use the same fold shape
-- as rowFold/columnFold, so each clause only supplies the class block equalities
-- and zero mismatched blocks.

concreteRowSumEqualsCandidate :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  Schur.concreteRowSum f ≡ Schur.concreteRowContribution f
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.forcedTailFiniteIndex ForcedTail.tailEnd h) =
  trans
    (rowFoldCongForExplicit
      (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.tailEnd h)
      (Relation.forcedTailPairIncidenceCount ForcedTail.tailEnd ForcedTail.tailEnd *
        ForcedTail.forcedTailTailCountBound ForcedTail.tailEnd N)
      0 0 0 0 0 0 0 0 0 0
      (forcedTailRowBlock {N = N} ForcedTail.tailEnd ForcedTail.tailEnd h)
      (zeroB {N = N})
      (zeroC {N = N})
      (zeroD {N = N})
      (zeroE {N = N})
      (zeroF {N = N})
      (zeroG {N = N})
      (zeroH {N = N})
      (zeroI {N = N})
      (zeroJ {N = N})
      (zeroK {N = N}))
    (trans rowFoldAtA refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.forcedTailFiniteIndex ForcedTail.nearTail h) =
  trans
    (rowFoldCongFor
      (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.nearTail h)
      {a' = 0}
      {b' = Relation.forcedTailPairIncidenceCount ForcedTail.nearTail ForcedTail.nearTail *
        ForcedTail.forcedTailTailCountBound ForcedTail.nearTail N}
      {c' = 0} {d' = 0} {e' = 0} {f' = 0}
      {g' = 0} {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (zeroA {N = N})
      (forcedTailRowBlock ForcedTail.nearTail ForcedTail.nearTail h)
      (zeroC {N = N}) (zeroD {N = N}) (zeroE {N = N})
      (zeroF {N = N}) (zeroG {N = N}) (zeroH {N = N})
      (zeroI {N = N}) (zeroJ {N = N}) (zeroK {N = N}))
    (trans rowFoldAtB refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.forcedTailFiniteIndex ForcedTail.transition h) =
  trans
    (rowFoldCongFor
      (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.transition h)
      {a' = 0} {b' = 0}
      {c' = Relation.forcedTailPairIncidenceCount ForcedTail.transition ForcedTail.transition *
        ForcedTail.forcedTailTailCountBound ForcedTail.transition N}
      {d' = 0} {e' = 0} {f' = 0} {g' = 0}
      {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (zeroA {N = N}) (zeroB {N = N})
      (forcedTailRowBlock ForcedTail.transition ForcedTail.transition h)
      (zeroD {N = N}) (zeroE {N = N}) (zeroF {N = N})
      (zeroG {N = N}) (zeroH {N = N}) (zeroI {N = N})
      (zeroJ {N = N}) (zeroK {N = N}))
    (trans rowFoldAtC refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.forcedTailFiniteIndex ForcedTail.degenerate h) =
  trans
    (rowFoldCongFor
      (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.degenerate h)
      {a' = 0} {b' = 0} {c' = 0}
      {d' = Relation.forcedTailPairIncidenceCount ForcedTail.degenerate ForcedTail.degenerate *
        ForcedTail.forcedTailTailCountBound ForcedTail.degenerate N}
      {e' = 0} {f' = 0} {g' = 0} {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N})
      (forcedTailRowBlock {N = N} ForcedTail.degenerate ForcedTail.degenerate h)
      (zeroE {N = N}) (zeroF {N = N}) (zeroG {N = N})
      (zeroH {N = N}) (zeroI {N = N}) (zeroJ {N = N})
      (zeroK {N = N}))
    (trans rowFoldAtD refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible h) =
  trans
    (rowFoldCongFor
      (Relation.adversarialFiniteIndex {shellIndex = N} Adversarial.sparseAdmissible h)
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N}) (zeroD {N = N})
      (adversarialRowBlock Adversarial.sparseAdmissible Adversarial.sparseAdmissible h)
      (zeroF {N = N}) (zeroG {N = N}) (zeroH {N = N})
      (zeroI {N = N}) (zeroJ {N = N}) (zeroK {N = N}))
    (trans rowFoldAtE refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.adversarialFiniteIndex Adversarial.angularDegenerate h) =
  trans
    (rowFoldCongFor
      (Relation.adversarialFiniteIndex {shellIndex = N} Adversarial.angularDegenerate h)
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N})
      (zeroD {N = N}) (zeroE {N = N})
      (adversarialRowBlock Adversarial.angularDegenerate Adversarial.angularDegenerate h)
      (zeroG {N = N}) (zeroH {N = N}) (zeroI {N = N})
      (zeroJ {N = N}) (zeroK {N = N}))
    (trans rowFoldAtF refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell h) =
  trans
    (rowFoldCongFor
      (Relation.adversarialFiniteIndex {shellIndex = N} Adversarial.boundarySmallShell h)
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N})
      (zeroD {N = N}) (zeroE {N = N}) (zeroF {N = N})
      (adversarialRowBlock {N = N} Adversarial.boundarySmallShell Adversarial.boundarySmallShell h)
      (zeroH {N = N}) (zeroI {N = N}) (zeroJ {N = N})
      (zeroK {N = N}))
    (trans rowFoldAtG refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.transitionFiniteIndex Transition.thinTransition h) =
  trans
    (rowFoldCongFor
      (Relation.transitionFiniteIndex {shellIndex = N} Transition.thinTransition h)
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N})
      (zeroD {N = N}) (zeroE {N = N}) (zeroF {N = N})
      (zeroG {N = N})
      (transitionRowBlock Transition.thinTransition Transition.thinTransition h)
      (zeroI {N = N}) (zeroJ {N = N}) (zeroK {N = N}))
    (trans rowFoldAtH refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.transitionFiniteIndex Transition.balancedTransition h) =
  trans
    (rowFoldCongFor
      (Relation.transitionFiniteIndex {shellIndex = N} Transition.balancedTransition h)
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N})
      (zeroD {N = N}) (zeroE {N = N}) (zeroF {N = N})
      (zeroG {N = N}) (zeroH {N = N})
      (transitionRowBlock Transition.balancedTransition Transition.balancedTransition h)
      (zeroJ {N = N}) (zeroK {N = N}))
    (trans rowFoldAtI refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.transitionFiniteIndex Transition.rowThickTransition h) =
  trans
    (rowFoldCongFor
      (Relation.transitionFiniteIndex {shellIndex = N} Transition.rowThickTransition h)
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N})
      (zeroD {N = N}) (zeroE {N = N}) (zeroF {N = N})
      (zeroG {N = N}) (zeroH {N = N}) (zeroI {N = N})
      (transitionRowBlock Transition.rowThickTransition Transition.rowThickTransition h)
      (zeroK {N = N}))
    (trans rowFoldAtJ refl)
concreteRowSumEqualsCandidate
  {N = N}
  (Relation.transitionFiniteIndex Transition.columnThickTransition h) =
  trans
    (rowFoldCongFor
      (Relation.transitionFiniteIndex {shellIndex = N} Transition.columnThickTransition h)
      (zeroA {N = N}) (zeroB {N = N}) (zeroC {N = N})
      (zeroD {N = N}) (zeroE {N = N}) (zeroF {N = N})
      (zeroG {N = N}) (zeroH {N = N}) (zeroI {N = N})
      (zeroJ {N = N})
      (transitionRowBlock Transition.columnThickTransition Transition.columnThickTransition h))
    (trans rowFoldAtK refl)

------------------------------------------------------------------------
-- The column fold is the dual 11-fiber calculation.  Its finite fibers use
-- head-count bounds rather than tail-count bounds.

colRawA : {N : Nat} -> Nat
colRawA {N} = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.tailEnd N} (λ _ -> 0)
colRawB : {N : Nat} -> Nat
colRawB {N} = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.nearTail N} (λ _ -> 0)
colRawC : {N : Nat} -> Nat
colRawC {N} = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.transition N} (λ _ -> 0)
colRawD : {N : Nat} -> Nat
colRawD {N} = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.degenerate N} (λ _ -> 0)
colRawE : {N : Nat} -> Nat
colRawE {N} = Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.sparseAdmissible N} (λ _ -> 0)
colRawF : {N : Nat} -> Nat
colRawF {N} = Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.angularDegenerate N} (λ _ -> 0)
colRawG : {N : Nat} -> Nat
colRawG {N} = Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.boundarySmallShell N} (λ _ -> 0)
colRawH : {N : Nat} -> Nat
colRawH {N} = Schur.sumFin {n = Transition.transitionRowCountBound Transition.thinTransition N} (λ _ -> 0)
colRawI : {N : Nat} -> Nat
colRawI {N} = Schur.sumFin {n = Transition.transitionRowCountBound Transition.balancedTransition N} (λ _ -> 0)
colRawJ : {N : Nat} -> Nat
colRawJ {N} = Schur.sumFin {n = Transition.transitionRowCountBound Transition.rowThickTransition N} (λ _ -> 0)
colRawK : {N : Nat} -> Nat
colRawK {N} = Schur.sumFin {n = Transition.transitionRowCountBound Transition.columnThickTransition N} (λ _ -> 0)

colA : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colA {N = N} (Relation.forcedTailTailIndex c h) with c
... | ForcedTail.tailEnd = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.tailEnd N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.tailEnd i) (Relation.forcedTailTailIndex ForcedTail.tailEnd h))
... | _ = colRawA {N = N}
colA {N = N} (Relation.adversarialTailIndex c h) = colRawA {N = N}
colA {N = N} (Relation.transitionTailIndex c h) = colRawA {N = N}
colB : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colB {N = N} (Relation.forcedTailTailIndex c h) with c
... | ForcedTail.nearTail = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.nearTail N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.nearTail i) (Relation.forcedTailTailIndex ForcedTail.nearTail h))
... | _ = colRawB {N = N}
colB {N = N} (Relation.adversarialTailIndex c h) = colRawB {N = N}
colB {N = N} (Relation.transitionTailIndex c h) = colRawB {N = N}
colC : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colC {N = N} (Relation.forcedTailTailIndex c h) with c
... | ForcedTail.transition = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.transition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.transition i) (Relation.forcedTailTailIndex ForcedTail.transition h))
... | _ = colRawC {N = N}
colC {N = N} (Relation.adversarialTailIndex c h) = colRawC {N = N}
colC {N = N} (Relation.transitionTailIndex c h) = colRawC {N = N}
colD : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colD {N = N} (Relation.forcedTailTailIndex c h) with c
... | ForcedTail.degenerate = Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.degenerate N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.forcedTailFiniteIndex {shellIndex = N} ForcedTail.degenerate i) (Relation.forcedTailTailIndex ForcedTail.degenerate h))
... | _ = colRawD {N = N}
colD {N = N} (Relation.adversarialTailIndex c h) = colRawD {N = N}
colD {N = N} (Relation.transitionTailIndex c h) = colRawD {N = N}
colE : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colE {N = N} (Relation.adversarialTailIndex Adversarial.sparseAdmissible h) = Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.sparseAdmissible N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.adversarialFiniteIndex {shellIndex = N} Adversarial.sparseAdmissible i) (Relation.adversarialTailIndex Adversarial.sparseAdmissible h))
colE {N = N} (Relation.forcedTailTailIndex c h) = colRawE {N = N}
colE {N = N} (Relation.adversarialTailIndex c h) = colRawE {N = N}
colE {N = N} (Relation.transitionTailIndex c h) = colRawE {N = N}
colF : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colF {N = N} (Relation.adversarialTailIndex Adversarial.angularDegenerate h) = Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.angularDegenerate N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.adversarialFiniteIndex {shellIndex = N} Adversarial.angularDegenerate i) (Relation.adversarialTailIndex Adversarial.angularDegenerate h))
colF {N = N} (Relation.forcedTailTailIndex c h) = colRawF {N = N}
colF {N = N} (Relation.adversarialTailIndex c h) = colRawF {N = N}
colF {N = N} (Relation.transitionTailIndex c h) = colRawF {N = N}
colG : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colG {N = N} (Relation.adversarialTailIndex Adversarial.boundarySmallShell h) = Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.boundarySmallShell N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.adversarialFiniteIndex {shellIndex = N} Adversarial.boundarySmallShell i) (Relation.adversarialTailIndex Adversarial.boundarySmallShell h))
colG {N = N} (Relation.forcedTailTailIndex c h) = colRawG {N = N}
colG {N = N} (Relation.adversarialTailIndex c h) = colRawG {N = N}
colG {N = N} (Relation.transitionTailIndex c h) = colRawG {N = N}
colH : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colH {N = N} (Relation.transitionTailIndex Transition.thinTransition h) = Schur.sumFin {n = Transition.transitionRowCountBound Transition.thinTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex {shellIndex = N} Transition.thinTransition i) (Relation.transitionTailIndex Transition.thinTransition h))
colH {N = N} (Relation.forcedTailTailIndex c h) = colRawH {N = N}
colH {N = N} (Relation.adversarialTailIndex c h) = colRawH {N = N}
colH {N = N} (Relation.transitionTailIndex c h) = colRawH {N = N}
colI : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colI {N = N} (Relation.transitionTailIndex Transition.balancedTransition h) = Schur.sumFin {n = Transition.transitionRowCountBound Transition.balancedTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex {shellIndex = N} Transition.balancedTransition i) (Relation.transitionTailIndex Transition.balancedTransition h))
colI {N = N} (Relation.forcedTailTailIndex c h) = colRawI {N = N}
colI {N = N} (Relation.adversarialTailIndex c h) = colRawI {N = N}
colI {N = N} (Relation.transitionTailIndex c h) = colRawI {N = N}
colJ : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colJ {N = N} (Relation.transitionTailIndex Transition.rowThickTransition h) = Schur.sumFin {n = Transition.transitionRowCountBound Transition.rowThickTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex {shellIndex = N} Transition.rowThickTransition i) (Relation.transitionTailIndex Transition.rowThickTransition h))
colJ {N = N} (Relation.forcedTailTailIndex c h) = colRawJ {N = N}
colJ {N = N} (Relation.adversarialTailIndex c h) = colRawJ {N = N}
colJ {N = N} (Relation.transitionTailIndex c h) = colRawJ {N = N}
colK : {N : Nat} -> Relation.ConcreteNonResidualTailIndex N -> Nat
colK {N = N} (Relation.transitionTailIndex Transition.columnThickTransition h) = Schur.sumFin {n = Transition.transitionRowCountBound Transition.columnThickTransition N} (λ i -> Relation.concreteNonResidualPairIncidenceCount
  (Relation.transitionFiniteIndex {shellIndex = N} Transition.columnThickTransition i) (Relation.transitionTailIndex Transition.columnThickTransition h))
colK {N = N} (Relation.forcedTailTailIndex c h) = colRawK {N = N}
colK {N = N} (Relation.adversarialTailIndex c h) = colRawK {N = N}
colK {N = N} (Relation.transitionTailIndex c h) = colRawK {N = N}

------------------------------------------------------------------------
-- Weighted concrete sums.  The current canonical source and target weights
-- are both the unit weight; keep them explicit so the rectangular kernel and
-- the two sides of the bipartite fold remain visible in the definition.

concreteRectangularKernel :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Relation.ConcreteNonResidualTailIndex N ->
  Nat
concreteRectangularKernel = Relation.concreteNonResidualPairIncidenceCount

sourceWeight :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
sourceWeight _ = 1

targetWeight :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
targetWeight _ = 1

------------------------------------------------------------------------
-- General weighted expressions.  The legacy unit-weight names above are
-- retained for the already-checked finite receipt surface; these aliases
-- expose the actual Schur expressions to the analytic lane.

generalWeightedConcreteRowSum :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
generalWeightedConcreteRowSum = WeightedFibers.weightedConcreteRowSum

generalWeightedConcreteColumnSum :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
generalWeightedConcreteColumnSum = WeightedFibers.weightedConcreteColumnSum

generalWeightedRowCandidate :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
generalWeightedRowCandidate = WeightedFibers.weightedRowCandidate

generalWeightedColumnCandidate :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
generalWeightedColumnCandidate = WeightedFibers.weightedColumnCandidate

generalWeightedRowBlockFactorization =
  WeightedFibers.weightedForcedTailRowBlock

generalWeightedColumnBlockFactorization =
  WeightedFibers.weightedForcedTailColumnBlock

generalWeightedRowSumNormalForm =
  WeightedFibers.weightedConcreteRowSumNormalForm

generalWeightedColumnSumNormalForm =
  WeightedFibers.weightedConcreteColumnSumNormalForm

------------------------------------------------------------------------
-- Corrected-refinement adapters.
--
-- The general aliases above already accept arbitrary source/target weight
-- functions.  These typed specializations connect them to the corrected
-- concrete classifier/refinement surface without asserting a Schur bound.
-- The two orientation lemmas below are pointwise consequences of supplied
-- refinement premises; they do not close either weighted decay obligation.
------------------------------------------------------------------------

correctedSourceWeight :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
correctedSourceWeight f =
  WeightModel.weightOf (ConcreteBridge.sourceEntryCode f)

correctedTargetWeight :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
correctedTargetWeight t =
  WeightModel.weightOf (ConcreteBridge.targetEntryCode t)

correctedGeneralWeightedConcreteRowSum :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
correctedGeneralWeightedConcreteRowSum f =
  generalWeightedConcreteRowSum correctedTargetWeight f

correctedGeneralWeightedConcreteColumnSum :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
correctedGeneralWeightedConcreteColumnSum t =
  generalWeightedConcreteColumnSum correctedSourceWeight t

correctedGeneralWeightedRowCandidate :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
correctedGeneralWeightedRowCandidate f =
  generalWeightedRowCandidate correctedTargetWeight f

correctedGeneralWeightedColumnCandidate :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
correctedGeneralWeightedColumnCandidate t =
  generalWeightedColumnCandidate correctedSourceWeight t

correctedGeneralWeightedRowSumAlias :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  correctedGeneralWeightedConcreteRowSum f
    ≡ WeightedFibers.weightedConcreteRowSum correctedTargetWeight f
correctedGeneralWeightedRowSumAlias f = refl

correctedGeneralWeightedColumnSumAlias :
  {N : Nat} ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  correctedGeneralWeightedConcreteColumnSum t
    ≡ WeightedFibers.weightedConcreteColumnSum correctedSourceWeight t
correctedGeneralWeightedColumnSumAlias t = refl

correctedGeneralWeightedRowCandidateAlias :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  correctedGeneralWeightedRowCandidate f
    ≡ WeightedFibers.weightedRowCandidate correctedTargetWeight f
correctedGeneralWeightedRowCandidateAlias f = refl

correctedGeneralWeightedColumnCandidateAlias :
  {N : Nat} ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  correctedGeneralWeightedColumnCandidate t
    ≡ WeightedFibers.weightedColumnCandidate correctedSourceWeight t
correctedGeneralWeightedColumnCandidateAlias t = refl

correctedFTToAdversarialRowWeightOrientation :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  {h : ForcedTailType.ForcedTailHead c N} ->
  {d : Adversarial.AdversarialClass} ->
  {t : AdversarialType.AdversarialTail d N} ->
  CorrectedRefinement.CorrectedFTToAdversarialIncidence N c h d t ->
  suc N * correctedTargetWeight
    (Relation.adversarialTailIndex d t)
    ≤ correctedSourceWeight
      (Relation.forcedTailFiniteIndex c h)
correctedFTToAdversarialRowWeightOrientation inc =
  CorrectedRefinement.correctedFTToAdversarialWeightOrientationFromIncidence
    inc

correctedFTToTransitionRowWeightOrientation :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  {h : ForcedTailType.ForcedTailHead c N} ->
  {d : Transition.TransitionClass} ->
  {t : TransitionType.TransitionTail d N} ->
  CorrectedRefinement.CorrectedFTToTransitionIncidence N c h d t ->
  suc N * correctedTargetWeight
    (Relation.transitionTailIndex d t)
    ≤ correctedSourceWeight
      (Relation.forcedTailFiniteIndex c h)
correctedFTToTransitionRowWeightOrientation inc =
  CorrectedRefinement.correctedFTToTransitionWeightOrientationFromIncidence
    inc

correctedFTToAdversarialRowWeightOrientationFromPremises :
  {N : Nat} ->
  CorrectedRefinement.CorrectedConcreteRefinementPremises N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialType.AdversarialTail d N) ->
  suc N * correctedTargetWeight
    (Relation.adversarialTailIndex d t)
    ≤ correctedSourceWeight
      (Relation.forcedTailFiniteIndex c h)
correctedFTToAdversarialRowWeightOrientationFromPremises premises c h d t =
  correctedFTToAdversarialRowWeightOrientation
    (CorrectedRefinement.CorrectedConcreteRefinementPremises.ftToAdversarial
      premises c h d t)

correctedFTToTransitionRowWeightOrientationFromPremises :
  {N : Nat} ->
  CorrectedRefinement.CorrectedConcreteRefinementPremises N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionType.TransitionTail d N) ->
  suc N * correctedTargetWeight
    (Relation.transitionTailIndex d t)
    ≤ correctedSourceWeight
      (Relation.forcedTailFiniteIndex c h)
correctedFTToTransitionRowWeightOrientationFromPremises premises c h d t =
  correctedFTToTransitionRowWeightOrientation
    (CorrectedRefinement.CorrectedConcreteRefinementPremises.ftToTransition
      premises c h d t)

weightedRowContribution :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
weightedRowContribution = Schur.concreteRowContribution

weightedColumnContribution :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
weightedColumnContribution = Schur.concreteColumnContribution

weightedConcreteRowSum :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
weightedConcreteRowSum f =
  Schur.concreteTailSum
    (λ t -> concreteRectangularKernel f t * targetWeight t)

weightedConcreteColumnSum :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
weightedConcreteColumnSum t =
  Schur.concreteFiniteSum
    (λ f -> concreteRectangularKernel f t * sourceWeight f)

weightedConcreteRowSumAsFold :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  weightedConcreteRowSum f ≡
  rowFold (rowA f) (rowB f) (rowC f) (rowD f) (rowE f) (rowF f)
    (rowG f) (rowH f) (rowI f) (rowJ f) (rowK f)
weightedConcreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.tailEnd h) = refl
weightedConcreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.nearTail h) = refl
weightedConcreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.transition h) = refl
weightedConcreteRowSumAsFold
  (Relation.forcedTailFiniteIndex ForcedTail.degenerate h) = refl
weightedConcreteRowSumAsFold
  (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible h) = refl
weightedConcreteRowSumAsFold
  (Relation.adversarialFiniteIndex Adversarial.angularDegenerate h) = refl
weightedConcreteRowSumAsFold
  (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell h) = refl
weightedConcreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.thinTransition h) = refl
weightedConcreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.balancedTransition h) = refl
weightedConcreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.rowThickTransition h) = refl
weightedConcreteRowSumAsFold
  (Relation.transitionFiniteIndex Transition.columnThickTransition h) = refl

weightedConcreteColumnSumAsFold :
  {N : Nat} ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  weightedConcreteColumnSum t ≡
  columnFold (colA t) (colB t) (colC t) (colD t) (colE t) (colF t)
    (colG t) (colH t) (colI t) (colJ t) (colK t)
weightedConcreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.tailEnd h) = refl
weightedConcreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.nearTail h) = refl
weightedConcreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.transition h) = refl
weightedConcreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.degenerate h) = refl
weightedConcreteColumnSumAsFold
  (Relation.adversarialTailIndex Adversarial.sparseAdmissible h) = refl
weightedConcreteColumnSumAsFold
  (Relation.adversarialTailIndex Adversarial.angularDegenerate h) = refl
weightedConcreteColumnSumAsFold
  (Relation.adversarialTailIndex Adversarial.boundarySmallShell h) = refl
weightedConcreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.thinTransition h) = refl
weightedConcreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.balancedTransition h) = refl
weightedConcreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.rowThickTransition h) = refl
weightedConcreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.columnThickTransition h) = refl

concreteColumnSumAsFold :
  {N : Nat} ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  Schur.concreteColumnSum t ≡
  columnFold (colA t) (colB t) (colC t) (colD t) (colE t) (colF t)
    (colG t) (colH t) (colI t) (colJ t) (colK t)
concreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.tailEnd h) = refl
concreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.nearTail h) = refl
concreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.transition h) = refl
concreteColumnSumAsFold
  (Relation.forcedTailTailIndex ForcedTail.degenerate h) = refl
concreteColumnSumAsFold
  (Relation.adversarialTailIndex Adversarial.sparseAdmissible h) = refl
concreteColumnSumAsFold
  (Relation.adversarialTailIndex Adversarial.angularDegenerate h) = refl
concreteColumnSumAsFold
  (Relation.adversarialTailIndex Adversarial.boundarySmallShell h) = refl
concreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.thinTransition h) = refl
concreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.balancedTransition h) = refl
concreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.rowThickTransition h) = refl
concreteColumnSumAsFold
  (Relation.transitionTailIndex Transition.columnThickTransition h) = refl

columnFoldAtA : {x : Nat} -> columnFold x 0 0 0 0 0 0 0 0 0 0 ≡ x
columnFoldAtA {x = 0} = refl
columnFoldAtA {x = Nat.suc x} = cong Nat.suc columnFoldAtA
columnFoldAtB : {x : Nat} -> columnFold 0 x 0 0 0 0 0 0 0 0 0 ≡ x
columnFoldAtB {x = 0} = refl
columnFoldAtB {x = Nat.suc x} = cong Nat.suc columnFoldAtB
columnFoldAtC : {x : Nat} -> columnFold 0 0 x 0 0 0 0 0 0 0 0 ≡ x
columnFoldAtC {x = 0} = refl
columnFoldAtC {x = Nat.suc x} = cong Nat.suc columnFoldAtC
columnFoldAtD : {x : Nat} -> columnFold 0 0 0 x 0 0 0 0 0 0 0 ≡ x
columnFoldAtD {x = 0} = refl
columnFoldAtD {x = Nat.suc x} = cong Nat.suc columnFoldAtD
columnFoldAtE : {x : Nat} -> columnFold 0 0 0 0 x 0 0 0 0 0 0 ≡ x
columnFoldAtE {x = 0} = refl
columnFoldAtE {x = Nat.suc x} = cong Nat.suc columnFoldAtE
columnFoldAtF : {x : Nat} -> columnFold 0 0 0 0 0 x 0 0 0 0 0 ≡ x
columnFoldAtF {x = 0} = refl
columnFoldAtF {x = Nat.suc x} = cong Nat.suc columnFoldAtF
columnFoldAtG : {x : Nat} -> columnFold 0 0 0 0 0 0 x 0 0 0 0 ≡ x
columnFoldAtG {x = 0} = refl
columnFoldAtG {x = Nat.suc x} = cong Nat.suc columnFoldAtG
columnFoldAtH : {x : Nat} -> columnFold 0 0 0 0 0 0 0 x 0 0 0 ≡ x
columnFoldAtH {x = 0} = refl
columnFoldAtH {x = Nat.suc x} = cong Nat.suc columnFoldAtH
columnFoldAtI : {x : Nat} -> columnFold 0 0 0 0 0 0 0 0 x 0 0 ≡ x
columnFoldAtI {x = 0} = refl
columnFoldAtI {x = Nat.suc x} = cong Nat.suc columnFoldAtI
columnFoldAtJ : {x : Nat} -> columnFold 0 0 0 0 0 0 0 0 0 x 0 ≡ x
columnFoldAtJ {x = 0} = refl
columnFoldAtJ {x = Nat.suc x} = cong Nat.suc columnFoldAtJ
columnFoldAtK : {x : Nat} -> columnFold 0 0 0 0 0 0 0 0 0 0 x ≡ x
columnFoldAtK {x = 0} = refl
columnFoldAtK {x = Nat.suc x} = cong Nat.suc columnFoldAtK

columnFoldCongFor :
  {N : Nat} ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  {a' b' c' d' e' f' g' h' i' j' k' : Nat} ->
  colA t ≡ a' -> colB t ≡ b' -> colC t ≡ c' -> colD t ≡ d' ->
  colE t ≡ e' -> colF t ≡ f' -> colG t ≡ g' -> colH t ≡ h' ->
  colI t ≡ i' -> colJ t ≡ j' -> colK t ≡ k' ->
  columnFold (colA t) (colB t) (colC t) (colD t) (colE t) (colF t)
    (colG t) (colH t) (colI t) (colJ t) (colK t) ≡
  columnFold a' b' c' d' e' f' g' h' i' j' k'
columnFoldCongFor t refl refl refl refl refl refl refl refl refl refl refl = refl

colZeroA : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.tailEnd N} (λ _ -> 0) ≡ 0
colZeroA {N} = Schur.sumFinZero {n = ForcedTail.forcedTailHeadCountBound ForcedTail.tailEnd N}
colZeroB : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.nearTail N} (λ _ -> 0) ≡ 0
colZeroB {N} = Schur.sumFinZero {n = ForcedTail.forcedTailHeadCountBound ForcedTail.nearTail N}
colZeroC : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.transition N} (λ _ -> 0) ≡ 0
colZeroC {N} = Schur.sumFinZero {n = ForcedTail.forcedTailHeadCountBound ForcedTail.transition N}
colZeroD : {N : Nat} -> Schur.sumFin {n = ForcedTail.forcedTailHeadCountBound ForcedTail.degenerate N} (λ _ -> 0) ≡ 0
colZeroD {N} = Schur.sumFinZero {n = ForcedTail.forcedTailHeadCountBound ForcedTail.degenerate N}
colZeroE : {N : Nat} -> Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.sparseAdmissible N} (λ _ -> 0) ≡ 0
colZeroE {N} = Schur.sumFinZero {n = Adversarial.adversarialRowCountBound Adversarial.sparseAdmissible N}
colZeroF : {N : Nat} -> Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.angularDegenerate N} (λ _ -> 0) ≡ 0
colZeroF {N} = Schur.sumFinZero {n = Adversarial.adversarialRowCountBound Adversarial.angularDegenerate N}
colZeroG : {N : Nat} -> Schur.sumFin {n = Adversarial.adversarialRowCountBound Adversarial.boundarySmallShell N} (λ _ -> 0) ≡ 0
colZeroG {N} = Schur.sumFinZero {n = Adversarial.adversarialRowCountBound Adversarial.boundarySmallShell N}
colZeroH : {N : Nat} -> Schur.sumFin {n = Transition.transitionRowCountBound Transition.thinTransition N} (λ _ -> 0) ≡ 0
colZeroH {N} = Schur.sumFinZero {n = Transition.transitionRowCountBound Transition.thinTransition N}
colZeroI : {N : Nat} -> Schur.sumFin {n = Transition.transitionRowCountBound Transition.balancedTransition N} (λ _ -> 0) ≡ 0
colZeroI {N} = Schur.sumFinZero {n = Transition.transitionRowCountBound Transition.balancedTransition N}
colZeroJ : {N : Nat} -> Schur.sumFin {n = Transition.transitionRowCountBound Transition.rowThickTransition N} (λ _ -> 0) ≡ 0
colZeroJ {N} = Schur.sumFinZero {n = Transition.transitionRowCountBound Transition.rowThickTransition N}
colZeroK : {N : Nat} -> Schur.sumFin {n = Transition.transitionRowCountBound Transition.columnThickTransition N} (λ _ -> 0) ≡ 0
colZeroK {N} = Schur.sumFinZero {n = Transition.transitionRowCountBound Transition.columnThickTransition N}

concreteColumnSumEqualsCandidate :
  {N : Nat} ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  Schur.concreteColumnSum t ≡ Schur.concreteColumnContribution t
concreteColumnSumEqualsCandidate
  {N = N} (Relation.forcedTailTailIndex ForcedTail.tailEnd h) =
  trans
    (columnFoldCongFor
      (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.tailEnd h)
      {a' = Relation.forcedTailPairIncidenceCount ForcedTail.tailEnd ForcedTail.tailEnd *
        ForcedTail.forcedTailHeadCountBound ForcedTail.tailEnd N}
      {b' = 0} {c' = 0} {d' = 0} {e' = 0} {f' = 0}
      {g' = 0} {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (forcedTailColumnBlock {N = N} ForcedTail.tailEnd ForcedTail.tailEnd h)
      (colZeroB {N = N}) (colZeroC {N = N}) (colZeroD {N = N})
      (colZeroE {N = N}) (colZeroF {N = N}) (colZeroG {N = N})
      (colZeroH {N = N}) (colZeroI {N = N}) (colZeroJ {N = N})
      (colZeroK {N = N}))
    (trans columnFoldAtA refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.forcedTailTailIndex ForcedTail.nearTail h) =
  trans
    (columnFoldCongFor
      (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.nearTail h)
      {a' = 0}
      {b' = Relation.forcedTailPairIncidenceCount ForcedTail.nearTail ForcedTail.nearTail *
        ForcedTail.forcedTailHeadCountBound ForcedTail.nearTail N}
      {c' = 0} {d' = 0} {e' = 0} {f' = 0}
      {g' = 0} {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (colZeroA {N = N})
      (forcedTailColumnBlock {N = N} ForcedTail.nearTail ForcedTail.nearTail h)
      (colZeroC {N = N}) (colZeroD {N = N}) (colZeroE {N = N})
      (colZeroF {N = N}) (colZeroG {N = N}) (colZeroH {N = N})
      (colZeroI {N = N}) (colZeroJ {N = N}) (colZeroK {N = N}))
    (trans columnFoldAtB refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.forcedTailTailIndex ForcedTail.transition h) =
  trans
    (columnFoldCongFor
      (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.transition h)
      {a' = 0} {b' = 0}
      {c' = Relation.forcedTailPairIncidenceCount ForcedTail.transition ForcedTail.transition *
        ForcedTail.forcedTailHeadCountBound ForcedTail.transition N}
      {d' = 0} {e' = 0} {f' = 0} {g' = 0}
      {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N})
      (forcedTailColumnBlock {N = N} ForcedTail.transition ForcedTail.transition h)
      (colZeroD {N = N}) (colZeroE {N = N}) (colZeroF {N = N})
      (colZeroG {N = N}) (colZeroH {N = N}) (colZeroI {N = N})
      (colZeroJ {N = N}) (colZeroK {N = N}))
    (trans columnFoldAtC refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.forcedTailTailIndex ForcedTail.degenerate h) =
  trans
    (columnFoldCongFor
      (Relation.forcedTailTailIndex {shellIndex = N} ForcedTail.degenerate h)
      {a' = 0} {b' = 0} {c' = 0}
      {d' = Relation.forcedTailPairIncidenceCount ForcedTail.degenerate ForcedTail.degenerate *
        ForcedTail.forcedTailHeadCountBound ForcedTail.degenerate N}
      {e' = 0} {f' = 0} {g' = 0} {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (forcedTailColumnBlock {N = N} ForcedTail.degenerate ForcedTail.degenerate h)
      (colZeroE {N = N}) (colZeroF {N = N}) (colZeroG {N = N})
      (colZeroH {N = N}) (colZeroI {N = N}) (colZeroJ {N = N})
      (colZeroK {N = N}))
    (trans columnFoldAtD refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.adversarialTailIndex Adversarial.sparseAdmissible h) =
  trans
    (columnFoldCongFor
      (Relation.adversarialTailIndex {shellIndex = N} Adversarial.sparseAdmissible h)
      {a' = 0} {b' = 0} {c' = 0} {d' = 0}
      {e' = Relation.adversarialPairIncidenceCount Adversarial.sparseAdmissible Adversarial.sparseAdmissible *
        Adversarial.adversarialRowCountBound Adversarial.sparseAdmissible N}
      {f' = 0} {g' = 0} {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (colZeroD {N = N})
      (adversarialColumnBlock {N = N} Adversarial.sparseAdmissible Adversarial.sparseAdmissible h)
      (colZeroF {N = N}) (colZeroG {N = N}) (colZeroH {N = N})
      (colZeroI {N = N}) (colZeroJ {N = N}) (colZeroK {N = N}))
    (trans columnFoldAtE refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.adversarialTailIndex Adversarial.angularDegenerate h) =
  trans
    (columnFoldCongFor
      (Relation.adversarialTailIndex {shellIndex = N} Adversarial.angularDegenerate h)
      {a' = 0} {b' = 0} {c' = 0} {d' = 0} {e' = 0}
      {f' = Relation.adversarialPairIncidenceCount Adversarial.angularDegenerate Adversarial.angularDegenerate *
        Adversarial.adversarialRowCountBound Adversarial.angularDegenerate N}
      {g' = 0} {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (colZeroD {N = N}) (colZeroE {N = N})
      (adversarialColumnBlock {N = N} Adversarial.angularDegenerate Adversarial.angularDegenerate h)
      (colZeroG {N = N}) (colZeroH {N = N}) (colZeroI {N = N})
      (colZeroJ {N = N}) (colZeroK {N = N}))
    (trans columnFoldAtF refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.adversarialTailIndex Adversarial.boundarySmallShell h) =
  trans
    (columnFoldCongFor
      (Relation.adversarialTailIndex {shellIndex = N} Adversarial.boundarySmallShell h)
      {a' = 0} {b' = 0} {c' = 0} {d' = 0} {e' = 0} {f' = 0}
      {g' = Relation.adversarialPairIncidenceCount Adversarial.boundarySmallShell Adversarial.boundarySmallShell *
        Adversarial.adversarialRowCountBound Adversarial.boundarySmallShell N}
      {h' = 0} {i' = 0} {j' = 0} {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (colZeroD {N = N}) (colZeroE {N = N}) (colZeroF {N = N})
      (adversarialColumnBlock {N = N} Adversarial.boundarySmallShell Adversarial.boundarySmallShell h)
      (colZeroH {N = N}) (colZeroI {N = N}) (colZeroJ {N = N})
      (colZeroK {N = N}))
    (trans columnFoldAtG refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.transitionTailIndex Transition.thinTransition h) =
  trans
    (columnFoldCongFor
      (Relation.transitionTailIndex {shellIndex = N} Transition.thinTransition h)
      {a' = 0} {b' = 0} {c' = 0} {d' = 0} {e' = 0} {f' = 0} {g' = 0}
      {h' = Relation.transitionPairIncidenceCount Transition.thinTransition Transition.thinTransition *
        Transition.transitionRowCountBound Transition.thinTransition N}
      {i' = 0} {j' = 0} {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (colZeroD {N = N}) (colZeroE {N = N}) (colZeroF {N = N})
      (colZeroG {N = N})
      (transitionColumnBlock {N = N} Transition.thinTransition Transition.thinTransition h)
      (colZeroI {N = N}) (colZeroJ {N = N}) (colZeroK {N = N}))
    (trans columnFoldAtH refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.transitionTailIndex Transition.balancedTransition h) =
  trans
    (columnFoldCongFor
      (Relation.transitionTailIndex {shellIndex = N} Transition.balancedTransition h)
      {a' = 0} {b' = 0} {c' = 0} {d' = 0} {e' = 0} {f' = 0} {g' = 0} {h' = 0}
      {i' = Relation.transitionPairIncidenceCount Transition.balancedTransition Transition.balancedTransition *
        Transition.transitionRowCountBound Transition.balancedTransition N}
      {j' = 0} {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (colZeroD {N = N}) (colZeroE {N = N}) (colZeroF {N = N})
      (colZeroG {N = N}) (colZeroH {N = N})
      (transitionColumnBlock {N = N} Transition.balancedTransition Transition.balancedTransition h)
      (colZeroJ {N = N}) (colZeroK {N = N}))
    (trans columnFoldAtI refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.transitionTailIndex Transition.rowThickTransition h) =
  trans
    (columnFoldCongFor
      (Relation.transitionTailIndex {shellIndex = N} Transition.rowThickTransition h)
      {a' = 0} {b' = 0} {c' = 0} {d' = 0} {e' = 0} {f' = 0} {g' = 0} {h' = 0} {i' = 0}
      {j' = Relation.transitionPairIncidenceCount Transition.rowThickTransition Transition.rowThickTransition *
        Transition.transitionRowCountBound Transition.rowThickTransition N}
      {k' = 0}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (colZeroD {N = N}) (colZeroE {N = N}) (colZeroF {N = N})
      (colZeroG {N = N}) (colZeroH {N = N}) (colZeroI {N = N})
      (transitionColumnBlock {N = N} Transition.rowThickTransition Transition.rowThickTransition h)
      (colZeroK {N = N}))
    (trans columnFoldAtJ refl)
concreteColumnSumEqualsCandidate
  {N = N} (Relation.transitionTailIndex Transition.columnThickTransition h) =
  trans
    (columnFoldCongFor
      (Relation.transitionTailIndex {shellIndex = N} Transition.columnThickTransition h)
      {a' = 0} {b' = 0} {c' = 0} {d' = 0} {e' = 0} {f' = 0} {g' = 0} {h' = 0} {i' = 0} {j' = 0}
      {k' = Relation.transitionPairIncidenceCount Transition.columnThickTransition Transition.columnThickTransition *
        Transition.transitionRowCountBound Transition.columnThickTransition N}
      (colZeroA {N = N}) (colZeroB {N = N}) (colZeroC {N = N})
      (colZeroD {N = N}) (colZeroE {N = N}) (colZeroF {N = N})
      (colZeroG {N = N}) (colZeroH {N = N}) (colZeroI {N = N})
      (colZeroJ {N = N})
      (transitionColumnBlock {N = N} Transition.columnThickTransition Transition.columnThickTransition h))
    (trans columnFoldAtK refl)

canonicalConcreteRowColumnSumIdentity :
  (N : Nat) -> ConcreteRowColumnSumIdentityTarget N
canonicalConcreteRowColumnSumIdentity N =
  mkConcreteRowColumnSumIdentityTarget
    concreteRowSumEqualsCandidate
    concreteColumnSumEqualsCandidate

weightedRowSumEqualsCandidate :
  {N : Nat} ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  weightedConcreteRowSum f ≡ weightedRowContribution f
weightedRowSumEqualsCandidate f =
  trans
    (weightedConcreteRowSumAsFold f)
    (trans
      (sym (concreteRowSumAsFold f))
      (concreteRowSumEqualsCandidate f))

weightedColumnSumEqualsCandidate :
  {N : Nat} ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  weightedConcreteColumnSum t ≡ weightedColumnContribution t
weightedColumnSumEqualsCandidate t =
  trans
    (weightedConcreteColumnSumAsFold t)
    (trans
      (sym (concreteColumnSumAsFold t))
      (concreteColumnSumEqualsCandidate t))

------------------------------------------------------------------------
-- The remaining analytic step is intentionally target-shaped.  These fields
-- must be supplied by the depth/weight estimates; the exact decompositions
-- above do not justify them by themselves.

record ConcreteBipartiteSchurBoundTarget
    (shellIndex : Nat) : Set₁ where
  constructor mkConcreteBipartiteSchurBoundTarget
  field
    rowBound : Nat
    columnBound : Nat
    productTarget : Nat

    rowSchurBound :
      (f : Relation.ConcreteNonResidualFiniteIndex shellIndex) ->
      weightedConcreteRowSum f
        ≤ rowBound * sourceWeight f

    columnSchurBound :
      (t : Relation.ConcreteNonResidualTailIndex shellIndex) ->
      weightedConcreteColumnSum t
        ≤ columnBound * targetWeight t
    weightedProductBound : rowBound * columnBound ≤ productTarget

    rowSumIdentity :
      (f : Relation.ConcreteNonResidualFiniteIndex shellIndex) ->
      weightedConcreteRowSum f ≡ weightedRowContribution f

    columnSumIdentity :
      (t : Relation.ConcreteNonResidualTailIndex shellIndex) ->
      weightedConcreteColumnSum t ≡ weightedColumnContribution t

open ConcreteBipartiteSchurBoundTarget public

------------------------------------------------------------------------
-- Constructive product handoff.
--
-- This is the strongest theorem available from this surface alone: once a
-- caller supplies the typed row/column inequalities, the existing Nat Schur
-- witness consumes their product bound.  It does not manufacture either
-- analytic inequality.

consumeConcreteBipartiteSchurBound :
  {N : Nat} ->
  (target : ConcreteBipartiteSchurBoundTarget N) ->
  Schur.BipartiteWeightedSchurProductBoundWitness
    (ConcreteBipartiteSchurBoundTarget.rowBound target)
    (ConcreteBipartiteSchurBoundTarget.columnBound target)
    (ConcreteBipartiteSchurBoundTarget.productTarget target)
consumeConcreteBipartiteSchurBound target =
  Schur.mkBipartiteWeightedSchurProductBoundWitness
    (ConcreteBipartiteSchurBoundTarget.weightedProductBound target)

------------------------------------------------------------------------
-- Parameterized weighted target.
--
-- The legacy target above preserves its unit-weight API.  The analytic route
-- needs the actual source/target weights, so expose a separate target whose
-- row and column expressions are parameterized by those functions.  This
-- target is constructive once the generic decay obligation is inhabited; it
-- does not identify that proxy kernel with the physical scalar kernel.
------------------------------------------------------------------------

record ConcreteWeightedBipartiteSchurBoundTarget (shellIndex : Nat) : Set₁ where
  constructor mkConcreteWeightedBipartiteSchurBoundTarget
  field
    weightedSourceWeight :
      Relation.ConcreteNonResidualFiniteIndex shellIndex -> Nat

    weightedTargetWeight :
      Relation.ConcreteNonResidualTailIndex shellIndex -> Nat

    rowBound : Nat
    columnBound : Nat
    productTarget : Nat

    rowSchurBound :
      (f : Relation.ConcreteNonResidualFiniteIndex shellIndex) ->
      WeightedFibers.weightedConcreteRowSum weightedTargetWeight f ≤
      rowBound * weightedSourceWeight f

    columnSchurBound :
      (t : Relation.ConcreteNonResidualTailIndex shellIndex) ->
      WeightedFibers.weightedConcreteColumnSum weightedSourceWeight t ≤
      columnBound * weightedTargetWeight t

    weightedProductBound : rowBound * columnBound ≤ productTarget

    rowSumIdentity :
      (f : Relation.ConcreteNonResidualFiniteIndex shellIndex) ->
      WeightedFibers.weightedConcreteRowSum weightedTargetWeight f ≡
      WeightedFibers.weightedRowCandidate weightedTargetWeight f

    columnSumIdentity :
      (t : Relation.ConcreteNonResidualTailIndex shellIndex) ->
      WeightedFibers.weightedConcreteColumnSum weightedSourceWeight t ≡
      WeightedFibers.weightedColumnCandidate weightedSourceWeight t

open ConcreteWeightedBipartiteSchurBoundTarget public

------------------------------------------------------------------------
-- Typed Nat-Schur product handoff.
--
-- This is the strongest handoff available from this target alone.  The
-- target owns the concrete weighted row/column bounds and their product
-- inequality, so it can construct the existing product witness without
-- claiming an operator norm or a Stage-3 carrier identification.
------------------------------------------------------------------------

consumeConcreteWeightedBipartiteSchurBoundTarget :
  {N : Nat} ->
  (target : ConcreteWeightedBipartiteSchurBoundTarget N) ->
  Schur.BipartiteWeightedSchurProductBoundWitness
    (ConcreteWeightedBipartiteSchurBoundTarget.rowBound target)
    (ConcreteWeightedBipartiteSchurBoundTarget.columnBound target)
    (ConcreteWeightedBipartiteSchurBoundTarget.productTarget target)
consumeConcreteWeightedBipartiteSchurBoundTarget target =
  Schur.mkBipartiteWeightedSchurProductBoundWitness
    (ConcreteWeightedBipartiteSchurBoundTarget.weightedProductBound target)

weightedRowSumIdentityFromFiniteFolds :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  WeightedFibers.weightedConcreteRowSum targetWeight f ≡
  WeightedFibers.weightedRowCandidate targetWeight f
weightedRowSumIdentityFromFiniteFolds targetWeight f =
  trans
    (WeightedFibers.weightedConcreteRowSumNormalForm targetWeight f)
    (WeightedFibers.weightedRowCandidateNormalFormProof targetWeight f)

weightedColumnSumIdentityFromFiniteFolds :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  WeightedFibers.weightedConcreteColumnSum sourceWeight t ≡
  WeightedFibers.weightedColumnCandidate sourceWeight t
weightedColumnSumIdentityFromFiniteFolds sourceWeight t =
  trans
    (WeightedFibers.weightedConcreteColumnSumNormalForm sourceWeight t)
    (WeightedFibers.weightedColumnCandidateNormalFormProof sourceWeight t)

concreteWeightedBipartiteSchurBoundTargetFromDecay :
  {N : Nat} ->
  (obligation : Decay.ConcreteWeightedSchurDecayObligation N) ->
  ConcreteWeightedBipartiteSchurBoundTarget N
concreteWeightedBipartiteSchurBoundTargetFromDecay
  {N = N} obligation =
  mkConcreteWeightedBipartiteSchurBoundTarget
    (Decay.ConcreteWeightedSchurDecayObligation.sourceWeight obligation)
    (Decay.ConcreteWeightedSchurDecayObligation.targetWeight obligation)
    (Decay.ConcreteWeightedSchurDecayObligation.rowConstant obligation)
    (Decay.ConcreteWeightedSchurDecayObligation.columnConstant obligation)
    ((suc N) * (suc N))
    (Decay.ConcreteWeightedSchurDecayObligation.weightedRowDecay obligation)
    (Decay.ConcreteWeightedSchurDecayObligation.weightedColumnDecay obligation)
    (Decay.ConcreteWeightedSchurDecayObligation.weightedSchurProduct obligation)
    (weightedRowSumIdentityFromFiniteFolds
      (Decay.ConcreteWeightedSchurDecayObligation.targetWeight obligation))
    (weightedColumnSumIdentityFromFiniteFolds
      (Decay.ConcreteWeightedSchurDecayObligation.sourceWeight obligation))
