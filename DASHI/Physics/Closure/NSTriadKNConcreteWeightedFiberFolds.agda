module DASHI.Physics.Closure.NSTriadKNConcreteWeightedFiberFolds where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (_*_; _+_)
open import Data.Nat.Properties using (*-distribˡ-+; *-identityˡ; *-zeroʳ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNBipartiteWeightedSchurWitness as Schur
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailType
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialType
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionType

------------------------------------------------------------------------
-- A constant kernel factor can be pulled through a finite Nat sum.
-- This is the algebraic step missing from the unit-weight fold: the
-- weight remains inside the finite fiber rather than being erased.

sumFinMulLeft :
  {n : Nat} ->
  (k : Nat) ->
  (f : Fin n -> Nat) ->
  Schur.sumFin (λ i -> k * f i) ≡ k * Schur.sumFin f
sumFinMulLeft {n = 0} k f = sym (*-zeroʳ k)
sumFinMulLeft {n = Nat.suc n} k f =
  trans
      (cong (λ rest -> k * f fzero + rest)
      (sumFinMulLeft k (λ i -> f (fsuc i))))
    (sym (*-distribˡ-+ k (f fzero)
      (Schur.sumFin (λ i -> f (fsuc i)))))

sumFinUnitFactor :
  {n : Nat} ->
  (f : Fin n -> Nat) ->
  Schur.sumFin (λ i -> 1 * f i) ≡ 1 * Schur.sumFin f
sumFinUnitFactor f = sumFinMulLeft 1 f

weightedZeroFiber :
  {n : Nat} ->
  {f : Fin n -> Nat} ->
  Schur.sumFin (λ i -> 0 * f i) ≡ 0
weightedZeroFiber {f = f} = trans (sumFinMulLeft 0 f) refl

sumFinCong :
  {n : Nat} ->
  {f g : Fin n -> Nat} ->
  ((i : Fin n) -> f i ≡ g i) ->
  Schur.sumFin f ≡ Schur.sumFin g
sumFinCong {n = 0} pointwise = refl
sumFinCong {n = Nat.suc n} {f = f} {g = g} pointwise =
  trans
    (cong (λ rest -> f fzero + rest)
      (sumFinCong (λ i -> pointwise (fsuc i))))
    (cong (λ head -> head + Schur.sumFin (λ i -> g (fsuc i)))
      (pointwise fzero))

weightedZeroBlock :
  {n : Nat} ->
  (k : Nat) ->
  k ≡ 0 ->
  (f : Fin n -> Nat) ->
  Schur.sumFin (λ i -> k * f i) ≡ 0
weightedZeroBlock k refl f =
  trans (sumFinMulLeft 0 f) refl

forcedTailAdversarialCountZero :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (d : Adversarial.AdversarialClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (i : AdversarialType.AdversarialTail d N) ->
  Relation.concreteNonResidualPairIncidenceCount
    (Relation.forcedTailFiniteIndex c h)
    (Relation.adversarialTailIndex d i) ≡ 0
forcedTailAdversarialCountZero c d h i = refl

forcedTailTransitionCountZero :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (d : Transition.TransitionClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  (i : TransitionType.TransitionTail d N) ->
  Relation.concreteNonResidualPairIncidenceCount
    (Relation.forcedTailFiniteIndex c h)
    (Relation.transitionTailIndex d i) ≡ 0
forcedTailTransitionCountZero c d h i = refl

adversarialForcedTailCountZero :
  {N : Nat} ->
  (c : Adversarial.AdversarialClass) ->
  (d : ForcedTail.ForcedTailClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  (i : ForcedTailType.ForcedTailTail d N) ->
  Relation.concreteNonResidualPairIncidenceCount
    (Relation.adversarialFiniteIndex c h)
    (Relation.forcedTailTailIndex d i) ≡ 0
adversarialForcedTailCountZero c d h i = refl

adversarialTransitionCountZero :
  {N : Nat} ->
  (c : Adversarial.AdversarialClass) ->
  (d : Transition.TransitionClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  (i : TransitionType.TransitionTail d N) ->
  Relation.concreteNonResidualPairIncidenceCount
    (Relation.adversarialFiniteIndex c h)
    (Relation.transitionTailIndex d i) ≡ 0
adversarialTransitionCountZero c d h i = refl

transitionForcedTailCountZero :
  {N : Nat} ->
  (c : Transition.TransitionClass) ->
  (d : ForcedTail.ForcedTailClass) ->
  (h : TransitionType.TransitionHead c N) ->
  (i : ForcedTailType.ForcedTailTail d N) ->
  Relation.concreteNonResidualPairIncidenceCount
    (Relation.transitionFiniteIndex c h)
    (Relation.forcedTailTailIndex d i) ≡ 0
transitionForcedTailCountZero c d h i = refl

transitionAdversarialCountZero :
  {N : Nat} ->
  (c : Transition.TransitionClass) ->
  (d : Adversarial.AdversarialClass) ->
  (h : TransitionType.TransitionHead c N) ->
  (i : AdversarialType.AdversarialTail d N) ->
  Relation.concreteNonResidualPairIncidenceCount
    (Relation.transitionFiniteIndex c h)
    (Relation.adversarialTailIndex d i) ≡ 0
transitionAdversarialCountZero c d h i = refl

addCong :
  {a a' b b' : Nat} ->
  a ≡ a' -> b ≡ b' -> a + b ≡ a' + b'
addCong refl refl = refl

sum11Cong :
  {a a' b b' c c' d d' e e' f f' g g' h h' i i' j j' k k' : Nat} ->
  a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' ->
  e ≡ e' -> f ≡ f' -> g ≡ g' -> h ≡ h' ->
  i ≡ i' -> j ≡ j' -> k ≡ k' ->
  (((a + b) + (c + d)) + ((e + f) + g)) + ((h + i) + (j + k))
    ≡
  (((a' + b') + (c' + d')) + ((e' + f') + g')) + ((h' + i') + (j' + k'))
sum11Cong pa pb pc pd pe pf pg ph pi pj pk =
  addCong
    (addCong
      (addCong (addCong pa pb) (addCong pc pd))
      (addCong (addCong pe pf) pg))
    (addCong (addCong ph pi) (addCong pj pk))

------------------------------------------------------------------------
-- Mixed profile blocks are zero.  The normal form retains all blocks in
-- the same profile family and erases only the six rectangular cross-family
-- blocks.  This is the exact global fold normalization needed before any
-- depth estimate is applied.

weightedRowNormalForm :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
weightedRowNormalForm targetWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) =
  Relation.forcedTailPairIncidenceCount c d *
    targetWeight (Relation.forcedTailTailIndex d i)
weightedRowNormalForm targetWeight
  (Relation.forcedTailFiniteIndex c h) _ = 0
weightedRowNormalForm targetWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex d i) =
  Relation.adversarialPairIncidenceCount c d *
    targetWeight (Relation.adversarialTailIndex d i)
weightedRowNormalForm targetWeight
  (Relation.adversarialFiniteIndex c h) _ = 0
weightedRowNormalForm targetWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex d i) =
  Relation.transitionPairIncidenceCount c d *
    targetWeight (Relation.transitionTailIndex d i)
weightedRowNormalForm targetWeight
  (Relation.transitionFiniteIndex c h) _ = 0

weightedRowKernelAgreement :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  Relation.concreteNonResidualPairIncidenceCount f t * targetWeight t
    ≡ weightedRowNormalForm targetWeight f t
weightedRowKernelAgreement targetWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) = refl
weightedRowKernelAgreement targetWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.adversarialTailIndex d i) =
  cong (λ k -> k * targetWeight (Relation.adversarialTailIndex d i))
    (forcedTailAdversarialCountZero c d h i)
weightedRowKernelAgreement targetWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.transitionTailIndex d i) =
  cong (λ k -> k * targetWeight (Relation.transitionTailIndex d i))
    (forcedTailTransitionCountZero c d h i)
weightedRowKernelAgreement targetWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) =
  cong (λ k -> k * targetWeight (Relation.forcedTailTailIndex d i))
    (adversarialForcedTailCountZero c d h i)
weightedRowKernelAgreement targetWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex d i) = refl
weightedRowKernelAgreement targetWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.transitionTailIndex d i) =
  cong (λ k -> k * targetWeight (Relation.transitionTailIndex d i))
    (adversarialTransitionCountZero c d h i)
weightedRowKernelAgreement targetWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) =
  cong (λ k -> k * targetWeight (Relation.forcedTailTailIndex d i))
    (transitionForcedTailCountZero c d h i)
weightedRowKernelAgreement targetWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.adversarialTailIndex d i) =
  cong (λ k -> k * targetWeight (Relation.adversarialTailIndex d i))
    (transitionAdversarialCountZero c d h i)
weightedRowKernelAgreement targetWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex d i) = refl

concreteTailSumCong :
  {N : Nat} ->
  {f g : Relation.ConcreteNonResidualTailIndex N -> Nat} ->
  ((t : Relation.ConcreteNonResidualTailIndex N) -> f t ≡ g t) ->
  Schur.concreteTailSum f ≡ Schur.concreteTailSum g
concreteTailSumCong pointwise =
  sum11Cong
    (sumFinCong (λ i -> pointwise (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
    (sumFinCong (λ i -> pointwise (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
    (sumFinCong (λ i -> pointwise (Relation.forcedTailTailIndex ForcedTail.transition i)))
    (sumFinCong (λ i -> pointwise (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
    (sumFinCong (λ i -> pointwise (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
    (sumFinCong (λ i -> pointwise (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
    (sumFinCong (λ i -> pointwise (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionTailIndex Transition.thinTransition i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionTailIndex Transition.balancedTransition i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionTailIndex Transition.rowThickTransition i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionTailIndex Transition.columnThickTransition i)))

------------------------------------------------------------------------
-- Weighted class candidates.  The source class is fixed by the row and
-- the target class is the finite fiber being summed.

weightedForcedTailRowBlock :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c d : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailHead c N) ->
  Schur.sumFin
    (λ i -> Relation.forcedTailPairIncidenceCount c d *
      targetWeight (Relation.forcedTailTailIndex d i))
  ≡ Relation.forcedTailPairIncidenceCount c d *
    Schur.sumFin (λ i -> targetWeight (Relation.forcedTailTailIndex d i))
weightedForcedTailRowBlock targetWeight c d h =
  sumFinMulLeft
    (Relation.forcedTailPairIncidenceCount c d)
    (λ i -> targetWeight (Relation.forcedTailTailIndex d i))

weightedAdversarialRowBlock :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c d : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialHead c N) ->
  Schur.sumFin
    (λ i -> Relation.adversarialPairIncidenceCount c d *
      targetWeight (Relation.adversarialTailIndex d i))
  ≡ Relation.adversarialPairIncidenceCount c d *
    Schur.sumFin (λ i -> targetWeight (Relation.adversarialTailIndex d i))
weightedAdversarialRowBlock targetWeight c d h =
  sumFinMulLeft
    (Relation.adversarialPairIncidenceCount c d)
    (λ i -> targetWeight (Relation.adversarialTailIndex d i))

weightedTransitionRowBlock :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (c d : Transition.TransitionClass) ->
  (h : TransitionType.TransitionHead c N) ->
  Schur.sumFin
    (λ i -> Relation.transitionPairIncidenceCount c d *
      targetWeight (Relation.transitionTailIndex d i))
  ≡ Relation.transitionPairIncidenceCount c d *
    Schur.sumFin (λ i -> targetWeight (Relation.transitionTailIndex d i))
weightedTransitionRowBlock targetWeight c d h =
  sumFinMulLeft
    (Relation.transitionPairIncidenceCount c d)
    (λ i -> targetWeight (Relation.transitionTailIndex d i))

weightedForcedTailColumnBlock :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c d : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailType.ForcedTailTail c N) ->
  Schur.sumFin
    (λ i -> Relation.forcedTailPairIncidenceCount d c *
      sourceWeight (Relation.forcedTailFiniteIndex d i))
  ≡ Relation.forcedTailPairIncidenceCount d c *
    Schur.sumFin (λ i -> sourceWeight (Relation.forcedTailFiniteIndex d i))
weightedForcedTailColumnBlock sourceWeight c d h =
  sumFinMulLeft
    (Relation.forcedTailPairIncidenceCount d c)
    (λ i -> sourceWeight (Relation.forcedTailFiniteIndex d i))

weightedAdversarialColumnBlock :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c d : Adversarial.AdversarialClass) ->
  (h : AdversarialType.AdversarialTail c N) ->
  Schur.sumFin
    (λ i -> Relation.adversarialPairIncidenceCount d c *
      sourceWeight (Relation.adversarialFiniteIndex d i))
  ≡ Relation.adversarialPairIncidenceCount d c *
    Schur.sumFin (λ i -> sourceWeight (Relation.adversarialFiniteIndex d i))
weightedAdversarialColumnBlock sourceWeight c d h =
  sumFinMulLeft
    (Relation.adversarialPairIncidenceCount d c)
    (λ i -> sourceWeight (Relation.adversarialFiniteIndex d i))

weightedTransitionColumnBlock :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (c d : Transition.TransitionClass) ->
  (h : TransitionType.TransitionTail c N) ->
  Schur.sumFin
    (λ i -> Relation.transitionPairIncidenceCount d c *
      sourceWeight (Relation.transitionFiniteIndex d i))
  ≡ Relation.transitionPairIncidenceCount d c *
    Schur.sumFin (λ i -> sourceWeight (Relation.transitionFiniteIndex d i))
weightedTransitionColumnBlock sourceWeight c d h =
  sumFinMulLeft
    (Relation.transitionPairIncidenceCount d c)
    (λ i -> sourceWeight (Relation.transitionFiniteIndex d i))

------------------------------------------------------------------------
-- The concrete weighted row/column sums.  These are the actual Schur-test
-- expressions; no unit-weight assumption is made here.

weightedConcreteRowSum :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
weightedConcreteRowSum targetWeight f =
  Schur.concreteTailSum
    (λ t -> Relation.concreteNonResidualPairIncidenceCount f t *
      targetWeight t)

weightedConcreteColumnSum :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
weightedConcreteColumnSum sourceWeight t =
  Schur.concreteFiniteSum
    (λ f -> Relation.concreteNonResidualPairIncidenceCount f t *
      sourceWeight f)

weightedConcreteRowSumNormalForm :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  weightedConcreteRowSum targetWeight f ≡
  Schur.concreteTailSum (weightedRowNormalForm targetWeight f)
weightedConcreteRowSumNormalForm targetWeight f =
  concreteTailSumCong (weightedRowKernelAgreement targetWeight f)

weightedColumnNormalForm :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
weightedColumnNormalForm sourceWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) =
  Relation.forcedTailPairIncidenceCount c d *
    sourceWeight (Relation.forcedTailFiniteIndex c h)
weightedColumnNormalForm sourceWeight _
  (Relation.forcedTailTailIndex c h) = 0
weightedColumnNormalForm sourceWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex d i) =
  Relation.adversarialPairIncidenceCount c d *
    sourceWeight (Relation.adversarialFiniteIndex c h)
weightedColumnNormalForm sourceWeight _
  (Relation.adversarialTailIndex c h) = 0
weightedColumnNormalForm sourceWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex d i) =
  Relation.transitionPairIncidenceCount c d *
    sourceWeight (Relation.transitionFiniteIndex c h)
weightedColumnNormalForm sourceWeight _
  (Relation.transitionTailIndex c h) = 0

weightedColumnKernelAgreement :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  Relation.concreteNonResidualPairIncidenceCount f t * sourceWeight f
    ≡ weightedColumnNormalForm sourceWeight f t
weightedColumnKernelAgreement sourceWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) = refl
weightedColumnKernelAgreement sourceWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.adversarialTailIndex d i) =
  cong (λ k -> k * sourceWeight (Relation.forcedTailFiniteIndex c h))
    (forcedTailAdversarialCountZero c d h i)
weightedColumnKernelAgreement sourceWeight
  (Relation.forcedTailFiniteIndex c h)
  (Relation.transitionTailIndex d i) =
  cong (λ k -> k * sourceWeight (Relation.forcedTailFiniteIndex c h))
    (forcedTailTransitionCountZero c d h i)
weightedColumnKernelAgreement sourceWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) =
  cong (λ k -> k * sourceWeight (Relation.adversarialFiniteIndex c h))
    (adversarialForcedTailCountZero c d h i)
weightedColumnKernelAgreement sourceWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.adversarialTailIndex d i) = refl
weightedColumnKernelAgreement sourceWeight
  (Relation.adversarialFiniteIndex c h)
  (Relation.transitionTailIndex d i) =
  cong (λ k -> k * sourceWeight (Relation.adversarialFiniteIndex c h))
    (adversarialTransitionCountZero c d h i)
weightedColumnKernelAgreement sourceWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.forcedTailTailIndex d i) =
  cong (λ k -> k * sourceWeight (Relation.transitionFiniteIndex c h))
    (transitionForcedTailCountZero c d h i)
weightedColumnKernelAgreement sourceWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.adversarialTailIndex d i) =
  cong (λ k -> k * sourceWeight (Relation.transitionFiniteIndex c h))
    (transitionAdversarialCountZero c d h i)
weightedColumnKernelAgreement sourceWeight
  (Relation.transitionFiniteIndex c h)
  (Relation.transitionTailIndex d i) = refl

concreteFiniteSumCong :
  {N : Nat} ->
  {f g : Relation.ConcreteNonResidualFiniteIndex N -> Nat} ->
  ((i : Relation.ConcreteNonResidualFiniteIndex N) -> f i ≡ g i) ->
  Schur.concreteFiniteSum f ≡ Schur.concreteFiniteSum g
concreteFiniteSumCong pointwise =
  sum11Cong
    (sumFinCong (λ i -> pointwise (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
    (sumFinCong (λ i -> pointwise (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
    (sumFinCong (λ i -> pointwise (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
    (sumFinCong (λ i -> pointwise (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
    (sumFinCong (λ i -> pointwise (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
    (sumFinCong (λ i -> pointwise (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
    (sumFinCong (λ i -> pointwise (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionFiniteIndex Transition.thinTransition i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionFiniteIndex Transition.balancedTransition i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
    (sumFinCong (λ i -> pointwise (Relation.transitionFiniteIndex Transition.columnThickTransition i)))

weightedConcreteColumnSumNormalForm :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  weightedConcreteColumnSum sourceWeight t ≡
  Schur.concreteFiniteSum (λ f -> weightedColumnNormalForm sourceWeight f t)
weightedConcreteColumnSumNormalForm sourceWeight t =
  concreteFiniteSumCong (λ f -> weightedColumnKernelAgreement sourceWeight f t)

weightedRowCandidate :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
weightedRowCandidate targetWeight
  (Relation.forcedTailFiniteIndex c _) =
  Relation.forcedTailPairIncidenceCount c c *
    Schur.sumFin (λ i -> targetWeight (Relation.forcedTailTailIndex c i))
weightedRowCandidate targetWeight
  (Relation.adversarialFiniteIndex c _) =
  Relation.adversarialPairIncidenceCount c c *
    Schur.sumFin (λ i -> targetWeight (Relation.adversarialTailIndex c i))
weightedRowCandidate targetWeight
  (Relation.transitionFiniteIndex c _) =
  Relation.transitionPairIncidenceCount c c *
    Schur.sumFin (λ i -> targetWeight (Relation.transitionTailIndex c i))

weightedColumnCandidate :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
weightedColumnCandidate sourceWeight
  (Relation.forcedTailTailIndex c _) =
  Relation.forcedTailPairIncidenceCount c c *
    Schur.sumFin (λ i -> sourceWeight (Relation.forcedTailFiniteIndex c i))
weightedColumnCandidate sourceWeight
  (Relation.adversarialTailIndex c _) =
  Relation.adversarialPairIncidenceCount c c *
    Schur.sumFin (λ i -> sourceWeight (Relation.adversarialFiniteIndex c i))
weightedColumnCandidate sourceWeight
  (Relation.transitionTailIndex c _) =
  Relation.transitionPairIncidenceCount c c *
    Schur.sumFin (λ i -> sourceWeight (Relation.transitionFiniteIndex c i))

weightedZeroBlockAny :
  {n : Nat} ->
  {f : Fin n -> Nat} ->
  Schur.sumFin (λ i -> 0 * f i) ≡ 0
weightedZeroBlockAny {f = f} = weightedZeroBlock 0 refl f


------------------------------------------------------------------------
-- Candidate fold target.
--
-- The 11-fiber kernel normal form is proved above.  Reducing its surviving
-- same-family block to the diagonal candidate additionally needs the
-- zero-multiplication normalization for arbitrary dependent Fin weights.  Keep
-- that exact remaining equality typed and fail-closed until its orientation
-- is proved without a unit-weight shortcut.
------------------------------------------------------------------------

record ConcreteWeightedCandidateFoldTarget (N : Nat) : Set₁ where
  constructor mkConcreteWeightedCandidateFoldTarget
  field
    rowCandidateNormalForm :
      (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
      (f : Relation.ConcreteNonResidualFiniteIndex N) ->
      Schur.concreteTailSum (weightedRowNormalForm targetWeight f)
        ≡ weightedRowCandidate targetWeight f

    columnCandidateNormalForm :
      (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
      (t : Relation.ConcreteNonResidualTailIndex N) ->
      Schur.concreteFiniteSum (λ f -> weightedColumnNormalForm sourceWeight f t)
        ≡ weightedColumnCandidate sourceWeight t

open ConcreteWeightedCandidateFoldTarget public

------------------------------------------------------------------------
-- The proxy kernel's weighted candidate folds are finite algebra.  The
-- surviving diagonal block is factored with sumFinMulLeft; every other
-- block is definitionally zero.  These proofs apply only to the concrete
-- proxy count above, not to the physical retained-triad kernel.
------------------------------------------------------------------------

rowFold : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat
rowFold a b c d e f g h i j k =
  (((a + b) + (c + d)) + ((e + f) + g)) + ((h + i) + (j + k))

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

rowFoldCong :
  {a a' b b' c c' d d' e e' f f' g g' h h' i i' j j' k k' : Nat} ->
  a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' ->
  e ≡ e' -> f ≡ f' -> g ≡ g' -> h ≡ h' ->
  i ≡ i' -> j ≡ j' -> k ≡ k' ->
  rowFold a b c d e f g h i j k ≡
  rowFold a' b' c' d' e' f' g' h' i' j' k'
rowFoldCong refl refl refl refl refl refl refl refl refl refl refl = refl

columnFold : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat
columnFold = rowFold

columnFoldAtA : {x : Nat} -> columnFold x 0 0 0 0 0 0 0 0 0 0 ≡ x
columnFoldAtA = rowFoldAtA
columnFoldAtB : {x : Nat} -> columnFold 0 x 0 0 0 0 0 0 0 0 0 ≡ x
columnFoldAtB = rowFoldAtB
columnFoldAtC : {x : Nat} -> columnFold 0 0 x 0 0 0 0 0 0 0 0 ≡ x
columnFoldAtC = rowFoldAtC
columnFoldAtD : {x : Nat} -> columnFold 0 0 0 x 0 0 0 0 0 0 0 ≡ x
columnFoldAtD = rowFoldAtD
columnFoldAtE : {x : Nat} -> columnFold 0 0 0 0 x 0 0 0 0 0 0 ≡ x
columnFoldAtE = rowFoldAtE
columnFoldAtF : {x : Nat} -> columnFold 0 0 0 0 0 x 0 0 0 0 0 ≡ x
columnFoldAtF = rowFoldAtF
columnFoldAtG : {x : Nat} -> columnFold 0 0 0 0 0 0 x 0 0 0 0 ≡ x
columnFoldAtG = rowFoldAtG
columnFoldAtH : {x : Nat} -> columnFold 0 0 0 0 0 0 0 x 0 0 0 ≡ x
columnFoldAtH = rowFoldAtH
columnFoldAtI : {x : Nat} -> columnFold 0 0 0 0 0 0 0 0 x 0 0 ≡ x
columnFoldAtI = rowFoldAtI
columnFoldAtJ : {x : Nat} -> columnFold 0 0 0 0 0 0 0 0 0 x 0 ≡ x
columnFoldAtJ = rowFoldAtJ
columnFoldAtK : {x : Nat} -> columnFold 0 0 0 0 0 0 0 0 0 0 x ≡ x
columnFoldAtK = rowFoldAtK

columnFoldCong :
  {a a' b b' c c' d d' e e' f f' g g' h h' i i' j j' k k' : Nat} ->
  a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' ->
  e ≡ e' -> f ≡ f' -> g ≡ g' -> h ≡ h' ->
  i ≡ i' -> j ≡ j' -> k ≡ k' ->
  columnFold a b c d e f g h i j k ≡
  columnFold a' b' c' d' e' f' g' h' i' j' k'
columnFoldCong = rowFoldCong

weightedRowCandidateNormalFormProof :
  {N : Nat} ->
  (targetWeight : Relation.ConcreteNonResidualTailIndex N -> Nat) ->
  (f : Relation.ConcreteNonResidualFiniteIndex N) ->
  Schur.concreteTailSum (weightedRowNormalForm targetWeight f) ≡
  weightedRowCandidate targetWeight f
weightedRowCandidateNormalFormProof targetWeight
  (Relation.forcedTailFiniteIndex ForcedTail.tailEnd h) =
  trans
    (sum11Cong
      (weightedForcedTailRowBlock targetWeight ForcedTail.tailEnd ForcedTail.tailEnd h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtA
weightedRowCandidateNormalFormProof targetWeight
  (Relation.forcedTailFiniteIndex ForcedTail.nearTail h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedForcedTailRowBlock targetWeight ForcedTail.nearTail ForcedTail.nearTail h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtB
weightedRowCandidateNormalFormProof targetWeight
  (Relation.forcedTailFiniteIndex ForcedTail.transition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedForcedTailRowBlock targetWeight ForcedTail.transition ForcedTail.transition h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtC
weightedRowCandidateNormalFormProof targetWeight
  (Relation.forcedTailFiniteIndex ForcedTail.degenerate h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedForcedTailRowBlock targetWeight ForcedTail.degenerate ForcedTail.degenerate h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtD
weightedRowCandidateNormalFormProof targetWeight
  (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedAdversarialRowBlock targetWeight Adversarial.sparseAdmissible Adversarial.sparseAdmissible h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtE
weightedRowCandidateNormalFormProof targetWeight
  (Relation.adversarialFiniteIndex Adversarial.angularDegenerate h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedAdversarialRowBlock targetWeight Adversarial.angularDegenerate Adversarial.angularDegenerate h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtF
weightedRowCandidateNormalFormProof targetWeight
  (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedAdversarialRowBlock targetWeight Adversarial.boundarySmallShell Adversarial.boundarySmallShell h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtG
weightedRowCandidateNormalFormProof targetWeight
  (Relation.transitionFiniteIndex Transition.thinTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedTransitionRowBlock targetWeight Transition.thinTransition Transition.thinTransition h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtH
weightedRowCandidateNormalFormProof targetWeight
  (Relation.transitionFiniteIndex Transition.balancedTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedTransitionRowBlock targetWeight Transition.balancedTransition Transition.balancedTransition h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtI
weightedRowCandidateNormalFormProof targetWeight
  (Relation.transitionFiniteIndex Transition.rowThickTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedTransitionRowBlock targetWeight Transition.rowThickTransition Transition.rowThickTransition h)
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.columnThickTransition i))))
    rowFoldAtJ
weightedRowCandidateNormalFormProof targetWeight
  (Relation.transitionFiniteIndex Transition.columnThickTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.forcedTailTailIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.adversarialTailIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> targetWeight (Relation.transitionTailIndex Transition.rowThickTransition i)))
      (weightedTransitionRowBlock targetWeight Transition.columnThickTransition Transition.columnThickTransition h))
    rowFoldAtK

weightedColumnCandidateNormalFormProof :
  {N : Nat} ->
  (sourceWeight : Relation.ConcreteNonResidualFiniteIndex N -> Nat) ->
  (t : Relation.ConcreteNonResidualTailIndex N) ->
  Schur.concreteFiniteSum (λ f -> weightedColumnNormalForm sourceWeight f t) ≡
  weightedColumnCandidate sourceWeight t
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.forcedTailTailIndex ForcedTail.tailEnd h) =
  trans
    (sum11Cong
      (weightedForcedTailColumnBlock sourceWeight ForcedTail.tailEnd ForcedTail.tailEnd h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtA
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.forcedTailTailIndex ForcedTail.nearTail h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedForcedTailColumnBlock sourceWeight ForcedTail.nearTail ForcedTail.nearTail h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtB
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.forcedTailTailIndex ForcedTail.transition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedForcedTailColumnBlock sourceWeight ForcedTail.transition ForcedTail.transition h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtC
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.forcedTailTailIndex ForcedTail.degenerate h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedForcedTailColumnBlock sourceWeight ForcedTail.degenerate ForcedTail.degenerate h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtD
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.adversarialTailIndex Adversarial.sparseAdmissible h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedAdversarialColumnBlock sourceWeight Adversarial.sparseAdmissible Adversarial.sparseAdmissible h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtE
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.adversarialTailIndex Adversarial.angularDegenerate h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedAdversarialColumnBlock sourceWeight Adversarial.angularDegenerate Adversarial.angularDegenerate h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtF
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.adversarialTailIndex Adversarial.boundarySmallShell h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedAdversarialColumnBlock sourceWeight Adversarial.boundarySmallShell Adversarial.boundarySmallShell h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtG
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.transitionTailIndex Transition.thinTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedTransitionColumnBlock sourceWeight Transition.thinTransition Transition.thinTransition h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtH
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.transitionTailIndex Transition.balancedTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedTransitionColumnBlock sourceWeight Transition.balancedTransition Transition.balancedTransition h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtI
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.transitionTailIndex Transition.rowThickTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedTransitionColumnBlock sourceWeight Transition.rowThickTransition Transition.rowThickTransition h)
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.columnThickTransition i))))
    columnFoldAtJ
weightedColumnCandidateNormalFormProof sourceWeight
  (Relation.transitionTailIndex Transition.columnThickTransition h) =
  trans
    (sum11Cong
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.nearTail i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.transition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.forcedTailFiniteIndex ForcedTail.degenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.thinTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.balancedTransition i)))
      (weightedZeroBlock 0 refl (λ i -> sourceWeight (Relation.transitionFiniteIndex Transition.rowThickTransition i)))
      (weightedTransitionColumnBlock sourceWeight Transition.columnThickTransition Transition.columnThickTransition h))
    columnFoldAtK

canonicalConcreteWeightedCandidateFold :
  (N : Nat) -> ConcreteWeightedCandidateFoldTarget N
canonicalConcreteWeightedCandidateFold N =
  mkConcreteWeightedCandidateFoldTarget
    weightedRowCandidateNormalFormProof
    weightedColumnCandidateNormalFormProof
