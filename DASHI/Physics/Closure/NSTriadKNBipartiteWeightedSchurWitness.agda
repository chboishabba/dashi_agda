module DASHI.Physics.Closure.NSTriadKNBipartiteWeightedSchurWitness where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (_≤_; _*_; _+_)
open import Data.Nat.Properties using
  (*-zeroʳ; *-suc; *-assoc; *-mono-≤; ≤-trans; ≤-refl; ≤-reflexive)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNRectangularWeightedSchurSurface as Rectangular
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition
import DASHI.Physics.ClaySupportingSchurOperatorBound as NatSchur

sumFin : {n : Nat} -> (Fin n -> Nat) -> Nat
sumFin {n = 0} _ = 0
sumFin {n = suc n} f =
  f fzero + sumFin {n = n} (λ i → f (fsuc i))

sumFinZero :
  {n : Nat} -> sumFin {n = n} (λ _ → 0) ≡ 0
sumFinZero {n = 0} = refl
sumFinZero {n = suc n} =
  trans (cong (0 +_) (sumFinZero {n = n})) refl

sumFinConstant :
  {n : Nat} -> (v : Nat) ->
  sumFin {n = n} (λ _ → v) ≡ v * n
sumFinConstant {n = 0} v = sym (*-zeroʳ v)
sumFinConstant {n = suc n} v =
  trans
    (cong (v +_) (sumFinConstant {n = n} v))
    (sym (*-suc v n))

concreteTailSum :
  {shellIndex : Nat} ->
  (Relation.ConcreteNonResidualTailIndex shellIndex -> Nat) -> Nat
concreteTailSum {shellIndex = N} f =
  (sumFin (λ i → f (Relation.forcedTailTailIndex ForcedTail.tailEnd i)) +
   sumFin (λ i → f (Relation.forcedTailTailIndex ForcedTail.nearTail i))) +
   (sumFin (λ i → f (Relation.forcedTailTailIndex ForcedTail.transition i)) +
   sumFin (λ i → f (Relation.forcedTailTailIndex ForcedTail.degenerate i))) +
  ((sumFin (λ i → f (Relation.adversarialTailIndex Adversarial.sparseAdmissible i)) +
    sumFin (λ i → f (Relation.adversarialTailIndex Adversarial.angularDegenerate i))) +
   sumFin (λ i → f (Relation.adversarialTailIndex Adversarial.boundarySmallShell i))) +
  ((sumFin (λ i → f (Relation.transitionTailIndex Transition.thinTransition i)) +
    sumFin (λ i → f (Relation.transitionTailIndex Transition.balancedTransition i))) +
   (sumFin (λ i → f (Relation.transitionTailIndex Transition.rowThickTransition i)) +
    sumFin (λ i → f (Relation.transitionTailIndex Transition.columnThickTransition i))))

concreteFiniteSum :
  {shellIndex : Nat} ->
  (Relation.ConcreteNonResidualFiniteIndex shellIndex -> Nat) -> Nat
concreteFiniteSum {shellIndex = N} f =
  (sumFin (λ i → f (Relation.forcedTailFiniteIndex ForcedTail.tailEnd i)) +
   sumFin (λ i → f (Relation.forcedTailFiniteIndex ForcedTail.nearTail i))) +
   (sumFin (λ i → f (Relation.forcedTailFiniteIndex ForcedTail.transition i)) +
   sumFin (λ i → f (Relation.forcedTailFiniteIndex ForcedTail.degenerate i))) +
  ((sumFin (λ i → f (Relation.adversarialFiniteIndex Adversarial.sparseAdmissible i)) +
    sumFin (λ i → f (Relation.adversarialFiniteIndex Adversarial.angularDegenerate i))) +
   sumFin (λ i → f (Relation.adversarialFiniteIndex Adversarial.boundarySmallShell i))) +
  ((sumFin (λ i → f (Relation.transitionFiniteIndex Transition.thinTransition i)) +
    sumFin (λ i → f (Relation.transitionFiniteIndex Transition.balancedTransition i))) +
   (sumFin (λ i → f (Relation.transitionFiniteIndex Transition.rowThickTransition i)) +
    sumFin (λ i → f (Relation.transitionFiniteIndex Transition.columnThickTransition i))))

concreteRowSum :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex shellIndex -> Nat
concreteRowSum f =
  concreteTailSum (λ t → Relation.concreteNonResidualPairIncidenceCount f t)

concreteColumnSum :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualTailIndex shellIndex -> Nat
concreteColumnSum t =
  concreteFiniteSum (λ f → Relation.concreteNonResidualPairIncidenceCount f t)

concreteRowContribution :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex shellIndex -> Nat
concreteRowContribution
  {shellIndex = N} (Relation.forcedTailFiniteIndex c _) =
  Relation.forcedTailPairIncidenceCount c c *
  ForcedTail.forcedTailTailCountBound c N
concreteRowContribution
  {shellIndex = N} (Relation.adversarialFiniteIndex c _) =
  Relation.adversarialPairIncidenceCount c c *
  Adversarial.adversarialColumnCountBound c N
concreteRowContribution
  {shellIndex = N} (Relation.transitionFiniteIndex c _) =
  Relation.transitionPairIncidenceCount c c *
  Transition.transitionColumnCountBound c N

concreteColumnContribution :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualTailIndex shellIndex -> Nat
concreteColumnContribution
  {shellIndex = N} (Relation.forcedTailTailIndex c _) =
  Relation.forcedTailPairIncidenceCount c c *
  ForcedTail.forcedTailHeadCountBound c N
concreteColumnContribution
  {shellIndex = N} (Relation.adversarialTailIndex c _) =
  Relation.adversarialPairIncidenceCount c c *
  Adversarial.adversarialRowCountBound c N
concreteColumnContribution
  {shellIndex = N} (Relation.transitionTailIndex c _) =
  Relation.transitionPairIncidenceCount c c *
  Transition.transitionRowCountBound c N

------------------------------------------------------------------------
-- Concrete weighted rectangular kernel witness.
--
-- Source and target weights are separate because the pair-incidence relation
-- is bipartite.  The row and column contributions are explicit Nat-valued
-- quantities; their analytic definitions and bounds are supplied downstream.

record BipartiteWeightedSchurKernelData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkBipartiteWeightedSchurKernelData
  field
    kernelData : Rectangular.RectangularKernelData
      residueNormModel shellIndex

    sourceWeight :
      Rectangular.RectangularKernelData.FiniteIndex kernelData -> Nat

    targetWeight :
      Rectangular.RectangularKernelData.TailIndex kernelData -> Nat

    rowContributionCandidate :
      Rectangular.RectangularKernelData.FiniteIndex kernelData -> Nat

    columnContributionCandidate :
      Rectangular.RectangularKernelData.TailIndex kernelData -> Nat

open BipartiteWeightedSchurKernelData public

BipartiteKernelFiniteIndex :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  BipartiteWeightedSchurKernelData residueNormModel shellIndex -> Set
BipartiteKernelFiniteIndex kernelData =
  Rectangular.RectangularKernelData.FiniteIndex
    (BipartiteWeightedSchurKernelData.kernelData kernelData)

BipartiteKernelTailIndex :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  BipartiteWeightedSchurKernelData residueNormModel shellIndex -> Set
BipartiteKernelTailIndex kernelData =
  Rectangular.RectangularKernelData.TailIndex
    (BipartiteWeightedSchurKernelData.kernelData kernelData)

canonicalBipartiteWeightedSchurKernelData :
  (residueNormModel : ResidueNorm.ResidueNormModel) ->
  BipartiteWeightedSchurKernelData residueNormModel 1
canonicalBipartiteWeightedSchurKernelData residueNormModel =
  mkBipartiteWeightedSchurKernelData
    (Rectangular.canonicalRectangularKernelData residueNormModel)
    (λ _ → 1)
    (λ _ → 1)
    concreteRowContribution
    concreteColumnContribution

------------------------------------------------------------------------
-- Schur bound target.
--
-- The row/column contributions are explicit, but no fake values or proof
-- receipts are supplied for them.

record BipartiteWeightedSchurBoundTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkBipartiteWeightedSchurBoundTarget
  field
    kernelData : BipartiteWeightedSchurKernelData
      residueNormModel shellIndex

    rowBound : Nat
    columnBound : Nat
    productTarget : Nat

    rowSum : BipartiteKernelFiniteIndex kernelData -> Nat
    columnSum : BipartiteKernelTailIndex kernelData -> Nat

    rowSumMatchesCandidate :
      (f : BipartiteKernelFiniteIndex kernelData) ->
      rowSum f ≡
      BipartiteWeightedSchurKernelData.rowContributionCandidate
        kernelData f

    columnSumMatchesCandidate :
      (t : BipartiteKernelTailIndex kernelData) ->
      columnSum t ≡
      BipartiteWeightedSchurKernelData.columnContributionCandidate
        kernelData t

    rowBoundProof :
      (f : BipartiteKernelFiniteIndex kernelData) ->
      rowSum f ≤
      rowBound * BipartiteWeightedSchurKernelData.sourceWeight
        kernelData f

    columnBoundProof :
      (t : BipartiteKernelTailIndex kernelData) ->
      columnSum t ≤
      columnBound * BipartiteWeightedSchurKernelData.targetWeight
        kernelData t

    weightedProductBound : rowBound * columnBound ≤ productTarget

open BipartiteWeightedSchurBoundTarget public

BipartiteSchurSourceCarrier :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  BipartiteWeightedSchurBoundTarget residueNormModel shellIndex -> Set
BipartiteSchurSourceCarrier target =
  BipartiteKernelFiniteIndex
    (BipartiteWeightedSchurBoundTarget.kernelData target)

BipartiteSchurTargetCarrier :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  BipartiteWeightedSchurBoundTarget residueNormModel shellIndex -> Set
BipartiteSchurTargetCarrier target =
  BipartiteKernelTailIndex
    (BipartiteWeightedSchurBoundTarget.kernelData target)

record BipartiteWeightedSchurProductBoundWitness
    (rowBound : Nat)
    (columnBound : Nat)
    (productTarget : Nat) : Set where
  constructor mkBipartiteWeightedSchurProductBoundWitness
  field
    weightedProductBoundWitness : rowBound * columnBound ≤ productTarget

consumeBipartiteWeightedSchurBounds :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteWeightedSchurBoundTarget residueNormModel shellIndex) ->
  BipartiteWeightedSchurProductBoundWitness
    (BipartiteWeightedSchurBoundTarget.rowBound target)
    (BipartiteWeightedSchurBoundTarget.columnBound target)
    (BipartiteWeightedSchurBoundTarget.productTarget target)
consumeBipartiteWeightedSchurBounds target =
  mkBipartiteWeightedSchurProductBoundWitness
    (BipartiteWeightedSchurBoundTarget.weightedProductBound target)

------------------------------------------------------------------------
-- Typed Nat-Schur handoff.
--
-- The legacy operator witness above is consumed by an older Stage-3 wrapper
-- whose three analytic fields are intentionally left as `Set`.  Keep that
-- compatibility surface unchanged, but expose the constructive Nat algebra
-- separately.  Its hypotheses are the actual Schur-test and scaled
-- row/column inputs; the final operator bound is supplied by the proved
-- `schurTestOpBound` theorem, not by a receipt.

record BipartiteNatSchurHandoff
    (shellIndex operatorNorm rowBound columnBound scaledConstant : Nat) : Set where
  constructor mkBipartiteNatSchurHandoff
  field
    schurTestInput : operatorNorm * operatorNorm ≤ rowBound * columnBound

    scaledRowBoundInput :
      (suc shellIndex * suc shellIndex) * rowBound ≤ scaledConstant

    scaledColumnBoundInput :
      (suc shellIndex * suc shellIndex) * columnBound ≤ scaledConstant

    scaledOperatorBound :
      (suc shellIndex * suc shellIndex) * operatorNorm ≤ scaledConstant

open BipartiteNatSchurHandoff public

bipartiteNatSchurHandoffFromSchurTest :
  (shellIndex operatorNorm rowBound columnBound scaledConstant : Nat) ->
  operatorNorm * operatorNorm ≤ rowBound * columnBound ->
  (suc shellIndex * suc shellIndex) * rowBound ≤ scaledConstant ->
  (suc shellIndex * suc shellIndex) * columnBound ≤ scaledConstant ->
  BipartiteNatSchurHandoff
    shellIndex operatorNorm rowBound columnBound scaledConstant
bipartiteNatSchurHandoffFromSchurTest
  shellIndex operatorNorm rowBound columnBound scaledConstant
  schurTest rowBoundBound columnBoundBound =
  mkBipartiteNatSchurHandoff
    schurTest
    rowBoundBound
    columnBoundBound
    (NatSchur.schurTestOpBound
      operatorNorm rowBound columnBound shellIndex scaledConstant
      schurTest rowBoundBound columnBoundBound)

------------------------------------------------------------------------
-- Typed handoff attached to a concrete weighted target.
--
-- This records exactly what a future concrete operator proof must supply.
-- Constructing it requires the missing analytic inputs, while the resulting
-- scaled operator inequality is completely discharged by Nat algebra.

record BipartiteWeightedSchurNatHandoff
    {residueNormModel : ResidueNorm.ResidueNormModel}
    {shellIndex : Nat}
    (target : BipartiteWeightedSchurBoundTarget residueNormModel shellIndex)
    (operatorNorm scaledConstant : Nat) : Set where
  constructor mkBipartiteWeightedSchurNatHandoff
  field
    schurTestInput :
      operatorNorm * operatorNorm ≤
      BipartiteWeightedSchurBoundTarget.rowBound target *
      BipartiteWeightedSchurBoundTarget.columnBound target

    scaledRowBoundInput :
      (suc shellIndex * suc shellIndex) *
      BipartiteWeightedSchurBoundTarget.rowBound target ≤ scaledConstant

    scaledColumnBoundInput :
      (suc shellIndex * suc shellIndex) *
      BipartiteWeightedSchurBoundTarget.columnBound target ≤ scaledConstant

    scaledOperatorBound :
      (suc shellIndex * suc shellIndex) * operatorNorm ≤ scaledConstant

open BipartiteWeightedSchurNatHandoff public

bipartiteWeightedSchurNatHandoffFromSchurTest :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteWeightedSchurBoundTarget residueNormModel shellIndex) ->
  (operatorNorm scaledConstant : Nat) ->
  operatorNorm * operatorNorm ≤
    BipartiteWeightedSchurBoundTarget.rowBound target *
    BipartiteWeightedSchurBoundTarget.columnBound target ->
  (suc shellIndex * suc shellIndex) *
    BipartiteWeightedSchurBoundTarget.rowBound target ≤ scaledConstant ->
  (suc shellIndex * suc shellIndex) *
    BipartiteWeightedSchurBoundTarget.columnBound target ≤ scaledConstant ->
  BipartiteWeightedSchurNatHandoff target operatorNorm scaledConstant
bipartiteWeightedSchurNatHandoffFromSchurTest
  {shellIndex = shellIndex}
  target operatorNorm scaledConstant schurTest rowBoundBound columnBoundBound =
  mkBipartiteWeightedSchurNatHandoff
    schurTest
    rowBoundBound
    columnBoundBound
    (NatSchur.schurTestOpBound
      operatorNorm
      (BipartiteWeightedSchurBoundTarget.rowBound target)
      (BipartiteWeightedSchurBoundTarget.columnBound target)
      shellIndex
      scaledConstant
      schurTest rowBoundBound columnBoundBound)

------------------------------------------------------------------------
-- Typed Nat-Schur operator surface.
--
-- The rectangular operator is kept separate from the Stage-3 carrier.  The
-- latter is connected only by the explicit embeddings and agreement laws in
-- the consumer bridge below.
------------------------------------------------------------------------

record BipartiteWeightedSchurNatOperatorWitness
    {residueNormModel : ResidueNorm.ResidueNormModel}
    {shellIndex : Nat}
    (target : BipartiteWeightedSchurBoundTarget
      residueNormModel shellIndex)
    (operatorNorm scaledConstant : Nat) : Set₁ where
  constructor mkBipartiteWeightedSchurNatOperatorWitness
  field
    bipartiteQuadraticForm :
      BipartiteSchurSourceCarrier target ->
      BipartiteSchurTargetCarrier target -> Nat

    sameOperatorAsConcreteIncidence :
      (f : BipartiteSchurSourceCarrier target) ->
      (t : BipartiteSchurTargetCarrier target) ->
      bipartiteQuadraticForm f t ≡
      Rectangular.RectangularKernelData.kernel
        (BipartiteWeightedSchurKernelData.kernelData
          (BipartiteWeightedSchurBoundTarget.kernelData target))
        f t

    quantitativeHandoff :
      BipartiteWeightedSchurNatHandoff target operatorNorm scaledConstant

open BipartiteWeightedSchurNatOperatorWitness public

bipartiteWeightedSchurNatOperatorWitnessFromHandoff :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteWeightedSchurBoundTarget
    residueNormModel shellIndex) ->
  (operatorNorm scaledConstant : Nat) ->
  (quadraticForm :
    BipartiteSchurSourceCarrier target ->
    BipartiteSchurTargetCarrier target -> Nat) ->
  ((f : BipartiteSchurSourceCarrier target) ->
   (t : BipartiteSchurTargetCarrier target) ->
   quadraticForm f t ≡
   Rectangular.RectangularKernelData.kernel
     (BipartiteWeightedSchurKernelData.kernelData
       (BipartiteWeightedSchurBoundTarget.kernelData target))
     f t) ->
  BipartiteWeightedSchurNatHandoff target operatorNorm scaledConstant ->
  BipartiteWeightedSchurNatOperatorWitness
    target operatorNorm scaledConstant
bipartiteWeightedSchurNatOperatorWitnessFromHandoff
  target operatorNorm scaledConstant quadraticForm sameOperator handoff =
  mkBipartiteWeightedSchurNatOperatorWitness
    quadraticForm
    sameOperator
    handoff

------------------------------------------------------------------------
-- Generic typed Stage-3 weak-quadratic consumer.
--
-- `qError` is not inferred from a carrier coercion.  A caller must provide
-- both agreement steps:
--
--   qError = stage3OperatorQuadraticForm
--   stage3OperatorQuadraticForm = bipartiteQuadraticForm
--
-- The final scaled estimate is then derived from the operator-norm estimate
-- and the typed Nat handoff.  No closure receipt is constructed here.

record BipartiteWeightedSchurNatStage3WeakQuadraticConsumer
    {residueNormModel : ResidueNorm.ResidueNormModel}
    {shellIndex : Nat}
    (target : BipartiteWeightedSchurBoundTarget
      residueNormModel shellIndex)
    (operatorNorm scaledConstant : Nat) : Set₁ where
  constructor mkBipartiteWeightedSchurNatStage3WeakQuadraticConsumer
  field
    natOperatorWitness :
      BipartiteWeightedSchurNatOperatorWitness
        target operatorNorm scaledConstant

    sourceEmbedding :
      ResidueNorm.Carrier residueNormModel shellIndex ->
      BipartiteSchurSourceCarrier target

    targetEmbedding :
      ResidueNorm.Carrier residueNormModel shellIndex ->
      BipartiteSchurTargetCarrier target

    stage3OperatorQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex -> Nat

    qError :
      ResidueNorm.Carrier residueNormModel shellIndex -> Nat

    qErrorAgreesWithOperator :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) ->
      qError x ≡ stage3OperatorQuadraticForm x

    operatorAgreesWithBipartiteQuadratic :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) ->
      stage3OperatorQuadraticForm x ≡
      BipartiteWeightedSchurNatOperatorWitness.bipartiteQuadraticForm
        natOperatorWitness
        (sourceEmbedding x)
        (targetEmbedding x)

    operatorNormControlsQuadratic :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) ->
      stage3OperatorQuadraticForm x ≤
      operatorNorm *
        ResidueNorm.weakNormSquared residueNormModel shellIndex x

    qErrorScaledBound :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) ->
      (suc shellIndex * suc shellIndex) * qError x ≤
      scaledConstant *
        ResidueNorm.weakNormSquared residueNormModel shellIndex x

    consumerClosed : Bool

open BipartiteWeightedSchurNatStage3WeakQuadraticConsumer public

bipartiteWeightedSchurNatOperatorWitnessToStage3WeakQuadraticConsumer :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteWeightedSchurBoundTarget
    residueNormModel shellIndex) ->
  (operatorNorm scaledConstant : Nat) ->
  (witness :
    BipartiteWeightedSchurNatOperatorWitness
      target operatorNorm scaledConstant) ->
  (sourceEmbedding :
    ResidueNorm.Carrier residueNormModel shellIndex ->
    BipartiteSchurSourceCarrier target) ->
  (targetEmbedding :
    ResidueNorm.Carrier residueNormModel shellIndex ->
    BipartiteSchurTargetCarrier target) ->
  (stage3OperatorQuadraticForm :
    ResidueNorm.Carrier residueNormModel shellIndex -> Nat) ->
  (qError :
    ResidueNorm.Carrier residueNormModel shellIndex -> Nat) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    qError x ≡ stage3OperatorQuadraticForm x) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    stage3OperatorQuadraticForm x ≡
    BipartiteWeightedSchurNatOperatorWitness.bipartiteQuadraticForm
      witness
      (sourceEmbedding x)
      (targetEmbedding x)) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    stage3OperatorQuadraticForm x ≤
    operatorNorm *
      ResidueNorm.weakNormSquared residueNormModel shellIndex x) ->
  BipartiteWeightedSchurNatStage3WeakQuadraticConsumer
    target operatorNorm scaledConstant
bipartiteWeightedSchurNatOperatorWitnessToStage3WeakQuadraticConsumer
  {residueNormModel = residueNormModel}
  {shellIndex = shellIndex}
  target operatorNorm scaledConstant witness
  sourceEmbedding targetEmbedding stage3OperatorQuadraticForm qError
  qErrorAgreesWithOperator operatorAgreesWithBipartiteQuadratic
  operatorNormControlsQuadratic =
  mkBipartiteWeightedSchurNatStage3WeakQuadraticConsumer
    witness
    sourceEmbedding
    targetEmbedding
    stage3OperatorQuadraticForm
    qError
    qErrorAgreesWithOperator
    operatorAgreesWithBipartiteQuadratic
    operatorNormControlsQuadratic
    derivedQErrorScaledBound
    false
  where
    qErrorBound :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) ->
      qError x ≤
      operatorNorm *
        ResidueNorm.weakNormSquared residueNormModel shellIndex x
    qErrorBound x
      rewrite qErrorAgreesWithOperator x =
      operatorNormControlsQuadratic x

    derivedQErrorScaledBound :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) ->
      (suc shellIndex * suc shellIndex) * qError x ≤
      scaledConstant *
        ResidueNorm.weakNormSquared residueNormModel shellIndex x
    derivedQErrorScaledBound x =
      let
        scale = suc shellIndex * suc shellIndex
        normSq = ResidueNorm.weakNormSquared
          residueNormModel shellIndex x
        step1 : scale * qError x ≤ scale * (operatorNorm * normSq)
        step1 = *-mono-≤ (≤-refl {scale}) (qErrorBound x)
        step2-eq : scale * (operatorNorm * normSq) ≡
          (scale * operatorNorm) * normSq
        step2-eq = sym (*-assoc scale operatorNorm normSq)
        step3 : (scale * operatorNorm) * normSq ≤
          scaledConstant * normSq
        step3 = *-mono-≤
          (BipartiteWeightedSchurNatHandoff.scaledOperatorBound
            (BipartiteWeightedSchurNatOperatorWitness.quantitativeHandoff
              witness))
          (≤-refl {normSq})
      in
      ≤-trans step1
        (≤-trans (≤-reflexive step2-eq) step3)

UnitShellBipartiteWeightedSchurNatStage3WeakQuadraticConsumerTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) ->
  (target : BipartiteWeightedSchurBoundTarget residueNormModel (suc zero)) ->
  (operatorNorm scaledConstant : Nat) -> Set₁
UnitShellBipartiteWeightedSchurNatStage3WeakQuadraticConsumerTarget
  residueNormModel target operatorNorm scaledConstant =
  BipartiteWeightedSchurNatStage3WeakQuadraticConsumer
    target operatorNorm scaledConstant

bipartiteWeightedSchurNatStage3WeakQuadraticConsumerClosed : Bool
bipartiteWeightedSchurNatStage3WeakQuadraticConsumerClosed = false

bipartiteWeightedSchurNatStage3WeakQuadraticConsumerClosedIsFalse :
  bipartiteWeightedSchurNatStage3WeakQuadraticConsumerClosed ≡ false
bipartiteWeightedSchurNatStage3WeakQuadraticConsumerClosedIsFalse = refl
