{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ProjectedNonlinearityPruneRound840Exact where

------------------------------------------------------------------------
-- R840 / EXACT R30 SPARSE PRUNING FOR THE 3-4-5 SNAPSHOT
--
-- R829D is now blocked only on concrete operator evaluation.  This owner
-- removes the 728-cube burden for R30 itself: an ordered projected nonlinear
-- cell is definitionally zero whenever either input velocity is zero.
--
-- Therefore, for any repository system whose velocity is the selected sparse
-- 3-4-5 velocity, projectedNonlinearity at a fixed output equals the fold over
-- only the finite seed-pair incidences selected by Snapshot.mixedCellActive.
--
-- No estimate, helicity law, time trajectory, or forcing support theorem is
-- used.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelEndpointZeroRound164Exact as R164
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact as R310
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot

projectedOrderedTermZeroFromPVelocityZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Audit.velocity system (Physical.p tau) ≡ C3.complex3Zero F →
  Audit.projectedOrderedTerm system tau ≡ C3.complex3Zero F
projectedOrderedTermZeroFromPVelocityZero {F = F} {E = E} {I = I}
    system tau pZero =
  let
    p = Physical.p tau
    q = Physical.q tau
    k = Physical.k tau
    dotZero :
      C3.bilinearDot3
        (Audit.velocity system p)
        (C3.modeVector E q)
      ≡ C3.complexZero F
    dotZero =
      trans
        (cong
          (λ u → C3.bilinearDot3 u (C3.modeVector E q))
          pZero)
        (R164.bilinearDot3ZeroLeft (C3.modeVector E q))

    innerZero :
      C3.complex3Scale
        (C3.bilinearDot3
          (Audit.velocity system p)
          (C3.modeVector E q))
        (Audit.velocity system q)
      ≡ C3.complex3Zero F
    innerZero =
      trans
        (cong
          (λ scalar → C3.complex3Scale scalar (Audit.velocity system q))
          dotZero)
        (R106.complex3ScaleZeroScalar (Audit.velocity system q))
  in
  trans
    (cong
      (C3.complex3Scale (C3.complexNegate (C3.complexI F)))
      (trans
        (cong (C3.lerayProject3 E I k) innerZero)
        (R436.lerayZeroVector E I k)))
    (R106.complex3ScaleZeroVector
      (C3.complexNegate (C3.complexI F)))

projectedOrderedTermZeroFromQVelocityZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Audit.velocity system (Physical.q tau) ≡ C3.complex3Zero F →
  Audit.projectedOrderedTerm system tau ≡ C3.complex3Zero F
projectedOrderedTermZeroFromQVelocityZero {F = F} {E = E} {I = I}
    system tau qZero =
  let
    p = Physical.p tau
    q = Physical.q tau
    k = Physical.k tau
    innerZero :
      C3.complex3Scale
        (C3.bilinearDot3
          (Audit.velocity system p)
          (C3.modeVector E q))
        (Audit.velocity system q)
      ≡ C3.complex3Zero F
    innerZero =
      trans
        (cong
          (C3.complex3Scale
            (C3.bilinearDot3
              (Audit.velocity system p)
              (C3.modeVector E q)))
          qZero)
        (R106.complex3ScaleZeroVector
          (C3.bilinearDot3
            (Audit.velocity system p)
            (C3.modeVector E q)))
  in
  trans
    (cong
      (C3.complex3Scale (C3.complexNegate (C3.complexI F)))
      (trans
        (cong (C3.lerayProject3 E I k) innerZero)
        (R436.lerayZeroVector E I k)))
    (R106.complex3ScaleZeroVector
      (C3.complexNegate (C3.complexI F)))

module SparseR30
    {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocitySame :
      (mode : Z3.FourierMode) →
      Audit.velocity system mode ≡ Snapshot.velocity345 mode) where

  actualInactive :
    (tau : Physical.PhysicalTriadIncidence) →
    Snapshot.mixedCellActive tau ≡ false →
    Sparse.MixedInactiveReason (Audit.velocity system) tau
  actualInactive tau rejected
    with Snapshot.mixedInactiveReason tau rejected
  ... | Sparse.mixedPVelocityZero proof =
    Sparse.mixedPVelocityZero
      (trans (velocitySame (Physical.p tau)) proof)
  ... | Sparse.mixedQVelocityZero proof =
    Sparse.mixedQVelocityZero
      (trans (velocitySame (Physical.q tau)) proof)

  activeR30Fold :
    Z3.FourierMode → C3.Complex3 F
  activeR30Fold output =
    R224.foldVector
      (Audit.projectedOrderedTerm system)
      (Sparse.filterSelected Snapshot.mixedCellActive
        (Output.physicalOutputFiber (Audit.cutoff system) output))

  projectedNonlinearityIsActiveR30Fold :
    (output : Z3.FourierMode) →
    Audit.projectedNonlinearity system output
    ≡ activeR30Fold output
  projectedNonlinearityIsActiveR30Fold output =
    trans
      (R310.projectedNonlinearityAsFold system output)
      (Sparse.foldPruneZero
        Snapshot.mixedCellActive
        (Audit.projectedOrderedTerm system)
        zero
        (Output.physicalOutputFiber (Audit.cutoff system) output))
    where
    zero :
      (tau : Physical.PhysicalTriadIncidence) →
      Snapshot.mixedCellActive tau ≡ false →
      Audit.projectedOrderedTerm system tau ≡ C3.complex3Zero F
    zero tau rejected with actualInactive tau rejected
    ... | Sparse.mixedPVelocityZero proof =
      projectedOrderedTermZeroFromPVelocityZero system tau proof
    ... | Sparse.mixedQVelocityZero proof =
      projectedOrderedTermZeroFromQVelocityZero system tau proof

round840R30SparseZeroPruningClosed : Bool
round840R30SparseZeroPruningClosed = true

round840ProjectedNonlinearityReducedToSeedPairs : Bool
round840ProjectedNonlinearityReducedToSeedPairs = true

round840AdditionalAnalyticEstimateRequired : Bool
round840AdditionalAnalyticEstimateRequired = false

round840ClayPromotion : Bool
round840ClayPromotion = false

round840ProjectedNonlinearityReducedToSeedPairsIsTrue :
  round840ProjectedNonlinearityReducedToSeedPairs ≡ true
round840ProjectedNonlinearityReducedToSeedPairsIsTrue = refl
