{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact where

------------------------------------------------------------------------
-- R834 / EXACT SPARSE-SUPPORT MAX-CUT FOR R224/R230
--
-- R829's 3-4-5 witness has finite support.  The live repository operators,
-- however, are defined by folds over complete physical output fibres.  This
-- owner removes that representation gap without introducing an estimate:
--
--   * any list fold may be pruned by an executable Bool selector whenever
--     every rejected cell is definitionally zero;
--   * an R224 mixed (+,-) cell is zero when either velocity leg is zero;
--   * an R230 forcing commutator cell is zero when either its p-forcing leg
--     or its q-velocity leg is zero.
--
-- Consequently a concrete R829 evaluator only has to enumerate/evaluate the
-- genuinely active cells.  No global PeriodicHelicalProjectorLaws record,
-- absolute value, shell bound, or time trajectory is required.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact as R437

------------------------------------------------------------------------
-- Generic exact zero-pruning for the repository vector fold.
------------------------------------------------------------------------

filterSelected :
  (Physical.PhysicalTriadIncidence → Bool) →
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
filterSelected select [] = []
filterSelected select (tau ∷ rest) with select tau
... | true = tau ∷ filterSelected select rest
... | false = filterSelected select rest

foldPruneZero :
  ∀ {r : Level} {F : C3.RealField r}
    (select : Physical.PhysicalTriadIncidence → Bool)
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  ((tau : Physical.PhysicalTriadIncidence) →
    select tau ≡ false →
    value tau ≡ C3.complex3Zero F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector value items
  ≡ R224.foldVector value (filterSelected select items)
foldPruneZero select value inactiveZero [] = refl
foldPruneZero {F = F} select value inactiveZero (tau ∷ rest)
  with select tau in decision
... | true =
  cong (C3.complex3Add (value tau))
    (foldPruneZero select value inactiveZero rest)
... | false =
  trans
    (cong₂ C3.complex3Add
      (inactiveZero tau decision)
      (foldPruneZero select value inactiveZero rest))
    (R230.complex3AddZeroLeft
      (R224.foldVector value (filterSelected select rest)))

------------------------------------------------------------------------
-- Zero laws needed for sparse mixed/commutator cells.
------------------------------------------------------------------------

crossZeroLeft :
  ∀ {r : Level} {F : C3.RealField r}
    (v : C3.Complex3 F) →
  Helical.complex3Cross (C3.complex3Zero F) v
  ≡ C3.complex3Zero F
crossZeroLeft {F = F} (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (trans
      (cong₂ C3.complexSubtract
        (Algebra.complexMultiplyZeroLeft vz)
        (Algebra.complexMultiplyZeroLeft vy))
      (Additive.complexSubtractSelf (C3.complexZero F)))
    (trans
      (cong₂ C3.complexSubtract
        (Algebra.complexMultiplyZeroLeft vx)
        (Algebra.complexMultiplyZeroLeft vz))
      (Additive.complexSubtractSelf (C3.complexZero F)))
    (trans
      (cong₂ C3.complexSubtract
        (Algebra.complexMultiplyZeroLeft vy)
        (Algebra.complexMultiplyZeroLeft vx))
      (Additive.complexSubtractSelf (C3.complexZero F)))

mixedPlusMinusZeroFromPVelocityZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  velocity (Physical.p tau) ≡ C3.complex3Zero F →
  R224.mixedPlusMinus S velocity tau ≡ C3.complex3Zero F
mixedPlusMinusZeroFromPVelocityZero
    {E = E} {I = I} S velocity tau pZero =
  trans
    (cong₂ Helical.complex3Cross
      (trans
        (cong
          (Helical.helicalProjectorPlus E I S (Physical.p tau))
          pZero)
        (R437.helicalProjectorPlusZero
          E I S (Physical.p tau)))
      refl)
    (crossZeroLeft
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau) (velocity (Physical.q tau))))

mixedPlusMinusZeroFromQVelocityZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  velocity (Physical.q tau) ≡ C3.complex3Zero F →
  R224.mixedPlusMinus S velocity tau ≡ C3.complex3Zero F
mixedPlusMinusZeroFromQVelocityZero
    {E = E} {I = I} S velocity tau qZero =
  trans
    (cong₂ Helical.complex3Cross
      refl
      (trans
        (cong
          (Helical.helicalProjectorMinus E I S (Physical.q tau))
          qZero)
        (R437.helicalProjectorMinusZero
          E I S (Physical.q tau))))
    (R437.crossZeroRight
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau) (velocity (Physical.p tau))))

forcingCommutatorZeroFromQVelocityZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  velocity (Physical.q tau) ≡ C3.complex3Zero F →
  R230.forcingCommutatorCell S velocity forcing tau
  ≡ C3.complex3Zero F
forcingCommutatorZeroFromQVelocityZero
    {F = F} {E = E} {I = I} S velocity forcing tau qZero =
  let
    qMinusZero =
      trans
        (cong
          (Helical.helicalProjectorMinus E I S (Physical.q tau))
          qZero)
        (R437.helicalProjectorMinusZero E I S (Physical.q tau))
    qPlusZero =
      trans
        (cong
          (Helical.helicalProjectorPlus E I S (Physical.q tau))
          qZero)
        (R437.helicalProjectorPlusZero E I S (Physical.q tau))
  in
  trans
    (cong₂ C3.complex3Subtract
      (trans
        (cong₂ Helical.complex3Cross refl qMinusZero)
        (R437.crossZeroRight
          (Helical.helicalProjectorPlus E I S
            (Physical.p tau) (forcing (Physical.p tau)))))
      (trans
        (cong₂ Helical.complex3Cross refl qPlusZero)
        (R437.crossZeroRight
          (Helical.helicalProjectorMinus E I S
            (Physical.p tau) (forcing (Physical.p tau))))))
    (R106.complex3SubtractSelf (C3.complex3Zero F))

------------------------------------------------------------------------
-- Typed inactive-cell reasons.  These are exactly what a concrete sparse
-- support classifier must provide; no global projector law is hidden here.
------------------------------------------------------------------------

data MixedInactiveReason
    {r : Level} {F : C3.RealField r}
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  mixedPVelocityZero :
    velocity (Physical.p tau) ≡ C3.complex3Zero F →
    MixedInactiveReason velocity tau
  qVelocityZero :
    velocity (Physical.q tau) ≡ C3.complex3Zero F →
    MixedInactiveReason velocity tau

data CommutatorInactiveReason
    {r : Level} {F : C3.RealField r}
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  commPForcingZero :
    forcing (Physical.p tau) ≡ C3.complex3Zero F →
    CommutatorInactiveReason velocity forcing tau
  qVelocityZero :
    velocity (Physical.q tau) ≡ C3.complex3Zero F →
    CommutatorInactiveReason velocity forcing tau

pruneMixedFixedOutput :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (select : Physical.PhysicalTriadIncidence → Bool) →
  ((tau : Physical.PhysicalTriadIncidence) →
    select tau ≡ false → MixedInactiveReason velocity tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (R224.mixedPlusMinus S velocity) items
  ≡
  R224.foldVector (R224.mixedPlusMinus S velocity)
    (filterSelected select items)
pruneMixedFixedOutput S velocity select inactive =
  foldPruneZero select (R224.mixedPlusMinus S velocity) zero
  where
  zero :
    (tau : Physical.PhysicalTriadIncidence) →
    select tau ≡ false →
    R224.mixedPlusMinus S velocity tau ≡ C3.complex3Zero _
  zero tau rejected with inactive tau rejected
  ... |... | mixedPVelocityZero proof =
    mixedPlusMinusZeroFromPVelocityZero S velocity tau proof
  ... |... | mixedQVelocityZero proof =
    mixedPlusMinusZeroFromQVelocityZero S velocity tau proof

pruneCommutatorFixedOutput :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (select : Physical.PhysicalTriadIncidence → Bool) →
  ((tau : Physical.PhysicalTriadIncidence) →
    select tau ≡ false →
    CommutatorInactiveReason velocity forcing tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector
    (R230.forcingCommutatorCell S velocity forcing) items
  ≡
  R224.foldVector
    (R230.forcingCommutatorCell S velocity forcing)
    (filterSelected select items)
pruneCommutatorFixedOutput S velocity forcing select inactive =
  foldPruneZero select
    (R230.forcingCommutatorCell S velocity forcing) zero
  where
  zero :
    (tau : Physical.PhysicalTriadIncidence) →
    select tau ≡ false →
    R230.forcingCommutatorCell S velocity forcing tau
    ≡ C3.complex3Zero _
  zero tau rejected with inactive tau rejected
  ... |... | commPForcingZero proof =
    R437.forcingCommutatorZeroFromForcingZero
      S velocity forcing tau proof
  ... |... | commQVelocityZero proof =
    forcingCommutatorZeroFromQVelocityZero
      S velocity forcing tau proof

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round834GenericExactZeroPruningClosed : Bool
round834GenericExactZeroPruningClosed = true

round834MixedCellSparseSupportPruningClosed : Bool
round834MixedCellSparseSupportPruningClosed = true

round834CommutatorSparseSupportPruningClosed : Bool
round834CommutatorSparseSupportPruningClosed = true

round834GlobalHelicalProjectorLawsRequired : Bool
round834GlobalHelicalProjectorLawsRequired = false

round834IntroducesEstimate : Bool
round834IntroducesEstimate = false

round834ClayPromotion : Bool
round834ClayPromotion = false

round834GenericExactZeroPruningClosedIsTrue :
  round834GenericExactZeroPruningClosed ≡ true
round834GenericExactZeroPruningClosedIsTrue = refl

round834GlobalHelicalProjectorLawsRequiredIsFalse :
  round834GlobalHelicalProjectorLawsRequired ≡ false
round834GlobalHelicalProjectorLawsRequiredIsFalse = refl
