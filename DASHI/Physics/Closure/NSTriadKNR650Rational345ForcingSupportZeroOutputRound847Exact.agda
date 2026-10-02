{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportZeroOutputRound847Exact where

------------------------------------------------------------------------
-- R847 / CORRECT THE R846 SUPPORT CUT: ZERO OUTPUT IS ACTIVE-PAIR POPULATED
--
-- R846 proposed the stronger combinatorial leaf
--
--   forcingActive k = false ->
--   filterSelected mixedCellActive (physicalOutputFiber 4 k) = [].
--
-- That leaf is stronger than the physical forcing theorem and is not the
-- correct target at k=0: the reality-paired six-mode seed has active pairs
-- p,-p with p+(-p)=0.  The literal NS ordered interaction nevertheless
-- vanishes at output zero by R436, using transversality.
--
-- Therefore split the actual same-object forcing proof exactly where the
-- repository mathematics splits:
--
--   k = 0: R436 pays projectedNonlinearity k = 0;
--
--   k != 0 and forcingActive k = false:
--     only here require the finite seed-pair support exhaustion
--
--       filterSelected mixedCellActive (physicalOutputFiber 4 k) = [].
--
-- This removes the false/overstrong zero-output list-emptiness target without
-- weakening the desired all-mode equality
--
--   projectedNonlinearity directSystem k = forcing345 k.
--
-- The remaining finite F1' leaf is now:
--   inactive NONZERO output -> no active seed-seed incidence in its fibre.
-- F2 (active R224/R230 helical vector evaluation) remains independent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveRepositoryReductionRound837Exact as R837
import DASHI.Physics.Closure.NSTriadKNR650Rational345ProjectedNonlinearityPruneRound840Exact as R840
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportRound845Exact as R845

F : C3.RealField _
F = Rational.rationalRealField

InactiveNonzeroActiveFibreEmpty : Set
InactiveNonzeroActiveFibreEmpty =
  (mode : Z3.FourierMode) →
  Snapshot.forcingActive mode ≡ false →
  Output.modeEqual mode Z3.zeroMode ≡ false →
  Sparse.filterSelected Snapshot.mixedCellActive
    (Output.physicalOutputFiber 4 mode)
  ≡ []

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E)
    (supportEmpty : InactiveNonzeroActiveFibreEmpty) where

  system = Direct.directAuditSystem E I
  module P = R840.SparseR30 system (Direct.directVelocitySame E I)

  inactiveProjectedZero :
    (mode : Z3.FourierMode) →
    Snapshot.forcingActive mode ≡ false →
    Audit.projectedNonlinearity system mode ≡ C3.complex3Zero F
  inactiveProjectedZero mode inactive
    with Output.modeEqual mode Z3.zeroMode in zeroDecision
  ... | true =
      subst
        (λ selected →
          Audit.projectedNonlinearity system selected
          ≡ C3.complex3Zero F)
        (sym (Output.modeEqualSound zeroDecision))
        (R436.projectedNonlinearityAtZeroIsZero
          system (Direct.snapshotVelocityTransverse E))
  ... | false =
      trans
        (P.projectedNonlinearityIsActiveR30Fold mode)
        tail
    where
    tail : P.activeR30Fold mode ≡ C3.complex3Zero F
    tail rewrite supportEmpty mode inactive zeroDecision = refl

  module Full = R845.Evaluate unit I inactiveProjectedZero

  modalSameObject :
    R837.Repository345ModalSameObject (Direct.directPhysicalSystem E I)
  modalSameObject = Full.modalSameObject

  module Reduction =
    R837.Reduction (Direct.directPhysicalSystem E I) modalSameObject

round847R846ZeroOutputListEmptinessRequired : Bool
round847R846ZeroOutputListEmptinessRequired = false

round847ZeroOutputPaidByLiteralR436 : Bool
round847ZeroOutputPaidByLiteralR436 = true

round847ForcingSameObjectReducedToInactiveNonzeroSupportEmpty : Bool
round847ForcingSameObjectReducedToInactiveNonzeroSupportEmpty = true

round847InactiveNonzeroSupportEmptyClosed : Bool
round847InactiveNonzeroSupportEmptyClosed = false

round847ActiveR224R230VectorEvaluationClosed : Bool
round847ActiveR224R230VectorEvaluationClosed = false

round847AdditionalAnalyticEstimateRequired : Bool
round847AdditionalAnalyticEstimateRequired = false

round847ClayPromotion : Bool
round847ClayPromotion = false

round847R846ZeroOutputListEmptinessRequiredIsFalse :
  round847R846ZeroOutputListEmptinessRequired ≡ false
round847R846ZeroOutputListEmptinessRequiredIsFalse = refl

round847ZeroOutputPaidByLiteralR436IsTrue :
  round847ZeroOutputPaidByLiteralR436 ≡ true
round847ZeroOutputPaidByLiteralR436IsTrue = refl

round847ForcingSameObjectReducedToInactiveNonzeroSupportEmptyIsTrue :
  round847ForcingSameObjectReducedToInactiveNonzeroSupportEmpty ≡ true
round847ForcingSameObjectReducedToInactiveNonzeroSupportEmptyIsTrue = refl
