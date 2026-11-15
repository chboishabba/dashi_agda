{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportMaxCutRound846Exact where

------------------------------------------------------------------------
-- R846 / HISTORICAL FULL MODAL R30 SUPPORT MAX-CUT (SUPERSEDED BY R851)
--
-- R840 already says the literal projected nonlinearity is the fold over only
-- seed-seed cells.  R845 already says the eight nonzero forcing rows are exact.
-- Therefore the entire remaining modal forcing weld is equivalent to one
-- finite combinatorial support statement:
--
--   forcingActive k = false
--     -> filterSelected mixedCellActive (physicalOutputFiber 4 k) = [].
--
-- From that list equality this file derives, without any estimate:
--
--   projectedNonlinearity k = 0
--   projectedNonlinearity k = Snapshot.forcing345 k
--   R837.Repository345ModalSameObject.
--
-- CORRECTION: F1 as stated is FALSE at output k=0, because the
-- velocity support contains opposite active seed pairs (p,-p) with sum 0.
-- The true mathematical decomposition is:
--   nonzero inactive k: R848 proves the active fibre is empty;
--   zero k: R436 proves the full projected nonlinear fold is zero from
--           transversality, even though active pairs occur.
-- R851 uses exactly these two theorems to inhabit R845.modalSameObject.
-- R852 then uses R837/R845/R846 actual-row evaluations to inhabit R829D.
-- This historical conditional theorem is retained but its universal
-- support-empty input must NOT be treated as an achievable obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveRepositoryReductionRound837Exact as R837
import DASHI.Physics.Closure.NSTriadKNR650Rational345ProjectedNonlinearityPruneRound840Exact as R840
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportRound845Exact as R845

F : C3.RealField _
F = Rational.rationalRealField

InactiveActiveFibreEmpty : Set
InactiveActiveFibreEmpty =
  (mode : Z3.FourierMode) →
  Snapshot.forcingActive mode ≡ false →
  Sparse.filterSelected Snapshot.mixedCellActive
    (Output.physicalOutputFiber 4 mode)
  ≡ []

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E)
    (supportEmpty : InactiveActiveFibreEmpty) where

  system = Direct.directAuditSystem E I
  module P = R840.SparseR30 system (Direct.directVelocitySame E I)

  inactiveProjectedZero :
    (mode : Z3.FourierMode) →
    Snapshot.forcingActive mode ≡ false →
    Audit.projectedNonlinearity system mode ≡ C3.complex3Zero F
  inactiveProjectedZero mode inactive =
    trans
      (P.projectedNonlinearityIsActiveR30Fold mode)
      tail
    where
    tail : P.activeR30Fold mode ≡ C3.complex3Zero F
    tail rewrite supportEmpty mode inactive = refl

  module Full = R845.Evaluate unit I inactiveProjectedZero

  modalSameObject :
    R837.Repository345ModalSameObject (Direct.directPhysicalSystem E I)
  modalSameObject = Full.modalSameObject

  module Reduction =
    R837.Reduction (Direct.directPhysicalSystem E I) modalSameObject

round846ForcingSameObjectReducedToFiniteSupportEmpty : Bool
round846ForcingSameObjectReducedToFiniteSupportEmpty = true

round846InactiveProjectedZeroDerivedFromSupportEmpty : Bool
round846InactiveProjectedZeroDerivedFromSupportEmpty = true

round846ModalSameObjectDerivedFromSupportEmpty : Bool
round846ModalSameObjectDerivedFromSupportEmpty = true

round846UnrestrictedSupportEmptyFalseAtZero : Bool
round846UnrestrictedSupportEmptyFalseAtZero = true

round846ReplacedByR851ZeroModeSplit : Bool
round846ReplacedByR851ZeroModeSplit = true

round846FiniteSupportEmptyClosed : Bool
round846FiniteSupportEmptyClosed = false

round846ActiveR224R230VectorEvaluationClosed : Bool
round846ActiveR224R230VectorEvaluationClosed = false

round846AdditionalAnalyticEstimateRequired : Bool
round846AdditionalAnalyticEstimateRequired = false

round846ClayPromotion : Bool
round846ClayPromotion = false

round846ForcingSameObjectReducedToFiniteSupportEmptyIsTrue :
  round846ForcingSameObjectReducedToFiniteSupportEmpty ≡ true
round846ForcingSameObjectReducedToFiniteSupportEmptyIsTrue = refl
