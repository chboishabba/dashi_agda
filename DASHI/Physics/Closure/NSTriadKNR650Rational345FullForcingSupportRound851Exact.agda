{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345FullForcingSupportRound851Exact where

------------------------------------------------------------------------
-- R851 / CORRECT ALL-OUTPUT R30 SUPPORT FOR THE RATIONAL 3-4-5 SNAPSHOT
--
-- The R846 proposed universal "inactive -> active-fibre empty" premise is
-- TOO STRONG at k = 0: opposite nonzero seed modes p and -p can be active
-- even though their output is zero.
--
-- Use the two ACTUAL physical cancellation theorems instead:
--   k = 0: R436 shows every ordered nonlinear term vanishes because
--          u_p is transverse to p and q = -p.
--   k != 0, forcingActive k = false: R848 proves the active finite
--          seed-pair incidence list is empty; R840 prunes the full
--          projected Fourier sum to precisely that list.
--
-- Consequently, the R845 conditional forcingSame theorem is inhabited
-- without assuming an impossible empty active fibre at output zero.
-- This also inhabits R837.Repository345ModalSameObject on the concrete
-- R841 physical state. No global rational helical laws or real ODE are used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveRepositoryReductionRound837Exact as R837
import DASHI.Physics.Closure.NSTriadKNR650Rational345ProjectedNonlinearityPruneRound840Exact as R840
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportRound845Exact as R845
import DASHI.Physics.Closure.NSTriadKNR650Rational345MixedOutputSupportRound848Exact as R848

F : C3.RealField _
F = Rational.rationalRealField

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  system = Direct.directAuditSystem E I
  module P = R840.SparseR30 system (Direct.directVelocitySame E I)

  nonzeroIfNotZero :
    (mode : Z3.FourierMode) →
    Output.modeEqual mode Z3.zeroMode ≡ false →
    Z3.NonZeroMode mode
  nonzeroIfNotZero mode unequal = record
    { Z3.notZero = λ eq →
        Output.falseNotTrue
          (trans (sym unequal) (Output.modeEqualComplete eq))
    }

  inactiveProjectedZero :
    (mode : Z3.FourierMode) →
    Snapshot.forcingActive mode ≡ false →
    Audit.projectedNonlinearity system mode ≡ C3.complex3Zero F
  inactiveProjectedZero mode inactive
    with Output.modeEqual mode Z3.zeroMode in isZero
  ... | true =
    subst
      (λ selected →
        Audit.projectedNonlinearity system selected
        ≡ C3.complex3Zero F)
      (sym (Output.modeEqualSound isZero))
      (R436.projectedNonlinearityAtZeroIsZero
        system (Direct.snapshotVelocityTransverse E))
  ... | false =
    trans
      (P.projectedNonlinearityIsActiveR30Fold mode)
      (cong
        (R224.foldVector (Audit.projectedOrderedTerm system))
        (R848.mixedFilterEmptyAtInactiveNonzero
          mode (nonzeroIfNotZero mode isZero) inactive))

  module Full = R845.Evaluate unit I inactiveProjectedZero

  forcingSame :
    (mode : Z3.FourierMode) →
    Audit.projectedNonlinearity system mode
      ≡ Snapshot.forcing345 mode
  forcingSame = Full.forcingSame

  modalSameObject :
    R837.Repository345ModalSameObject (Direct.directPhysicalSystem E I)
  modalSameObject = Full.modalSameObject

round851ZeroOutputUsesTransverseCancellation : Bool
round851ZeroOutputUsesTransverseCancellation = true

round851InactiveNonzeroOutputsUseSparseSupport : Bool
round851InactiveNonzeroOutputsUseSparseSupport = true

round851FullModalForcingSameObjectClosed : Bool
round851FullModalForcingSameObjectClosed = true

round851R846UnconditionalEmptyListAssumptionNeeded : Bool
round851R846UnconditionalEmptyListAssumptionNeeded = false

round851RealODETransportClosed : Bool
round851RealODETransportClosed = false

round851ClayPromotion : Bool
round851ClayPromotion = false

round851FullModalForcingSameObjectClosedIsTrue :
  round851FullModalForcingSameObjectClosed ≡ true
round851FullModalForcingSameObjectClosedIsTrue = refl
