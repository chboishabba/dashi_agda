{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportRound845Exact where

------------------------------------------------------------------------
-- R845 / ACTIVE R30 ROWS -> FULL MODAL SAME-OBJECT SUPPORT BOUNDARY
--
-- R844 kernel-targets the literal projected nonlinearity on all eight modes
-- where Snapshot.forcing345 is nonzero.  This owner removes those eight rows
-- from the remaining R829D burden.
--
-- The only forcing same-object fact still needed is now the support theorem:
--
--   forcingActive k = false
--     -> Audit.projectedNonlinearity directSystem k = 0.
--
-- Once that single statement is supplied, the complete modal equality
--
--   Audit.projectedNonlinearity directSystem k = Snapshot.forcing345 k
--
-- follows for every Fourier mode, and R837's modal same-object record is
-- inhabited.  No helical/projector arithmetic and no scalar estimate occurs
-- here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveRepositoryReductionRound837Exact as R837
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingRowsRound844Exact as R844
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output

F : C3.RealField _
F = Rational.rationalRealField

data ForcingActiveHit (mode : Z3.FourierMode) : Set where
  hit₁ : mode ≡ Active.k₁ → ForcingActiveHit mode
  hit₂ : mode ≡ Active.k₂ → ForcingActiveHit mode
  hit₃ : mode ≡ Active.k₃ → ForcingActiveHit mode
  hit₄ : mode ≡ Active.k₄ → ForcingActiveHit mode
  hit₅ : mode ≡ Active.k₅ → ForcingActiveHit mode
  hit₆ : mode ≡ Active.k₆ → ForcingActiveHit mode
  hit₇ : mode ≡ Active.k₇ → ForcingActiveHit mode
  hit₈ : mode ≡ Active.k₈ → ForcingActiveHit mode

forcingActiveSound :
  (mode : Z3.FourierMode) →
  Snapshot.forcingActive mode ≡ true →
  ForcingActiveHit mode
forcingActiveSound mode active
  with Output.modeEqual mode Active.k₁ in d₁
... | true = hit₁ (Output.modeEqualSound d₁)
... | false
  with Output.modeEqual mode Active.k₂ in d₂
... | true = hit₂ (Output.modeEqualSound d₂)
... | false
  with Output.modeEqual mode Active.k₃ in d₃
... | true = hit₃ (Output.modeEqualSound d₃)
... | false
  with Output.modeEqual mode Active.k₄ in d₄
... | true = hit₄ (Output.modeEqualSound d₄)
... | false
  with Output.modeEqual mode Active.k₅ in d₅
... | true = hit₅ (Output.modeEqualSound d₅)
... | false
  with Output.modeEqual mode Active.k₆ in d₆
... | true = hit₆ (Output.modeEqualSound d₆)
... | false
  with Output.modeEqual mode Active.k₇ in d₇
... | true = hit₇ (Output.modeEqualSound d₇)
... | false
  with Output.modeEqual mode Active.k₈ in d₈
... | true = hit₈ (Output.modeEqualSound d₈)
... | false = Output.falseNotTrue active

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E)
    (inactiveProjectedZero :
      (mode : Z3.FourierMode) →
      Snapshot.forcingActive mode ≡ false →
      Audit.projectedNonlinearity (Direct.directAuditSystem E I) mode
      ≡ C3.complex3Zero F) where

  module Rows = R844.Evaluate unit I

  forcingSame :
    (mode : Z3.FourierMode) →
    Audit.projectedNonlinearity (Direct.directAuditSystem E I) mode
    ≡ Snapshot.forcing345 mode
  forcingSame mode with Snapshot.forcingActive mode in active
  ... | false =
    trans
      (inactiveProjectedZero mode active)
      (sym (Snapshot.forcingInactiveZero mode active))
  ... | true with forcingActiveSound mode active
  ...   | hit₁ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₁
  ...   | hit₂ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₂
  ...   | hit₃ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₃
  ...   | hit₄ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₄
  ...   | hit₅ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₅
  ...   | hit₆ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₆
  ...   | hit₇ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₇
  ...   | hit₈ same =
      subst
        (λ selected →
          Audit.projectedNonlinearity (Direct.directAuditSystem E I) selected
          ≡ Snapshot.forcing345 selected)
        (sym same)
        Rows.forcing₈

  modalSameObject :
    R837.Repository345ModalSameObject (Direct.directPhysicalSystem E I)
  modalSameObject = record
    { R837.cutoffIsFour = refl
    ; R837.velocitySame = Direct.directVelocitySame E I
    ; R837.forcingSame = forcingSame
    }

round845EightActiveRowsConsumed : Bool
round845EightActiveRowsConsumed = true

round845FullModalForcingReducedToInactiveSupportZero : Bool
round845FullModalForcingReducedToInactiveSupportZero = true

round845InactiveSupportZeroClosed : Bool
round845InactiveSupportZeroClosed = false

round845AdditionalNumericalOracleRequired : Bool
round845AdditionalNumericalOracleRequired = false

round845ClayPromotion : Bool
round845ClayPromotion = false

round845EightActiveRowsConsumedIsTrue :
  round845EightActiveRowsConsumed ≡ true
round845EightActiveRowsConsumedIsTrue = refl

round845FullModalForcingReducedToInactiveSupportZeroIsTrue :
  round845FullModalForcingReducedToInactiveSupportZero ≡ true
round845FullModalForcingReducedToInactiveSupportZeroIsTrue = refl
