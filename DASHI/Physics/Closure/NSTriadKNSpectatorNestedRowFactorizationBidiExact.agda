module DASHI.Physics.Closure.NSTriadKNSpectatorNestedRowFactorizationBidiExact where

------------------------------------------------------------------------
-- SPECTATOR ROW -> NESTED SIGNED FORCE FOLD BIDI
--
-- This is the shortest exact composition exposed by the cross-repository
-- signed-first audit.
--
-- R542 already proves, on a complete fixed-output fibre, that the
-- spectator-resolvent weighted double forcing folds to four copies of the
-- R294 commutator fold.
--
-- The preceding R541 x R573 specialization proves that the pointwise fourfold
-- weighted R294 commutator carrier is exactly the nested four-sign inner
-- commutator carrier.
--
-- Therefore the FORCE half of R545's literal scalar spectator row may be
-- contracted directly against the nested signed fold, before any norm or
-- absolute value.  The independent AMPLITUDE half remains explicit and is not
-- claimed paid here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Rational.Base using (_*_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleForcingCommutatorFoldRound542Exact as R542
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as Weld

module NestedRow
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem Weld.F)
    (S : Helical.HelicalModeScalars Weld.F)
    (L : Helical.PeriodicHelicalProjectorLaws Weld.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Row = R545.Row physicalSystem S
  module SN = Weld.SpectatorNested physicalSystem S L H velocityTransverse

  system = Field30.finiteSystem physicalSystem

  -- The R573 source fold is definitionally four copies of the same R294
  -- commutator cell used by R542/R545.  Finite additivity moves only the sums;
  -- it inserts no norm or sign erasure.
  foldFourNestedSourceIsFourCommutatorFolds :
    (beta : Physical.PhysicalTriadIncidence) →
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        C = R224.foldVector (Row.Weighted.Force.commutator beta) items
    in
    R224.foldVector
      (λ alpha → C3.complex3Add
        (R438.doubleWeightedProjectedForcingCell
          (Row.Weighted.W beta) S system alpha)
        (R438.doubleWeightedProjectedForcingCell
          (Row.Weighted.W beta) S system alpha))
      items
    ≡ C3.complex3Add (C3.complex3Add C C) (C3.complex3Add C C)
  foldFourNestedSourceIsFourCommutatorFolds beta output =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      Ccell = Row.Weighted.Force.commutator beta
      Dcell = R438.doubleWeightedProjectedForcingCell
        (Row.Weighted.W beta) S system
    in
    trans
      (R230.foldAdd Dcell Dcell items)
      (cong₂ C3.complex3Add
        (R230.foldAdd Ccell Ccell items)
        (R230.foldAdd Ccell Ccell items))

  -- The four-commutator force aggregate is exactly the nested four-sign fold.
  fourCommutatorFoldsAreNested :
    (beta : Physical.PhysicalTriadIncidence) →
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        C = R224.foldVector (Row.Weighted.Force.commutator beta) items
        module N = SN.Nested beta
    in
    C3.complex3Add (C3.complex3Add C C) (C3.complex3Add C C)
    ≡ R224.foldVector N.nestedWeightedCompanionCell items
  fourCommutatorFoldsAreNested beta output =
    trans
      (sym (foldFourNestedSourceIsFourCommutatorFolds beta output))
      (SN.fixedOutputFourSpectatorResolvedR294IsNested beta output)

  -- Hence R542's physical spectator-weighted double forcing aggregate lands
  -- directly on the R573 nested carrier.
  weightedDoubleForcingFoldIsNested :
    (beta : Physical.PhysicalTriadIncidence) →
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        module N = SN.Nested beta
    in
    R224.foldVector (Row.Weighted.Force.weightedDouble beta) items
    ≡ R224.foldVector N.nestedWeightedCompanionCell items
  weightedDoubleForcingFoldIsNested beta output =
    trans
      (Row.Weighted.Force.fixedOutputWeightedDoubleIsFourCommutatorFolds
        beta output)
      (fourCommutatorFoldsAreNested beta output)

  -- Exact scalar consequence for R545.  Only the force half is normalized into
  -- the nested signed carrier; the amplitude half remains a separate literal
  -- term and therefore remains visible to subsequent proof search.
  fixedOutputSpectatorRowFactorsThroughNestedForce :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        module N = SN.Nested beta
        nestedForce = R224.foldVector N.nestedWeightedCompanionCell items
        A = R224.foldVector (Row.Weighted.Amp.amplitude beta) items
        fourA = C3.complex3Add (C3.complex3Add A A) (C3.complex3Add A A)
    in
    Row.spectatorRow beta items
    ≡ R291.two *
        (R179.realHermitianCross nestedForce (Row.doubleCell beta)
        + R179.realHermitianCross fourA (Row.D.doubleForcing beta))
  fixedOutputSpectatorRowFactorsThroughNestedForce output beta =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      C = R224.foldVector (Row.Weighted.Force.commutator beta) items
      fourC = C3.complex3Add (C3.complex3Add C C) (C3.complex3Add C C)
      A = R224.foldVector (Row.Weighted.Amp.amplitude beta) items
      fourA = C3.complex3Add (C3.complex3Add A A) (C3.complex3Add A A)
    in
    trans
      (Row.fixedOutputSpectatorRowFactorsThroughR294 output beta)
      (cong
        (λ forceAggregate →
          R291.two *
            (R179.realHermitianCross forceAggregate (Row.doubleCell beta)
            + R179.realHermitianCross fourA (Row.D.doubleForcing beta)))
        (fourCommutatorFoldsAreNested beta output))

------------------------------------------------------------------------
-- BIDI / status firewalls.
------------------------------------------------------------------------

spectatorNestedForceRowSameObjectWeldClosed : Bool
spectatorNestedForceRowSameObjectWeldClosed = true

spectatorNestedForceRowNormInsertedBeforeNestedCancellation : Bool
spectatorNestedForceRowNormInsertedBeforeNestedCancellation = false

spectatorNestedAmplitudeHalfPaid : Bool
spectatorNestedAmplitudeHalfPaid = false

spectatorNestedSignedSpacetimeEstimatePaid : Bool
spectatorNestedSignedSpacetimeEstimatePaid = false

spectatorNestedR503CutoffUniformBudgetPaid : Bool
spectatorNestedR503CutoffUniformBudgetPaid = false

spectatorNestedClayPromotion : Bool
spectatorNestedClayPromotion = false

spectatorNestedForceRowSameObjectWeldClosedIsTrue :
  spectatorNestedForceRowSameObjectWeldClosed ≡ true
spectatorNestedForceRowSameObjectWeldClosedIsTrue = refl

spectatorNestedAmplitudeHalfPaidIsFalse :
  spectatorNestedAmplitudeHalfPaid ≡ false
spectatorNestedAmplitudeHalfPaidIsFalse = refl

spectatorNestedSignedSpacetimeEstimatePaidIsFalse :
  spectatorNestedSignedSpacetimeEstimatePaid ≡ false
spectatorNestedSignedSpacetimeEstimatePaidIsFalse = refl

spectatorNestedClayPromotionIsFalse : spectatorNestedClayPromotion ≡ false
spectatorNestedClayPromotionIsFalse = refl
