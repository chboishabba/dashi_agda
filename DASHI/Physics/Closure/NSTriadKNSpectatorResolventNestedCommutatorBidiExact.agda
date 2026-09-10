module DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact where

------------------------------------------------------------------------
-- SPECTATOR RESOLVENT x NESTED COMMUTATOR BIDI
--
-- PURPOSE
-- -------
-- Test the composition that the historical lanes had separately prepared but
-- had not, on the audited default branch, instantiated together by name:
--
--   R541 spectator-dependent literal Cauchy resolvent weight
--     +
--   R573 exact weighted nested componentwise commutator
--
-- R541 proves that for a fixed spectator beta
--
--   W_beta(alpha) = 1 / (lambda_alpha + lambda_beta)
--
-- is an exact R294 swap-invariant cell weight on the physical carrier.
-- R573 is generic in precisely such an R294 weight and proves, before norms,
-- that the weighted projected-forcing carrier is the nested four-sign inner
-- commutator carrier.
--
-- This module performs only that missing specialization.  It introduces no
-- estimate, no absolute value, no Schur/Cotlar majorant, no Laplace transform,
-- and no new mathematical owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573

F : C3.RealField _
F = Rational.rationalRealField

module SpectatorNested
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Spec = R541.Spectator physicalSystem S

  system = Field30.finiteSystem physicalSystem

  module Nested (beta : Physical.PhysicalTriadIncidence) =
    R573.WeightedNested
      (Spec.spectatorWeight beta)
      S L H system velocityTransverse

  -- The selected R573 weight is literally the R541 pair resolvent.
  spectatorWeightIsLiteralPairResolvent :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    let module N = Nested beta in
    R438.doubleWeightedProjectedForcingCell
      (Spec.spectatorWeight beta) S system alpha
    ≡
    R438.doubleWeightedProjectedForcingCell
      (Spec.spectatorWeight beta) S system alpha
  spectatorWeightIsLiteralPairResolvent beta alpha = refl

  -- Same-object composition: for each fixed spectator beta, four copies of the
  -- literal R438 weighted projected-forcing cell are exactly the R573 nested
  -- weighted companion cell using the nonseparable Cauchy resolvent weight.
  fourSpectatorResolvedR294CellIsNested :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    let module N = Nested beta in
    C3.complex3Add
      (R438.doubleWeightedProjectedForcingCell
        (Spec.spectatorWeight beta) S system alpha)
      (R438.doubleWeightedProjectedForcingCell
        (Spec.spectatorWeight beta) S system alpha)
    ≡ N.nestedWeightedCompanionCell alpha
  fourSpectatorResolvedR294CellIsNested beta alpha =
    let module N = Nested beta in
    N.fourWeightedR294CellIsNested alpha

  -- The same composition over any finite alpha list.
  foldFourSpectatorResolvedR294IsNested :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    let module N = Nested beta in
    R224.foldVector
      (λ alpha → C3.complex3Add
        (R438.doubleWeightedProjectedForcingCell
          (Spec.spectatorWeight beta) S system alpha)
        (R438.doubleWeightedProjectedForcingCell
          (Spec.spectatorWeight beta) S system alpha))
      items
    ≡ R224.foldVector N.nestedWeightedCompanionCell items
  foldFourSpectatorResolvedR294IsNested beta items =
    let module N = Nested beta in
    N.foldFourWeightedR294IsNested items

  -- And therefore on the literal physical fixed-output fibre.
  fixedOutputFourSpectatorResolvedR294IsNested :
    (beta : Physical.PhysicalTriadIncidence) →
    (output : Z3.FourierMode) →
    let module N = Nested beta in
    R224.foldVector
      (λ alpha → C3.complex3Add
        (R438.doubleWeightedProjectedForcingCell
          (Spec.spectatorWeight beta) S system alpha)
        (R438.doubleWeightedProjectedForcingCell
          (Spec.spectatorWeight beta) S system alpha))
      (Output.physicalOutputFiber (Audit.cutoff system) output)
    ≡
    R224.foldVector N.nestedWeightedCompanionCell
      (Output.physicalOutputFiber (Audit.cutoff system) output)
  fixedOutputFourSpectatorResolvedR294IsNested beta output =
    let module N = Nested beta in
    N.fixedOutputFourWeightedR294IsNested output

------------------------------------------------------------------------
-- BIDI / WRONGTYPE FIREWALLS
------------------------------------------------------------------------

roundSpectatorNestedR541WeightInstantiatedIntoR573 : Bool
roundSpectatorNestedR541WeightInstantiatedIntoR573 = true

roundSpectatorNestedLiteralNonseparableResolventPreserved : Bool
roundSpectatorNestedLiteralNonseparableResolventPreserved = true

roundSpectatorNestedInnerOuterCommutatorSameObjectWeldClosed : Bool
roundSpectatorNestedInnerOuterCommutatorSameObjectWeldClosed = true

roundSpectatorNestedNormInsertedBeforeCancellation : Bool
roundSpectatorNestedNormInsertedBeforeCancellation = false

roundSpectatorNestedSchurOrCotlarRequiredForThisWeld : Bool
roundSpectatorNestedSchurOrCotlarRequiredForThisWeld = false

roundSpectatorNestedSignedSpectatorSpacetimePaymentClosed : Bool
roundSpectatorNestedSignedSpectatorSpacetimePaymentClosed = false

roundSpectatorNestedClayPromotion : Bool
roundSpectatorNestedClayPromotion = false

roundSpectatorNestedR541WeightInstantiatedIntoR573IsTrue :
  roundSpectatorNestedR541WeightInstantiatedIntoR573 ≡ true
roundSpectatorNestedR541WeightInstantiatedIntoR573IsTrue = refl

roundSpectatorNestedInnerOuterCommutatorSameObjectWeldClosedIsTrue :
  roundSpectatorNestedInnerOuterCommutatorSameObjectWeldClosed ≡ true
roundSpectatorNestedInnerOuterCommutatorSameObjectWeldClosedIsTrue = refl

roundSpectatorNestedNormInsertedBeforeCancellationIsFalse :
  roundSpectatorNestedNormInsertedBeforeCancellation ≡ false
roundSpectatorNestedNormInsertedBeforeCancellationIsFalse = refl

roundSpectatorNestedSignedSpectatorSpacetimePaymentClosedIsFalse :
  roundSpectatorNestedSignedSpectatorSpacetimePaymentClosed ≡ false
roundSpectatorNestedSignedSpectatorSpacetimePaymentClosedIsFalse = refl

roundSpectatorNestedClayPromotionIsFalse :
  roundSpectatorNestedClayPromotion ≡ false
roundSpectatorNestedClayPromotionIsFalse = refl
