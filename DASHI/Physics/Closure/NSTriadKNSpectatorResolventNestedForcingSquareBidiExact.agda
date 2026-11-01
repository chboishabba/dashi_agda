module DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedForcingSquareBidiExact where

------------------------------------------------------------------------
-- SPECTATOR RESOLVENT x NESTED COMMUTATOR x FORCING-SQUARE BIDI
--
-- This composes existing owners in the cancellation-preserving order:
--
--   R541  W_beta(alpha) = 1 / (lambda_alpha + lambda_beta)
--   R542  physical weighted double-forcing fold = four R294 commutator folds
--   R573  four weighted R294 commutator cells = nested four-sign inner carrier
--   R545  spectator forcing row factors through the physical weighted fold
--   R546  complete forcing square = sum of spectator rows
--
-- Hence R567's one surviving forcing half is definitionally transported onto
-- the beta-indexed spectator-resolved nested commutator carrier BEFORE norms,
-- absolute values, Schur/Cotlar, Laplace, or spacetime majorization.
--
-- No analytic estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleForcingCommutatorFoldRound542Exact as R542
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538

F : C3.RealField _
F = Rational.rationalRealField

module Weld
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

  system = Field30.finiteSystem physicalSystem

  module Row = R545.Row physicalSystem S
  module T = R566.PhysicalTranspose physicalSystem S
  module Spec = R541.Spectator physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  module Force (beta : Physical.PhysicalTriadIncidence) =
    R542.Fold physicalSystem S (Spec.spectatorWeight beta)

  module Nested (beta : Physical.PhysicalTriadIncidence) =
    R573.WeightedNested
      (Spec.spectatorWeight beta) S L H system velocityTransverse

  spectatorWeightIsLiteralPairResolvent :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    R294.weight (Spec.spectatorWeight beta) alpha
    ≡ C3.realEmbed F (Swap.pairResolvent alpha beta)
  spectatorWeightIsLiteralPairResolvent beta alpha =
    Spec.spectatorWeightMeaning beta alpha

  ----------------------------------------------------------------------
  -- R542 and R573 normalize to the SAME four-commutator fold.
  ----------------------------------------------------------------------

  foldFourR438IsFourCommutators :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    let
      module Fo = Force beta
      D = R438.doubleWeightedProjectedForcingCell
        (Spec.spectatorWeight beta) S system
      C = R224.foldVector Fo.commutator items
    in
    R224.foldVector
      (λ alpha → C3.complex3Add (D alpha) (D alpha)) items
    ≡ C3.complex3Add (C3.complex3Add C C) (C3.complex3Add C C)
  foldFourR438IsFourCommutators beta items =
    let
      module Fo = Force beta
      D = R438.doubleWeightedProjectedForcingCell
        (Spec.spectatorWeight beta) S system
    in
    trans
      (R230.foldAdd D D items)
      (cong₂ C3.complex3Add
        (R230.foldAdd Fo.commutator Fo.commutator items)
        (R230.foldAdd Fo.commutator Fo.commutator items))

  fixedOutputPhysicalWeightedDoubleIsNested :
    (beta : Physical.PhysicalTriadIncidence) →
    (output : Z3.FourierMode) →
    let
      module Fo = Force beta
      module N = Nested beta
      items = Output.physicalOutputFiber (Audit.cutoff system) output
    in
    R224.foldVector Fo.weightedDouble items
    ≡ R224.foldVector N.nestedWeightedCompanionCell items
  fixedOutputPhysicalWeightedDoubleIsNested beta output =
    let
      module Fo = Force beta
      module N = Nested beta
      items = Output.physicalOutputFiber (Audit.cutoff system) output
    in
    trans
      (Fo.fixedOutputWeightedDoubleIsFourCommutatorFolds output)
      (trans
        (sym (foldFourR438IsFourCommutators beta items))
        (N.fixedOutputFourWeightedR294IsNested output))

  ----------------------------------------------------------------------
  -- Lift the inner alpha fold into the ACTUAL R567 forcing pair rows.
  ----------------------------------------------------------------------

  spectatorForcingRowIsR545ForcingHalf :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow T.forcingPair beta items ≡ Row.forcingHalf beta items
  spectatorForcingRowIsR545ForcingHalf beta [] = refl
  spectatorForcingRowIsR545ForcingHalf beta (alpha ∷ rest) =
    cong₂ _+_ refl (spectatorForcingRowIsR545ForcingHalf beta rest)

  nestedForcingRow :
    (output : Z3.FourierMode) →
    Physical.PhysicalTriadIncidence → ℚ
  nestedForcingRow output beta =
    let
      module N = Nested beta
      items = Output.physicalOutputFiber (Audit.cutoff system) output
    in
    R179.realHermitianCross
      (R224.foldVector N.nestedWeightedCompanionCell items)
      (Row.doubleCell beta)

  spectatorForcingRowIsNested :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    R546.spectatorRow T.forcingPair beta items
    ≡ nestedForcingRow output beta
  spectatorForcingRowIsNested output beta =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
    in
    trans
      (spectatorForcingRowIsR545ForcingHalf beta items)
      (trans
        (Row.forcingHalfFactors beta items)
        (cong
          (λ value → R179.realHermitianCross value (Row.doubleCell beta))
          (fixedOutputPhysicalWeightedDoubleIsNested beta output)))

  allNestedForcingRows :
    Z3.FourierMode →
    List Physical.PhysicalTriadIncidence → ℚ
  allNestedForcingRows output [] = 0ℚ
  allNestedForcingRows output (beta ∷ rest) =
    nestedForcingRow output beta + allNestedForcingRows output rest

  allSpectatorForcingRowsAreNested :
    (output : Z3.FourierMode) →
    (betas : List Physical.PhysicalTriadIncidence) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    R546.allSpectatorRows T.forcingPair items betas
    ≡ allNestedForcingRows output betas
  allSpectatorForcingRowsAreNested output [] = refl
  allSpectatorForcingRowsAreNested output (beta ∷ rest) =
    cong₂ _+_
      (spectatorForcingRowIsNested output beta)
      (allSpectatorForcingRowsAreNested output rest)

  forcingFullIsNestedSpectatorRows :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    R543.fullSquareSum T.forcingPair items
    ≡ allNestedForcingRows output items
  forcingFullIsNestedSpectatorRows output =
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    trans
      (R546.fullSquareIsAllSpectatorRows T.forcingPair items)
      (allSpectatorForcingRowsAreNested output items)

------------------------------------------------------------------------
-- STATUS / INTROSPECTIVE RESULT
------------------------------------------------------------------------

spectatorNestedLiteralWeightReceiptClosed : Bool
spectatorNestedLiteralWeightReceiptClosed = true

spectatorNestedPhysicalDoubleFoldWeldClosed : Bool
spectatorNestedPhysicalDoubleFoldWeldClosed = true

spectatorNestedR567ForcingSquareWeldClosed : Bool
spectatorNestedR567ForcingSquareWeldClosed = true

spectatorNestedAnyNormInsertedBeforeWeld : Bool
spectatorNestedAnyNormInsertedBeforeWeld = false

spectatorNestedAnyNewAnalyticEstimate : Bool
spectatorNestedAnyNewAnalyticEstimate = false

spectatorNestedLiveSpacetimePaymentClosed : Bool
spectatorNestedLiveSpacetimePaymentClosed = false

spectatorNestedClayPromotion : Bool
spectatorNestedClayPromotion = false

spectatorNestedR567ForcingSquareWeldClosedIsTrue :
  spectatorNestedR567ForcingSquareWeldClosed ≡ true
spectatorNestedR567ForcingSquareWeldClosedIsTrue = refl

spectatorNestedAnyNormInsertedBeforeWeldIsFalse :
  spectatorNestedAnyNormInsertedBeforeWeld ≡ false
spectatorNestedAnyNormInsertedBeforeWeldIsFalse = refl

spectatorNestedClayPromotionIsFalse :
  spectatorNestedClayPromotion ≡ false
spectatorNestedClayPromotionIsFalse = refl
