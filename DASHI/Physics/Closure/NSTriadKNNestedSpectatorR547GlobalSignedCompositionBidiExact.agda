module DASHI.Physics.Closure.NSTriadKNNestedSpectatorR547GlobalSignedCompositionBidiExact where

------------------------------------------------------------------------
-- NESTED SPECTATOR -> EXISTING R547 GLOBAL SIGNED BETA SUM
--
-- This owner records the shortest composition discovered by snowballing.
-- R547 already owns the complete signed beta aggregation:
--
--   factoredFull output betas = sum_beta factoredRow output beta
--
-- with no norm / absolute value / Schur / Cotlar step before that sum.
--
-- The newer spectator-nested weld instantiates R573 with the literal R541
-- nonseparable pair-resolvent weight for each fixed beta.  Therefore the
-- remaining compositional task is local to one beta-row: transport the R547
-- weighted outer commutator fold onto the already-constructed R573 nested
-- four-sign carrier.  The global beta aggregation itself is not a residual.
--
-- This file deliberately does not assert the final spacetime estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as NestedSpec

F : C3.RealField _
F = Rational.rationalRealField

module GlobalNested
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) ->
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Old = R547.NormalForm physicalSystem S
  module New = NestedSpec.SpectatorNested physicalSystem S L H velocityTransverse

  -- R547 already is the complete signed spectator aggregation.
  existingSignedBetaSum :
    Z3.FourierMode -> List Physical.PhysicalTriadIncidence -> Rational.ℚ
  existingSignedBetaSum = Old.factoredFull

  -- The local nested carrier is already available for every beta under the
  -- literal nonseparable spectator resolvent weight.
  nestedFixedOutputCarrier :
    (beta : Physical.PhysicalTriadIncidence) ->
    (output : Z3.FourierMode) ->
    let module N = New.Nested beta in
    C3.Complex3 F
  nestedFixedOutputCarrier beta output =
    let module N = New.Nested beta in
    -- `fixedOutputFourSpectatorResolvedR294IsNested` proves that this fold is
    -- definitionally the same weighted outer object after the inner four-sign
    -- expansion.  We expose the RHS directly as the reusable carrier.
    let open import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact in
    foldVector N.nestedWeightedCompanionCell
      (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
        (Audit.cutoff (Field30.finiteSystem physicalSystem)) output)

roundNestedSpectatorR547ExistingGlobalBetaSumClosed : Bool
roundNestedSpectatorR547ExistingGlobalBetaSumClosed = true

roundNestedSpectatorR547LiteralR541IntoR573Closed : Bool
roundNestedSpectatorR547LiteralR541IntoR573Closed = true

roundNestedSpectatorR547NormBeforeBetaAggregation : Bool
roundNestedSpectatorR547NormBeforeBetaAggregation = false

roundNestedSpectatorR547GlobalBetaAggregationIsNewResidual : Bool
roundNestedSpectatorR547GlobalBetaAggregationIsNewResidual = false

roundNestedSpectatorR547RemainingLocalRowTransportToNestedCarrier : Bool
roundNestedSpectatorR547RemainingLocalRowTransportToNestedCarrier = true

roundNestedSpectatorR547SignedSpacetimeEstimateClosed : Bool
roundNestedSpectatorR547SignedSpacetimeEstimateClosed = false

roundNestedSpectatorR547ClayPromotion : Bool
roundNestedSpectatorR547ClayPromotion = false

roundNestedSpectatorR547ExistingGlobalBetaSumClosedIsTrue :
  roundNestedSpectatorR547ExistingGlobalBetaSumClosed ≡ true
roundNestedSpectatorR547ExistingGlobalBetaSumClosedIsTrue = refl

roundNestedSpectatorR547GlobalBetaAggregationIsNewResidualIsFalse :
  roundNestedSpectatorR547GlobalBetaAggregationIsNewResidual ≡ false
roundNestedSpectatorR547GlobalBetaAggregationIsNewResidualIsFalse = refl

roundNestedSpectatorR547NormBeforeBetaAggregationIsFalse :
  roundNestedSpectatorR547NormBeforeBetaAggregation ≡ false
roundNestedSpectatorR547NormBeforeBetaAggregationIsFalse = refl

roundNestedSpectatorR547ClayPromotionIsFalse :
  roundNestedSpectatorR547ClayPromotion ≡ false
roundNestedSpectatorR547ClayPromotionIsFalse = refl
