module DASHI.Physics.Closure.NSHistoricalGlobalSignedDangerNestedSpectatorSnowballBidiExact where

------------------------------------------------------------------------
-- HISTORICAL GLOBAL-SIGNED CONSUMER x MODERN LITERAL SPECTATOR CARRIER
--
-- Snowball result:
--
-- * Round105 (2026-08-20) already proves the mathematically sharp ordering:
--     aggregate the COMPLETE signed scalar first;
--     apply positivePart only after that aggregation.
--   Its positivePartDominates theorem is generic in the scalar, so this order
--   is not tied to the old packet/danger representation.
--
-- * Round547 later constructs the complete literal fixed-output spectator-row
--   sum as a signed scalar before any norm / absolute value / Schur / Cotlar.
--
-- * NSTriadKNSpectatorResolventNestedCommutatorBidiExact instantiates the
--   generic R573 nested commutator with the literal R541 nonseparable
--   spectator resolvent weight.
--
-- Hence the historical Round105 final-order consumer accepts the modern
-- literal signed spectator aggregate directly.  The composition does NOT say
-- that CFD packet signs, Waleffe helicity signs, or old danger cells are the
-- same carrier.  It says only that the final scalar order operation was
-- already owned generically and can be reused after the literal same-object
-- signed aggregation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNGlobalSignedDangerPositivePartRound105Exact as R105
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as NestedSpec

F : C3.RealField _
F = Rational.rationalRealField

module HistoricalConsumer
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Global = R547.NormalForm physicalSystem S

  literalSignedSpectatorAggregate :
    Z3.FourierMode → List Physical.PhysicalTriadIncidence → ℚ
  literalSignedSpectatorAggregate = Global.factoredFull

  historicalFinalPositivePart :
    Z3.FourierMode → List Physical.PhysicalTriadIncidence → ℚ
  historicalFinalPositivePart output betas =
    R105.positivePart (literalSignedSpectatorAggregate output betas)

  historicalFinalOrderConsumesLiteralSignedAggregate :
    (output : Z3.FourierMode) →
    (betas : List Physical.PhysicalTriadIncidence) →
    literalSignedSpectatorAggregate output betas
    ≤ historicalFinalPositivePart output betas
  historicalFinalOrderConsumesLiteralSignedAggregate output betas =
    R105.positivePartDominates (literalSignedSpectatorAggregate output betas)

roundHistoricalGlobalSignedConsumerAlreadyOwned : Bool
roundHistoricalGlobalSignedConsumerAlreadyOwned = true

roundHistoricalPerCellPositiveTaxRequired : Bool
roundHistoricalPerCellPositiveTaxRequired = false

roundModernR547AlreadyAggregatesSignedSpectatorRows : Bool
roundModernR547AlreadyAggregatesSignedSpectatorRows = true

roundHistoricalConsumerAcceptsModernLiteralAggregateWithoutNorm : Bool
roundHistoricalConsumerAcceptsModernLiteralAggregateWithoutNorm = true

roundCFDPacketSignIdentifiedWithHelicitySign : Bool
roundCFDPacketSignIdentifiedWithHelicitySign = false

roundHistoricalCompositionAlonePaysSpacetimeEstimate : Bool
roundHistoricalCompositionAlonePaysSpacetimeEstimate = false

roundHistoricalGlobalSignedConsumerAlreadyOwnedIsTrue :
  roundHistoricalGlobalSignedConsumerAlreadyOwned ≡ true
roundHistoricalGlobalSignedConsumerAlreadyOwnedIsTrue = refl

roundHistoricalPerCellPositiveTaxRequiredIsFalse :
  roundHistoricalPerCellPositiveTaxRequired ≡ false
roundHistoricalPerCellPositiveTaxRequiredIsFalse = refl

roundHistoricalConsumerAcceptsModernLiteralAggregateWithoutNormIsTrue :
  roundHistoricalConsumerAcceptsModernLiteralAggregateWithoutNorm ≡ true
roundHistoricalConsumerAcceptsModernLiteralAggregateWithoutNormIsTrue = refl

roundHistoricalCompositionAlonePaysSpacetimeEstimateIsFalse :
  roundHistoricalCompositionAlonePaysSpacetimeEstimate ≡ false
roundHistoricalCompositionAlonePaysSpacetimeEstimateIsFalse = refl
