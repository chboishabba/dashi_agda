module DASHI.Physics.Chemistry.Nobel2026QuantitativeSourceWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.Nobel2026QuantitativeProducerBoundaryExact as Abstract
import DASHI.Physics.Chemistry.Nobel2026SourcePaidAmplificationExact as Amplification
import DASHI.Physics.Chemistry.Nobel2026SoaiMechanisticKineticWeldExact as Kinetics
import DASHI.Physics.Chemistry.Nobel2026ChiralitySourceAtlasExact as Atlas

------------------------------------------------------------------------
-- QUANTITATIVE SOURCE WELD
--
-- The earlier abstract producer boundary is now consumed by an inhabited
-- source-facing surface.  It intentionally keeps distinct experiments distinct:
-- Sato et al. 2003 pay the extreme three-cycle ee amplification receipt;
-- Möhler et al. 2025 pay the detailed same-reaction-family kinetic/mechanistic
-- profile.  Cross-study synthesis is not mislabeled as one historical run.
------------------------------------------------------------------------

record SourcePaidSoaiQuantitativeSurface : Set where
  constructor sourcePaidSoaiQuantitativeSurface
  field
    amplificationSource : Source.AttributedSource
    amplification : Amplification.AmplificationObservation
    kineticSource : Source.AttributedSource
    networkScale : Kinetics.KineticNetworkScale
    mechanism : Kinetics.MechanisticReceipt

    sameReactionFamily : Bool
    sameReactionFamilyIsTrue : sameReactionFamily ≡ true

    sameHistoricalExperiment : Bool
    sameHistoricalExperimentIsFalse : sameHistoricalExperiment ≡ false

    sourceExposedEEEndpointPaid : Bool
    sourceExposedEEEndpointPaidIsTrue : sourceExposedEEEndpointPaid ≡ true

    sourceExposedKineticArchitecturePaid : Bool
    sourceExposedKineticArchitecturePaidIsTrue :
      sourceExposedKineticArchitecturePaid ≡ true

    sourceExposedMechanisticRolesPaid : Bool
    sourceExposedMechanisticRolesPaidIsTrue :
      sourceExposedMechanisticRolesPaid ≡ true

sourcePaidSoaiSurface : SourcePaidSoaiQuantitativeSurface
sourcePaidSoaiSurface =
  sourcePaidSoaiQuantitativeSurface
    Atlas.sato2003
    Amplification.sato2003Amplification
    Atlas.mohler2025
    Kinetics.mohler2025NetworkScale
    Kinetics.mohler2025MechanisticReceipt
    true refl
    false refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Projection to the earlier abstract frontier vocabulary.
--
-- The source weld pays the concrete observations available in the article main
-- texts; it does not fabricate a total continuous response function from sparse
-- source points or copy unseen supplementary ODE right-hand sides.
------------------------------------------------------------------------

record AbstractProducerPayment : Set where
  constructor abstractProducerPayment
  field
    abstractEEInterfaceAvailable : Bool
    sourceSpecificEEObservationInhabited : Bool
    sourceSpecificKineticNetworkInhabited : Bool
    sourceSpecificMechanisticReceiptInhabited : Bool
    measurementMethodIdentityAvailable : Bool
    mirrorRateIdentityAvailable : Bool
    totalContinuousEEFunctionRecoveredFromSparsePoints : Bool
    supplementaryODERightHandSidesInvented : Bool

canonicalAbstractProducerPayment : AbstractProducerPayment
canonicalAbstractProducerPayment =
  abstractProducerPayment
    true true true true true true false false

abstractInterfaceStillLive : Abstract.Nobel2026QuantitativeProducerBoundary
abstractInterfaceStillLive = Abstract.canonicalNobel2026QuantitativeProducerBoundary

-- The formerly vague source/kinetic seam is therefore replaced by an inhabited
-- quantitative observation surface plus an explicit total-model promotion gate.
record QuantitativeSourceWeldBoundary : Set where
  constructor quantitativeSourceWeldBoundary
  field
    extremeEEAmplificationSourceWeldPaid : Bool
    mechanisticKineticSourceWeldPaid : Bool
    activationBarrierWeldPaid : Bool
    rateRoleAndUnitWeldPaid : Bool
    mirrorCycleRateWeldPaid : Bool
    distinctHistoricalExperimentsCollapsed : Bool
    sparseDataPromotedToUniqueContinuousLaw : Bool

canonicalQuantitativeSourceWeldBoundary : QuantitativeSourceWeldBoundary
canonicalQuantitativeSourceWeldBoundary =
  quantitativeSourceWeldBoundary true true true true true false false
