module DASHI.Cognition.PNF.RelevanceMassDynamicSafetyRegression where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
import DASHI.Cognition.PNF.TerminalisationDefectRegression as Regression
import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance
import DASHI.Core.ConsumerProjectionSufficiency as Sufficiency
import DASHI.Core.DynamicalQuotientSafety as Dynamic

------------------------------------------------------------------------
-- A tiny consumer-indexed normalized measure.
--
-- The retained current-visible region carries unit relevance mass; represented
-- residual and outside-model residual are assigned zero for this consumer.
-- This is intentionally a model-relative normalization, not world truth.
------------------------------------------------------------------------

data VisibleConsumer : Set where
  currentVisibleConsumer : VisibleConsumer

data VisibleRegion : Set where
  wholeVisibleCarrier : VisibleRegion
  retainedVisibleRegion : VisibleRegion
  representedResidualRegion : VisibleRegion
  outsideVisibleModel : VisibleRegion

one : Nat
one = suc zero

visibleRelevanceMass : VisibleConsumer → VisibleRegion → Nat
visibleRelevanceMass currentVisibleConsumer wholeVisibleCarrier = one
visibleRelevanceMass currentVisibleConsumer retainedVisibleRegion = one
visibleRelevanceMass currentVisibleConsumer representedResidualRegion = zero
visibleRelevanceMass currentVisibleConsumer outsideVisibleModel = zero

visibleMeasure :
  Relevance.ConsumerIndexedRelevanceMeasure
    VisibleConsumer VisibleRegion Nat
visibleMeasure =
  Relevance.consumerIndexedRelevanceMeasure
    Relevance.consumerRelevanceMass
    wholeVisibleCarrier
    zero
    one
    _+ᶜ_
    visibleRelevanceMass
    (λ consumer → refl)

visibleAccounting :
  Relevance.OpenWorldMassAccounting
    visibleMeasure currentVisibleConsumer
visibleAccounting =
  Relevance.openWorldMassAccounting
    retainedVisibleRegion
    representedResidualRegion
    outsideVisibleModel
    "retained current-visible task mass plus explicit residual accounting"
    refl

visibleFullRetainedMass :
  Relevance.FullRetainedModelMass visibleAccounting
visibleFullRetainedMass = Relevance.fullRetainedModelMass refl

visibleMassCertificate :
  Sufficiency.ConsumerMassCertificate
    visibleMeasure currentVisibleConsumer
visibleMassCertificate =
  Sufficiency.consumerMassCertificate
    visibleAccounting
    visibleFullRetainedMass

------------------------------------------------------------------------
-- Full retained model mass coexists with the existing residual terminalisation
-- defect.  Therefore mu_C(retained)=1 is not a dynamic-safety theorem.
------------------------------------------------------------------------

fullVisibleMassButDynamicallyUnsafe :
  Sufficiency.MassSufficientButDynamicallyUnsafe
    Regression.residualSystem
    Regression.residualProjection
    visibleMeasure
    currentVisibleConsumer
fullVisibleMassButDynamicallyUnsafe =
  Sufficiency.massSufficientButDynamicallyUnsafe
    visibleMassCertificate
    Regression.residualProjectionTerminalisationDefect

fullTaskMassStillCannotSupplyDynamicSafety :
  Dynamic.DynamicConsumerSafety
    Regression.residualSystem
    Regression.residualProjection →
  ⊥
fullTaskMassStillCannotSupplyDynamicSafety =
  Sufficiency.fullMassUnsafeCannotSupplySafeCompression
    fullVisibleMassButDynamicallyUnsafe
