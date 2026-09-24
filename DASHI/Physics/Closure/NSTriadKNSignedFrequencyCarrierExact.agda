module DASHI.Physics.Closure.NSTriadKNSignedFrequencyCarrierExact where

------------------------------------------------------------------------
-- DOMAIN-INDEPENDENT SIGNED FREQUENCY CARRIER
--
-- The current periodic NS frontier has isolated the exact pointwise identity
--
--   weighted resolvent flux
--     = common-output-resolvent Gram flux
--         - centered-frequency resolvent correction.
--
-- Nothing in that algebraic statement requires Z^3, a finite output fibre, or
-- counting measure.  This owner factors that theorem shape away from its
-- periodic realization so a future R^3/Lebesgue realization can target the
-- SAME signed object rather than restating the analytic mechanism.
--
-- Important trust boundary:
--   * this file owns only the exact signed decomposition interface;
--   * aggregation requires an explicit linearity/extensionality receipt;
--   * no positivity, absolute-value estimate, cutoff-uniform estimate,
--     Lebesgue integration, or Clay promotion is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans)

record SignedFrequencyCarrier : Set₁ where
  constructor signed-frequency-carrier
  field
    Interaction : Set
    Scalar : Set

    _minus_ : Scalar → Scalar → Scalar

    weightedFlux : Interaction → Scalar
    commonResolventFlux : Interaction → Scalar
    centeredResolventCorrection : Interaction → Scalar

    pointwiseCenteredResolventSplit :
      (x : Interaction) →
      weightedFlux x
      ≡ _minus_
          (commonResolventFlux x)
          (centeredResolventCorrection x)

open SignedFrequencyCarrier public

------------------------------------------------------------------------
-- Aggregation is deliberately a second layer.
--
-- Counting measure, Lebesgue measure, a finite list fold, or another spectral
-- measure may instantiate this record, but only after providing the two laws
-- actually used below:
--
--   1. pointwise equality is respected by aggregation;
--   2. aggregation commutes with the signed difference.
------------------------------------------------------------------------

record SignedFrequencyAggregation
    (C : SignedFrequencyCarrier) : Set₁ where
  constructor signed-frequency-aggregation
  field
    aggregate : (Interaction C → Scalar C) → Scalar C

    aggregateRespectsPointwise :
      {f g : Interaction C → Scalar C} →
      ((x : Interaction C) → f x ≡ g x) →
      aggregate f ≡ aggregate g

    aggregateDifference :
      (f g : Interaction C → Scalar C) →
      aggregate (λ x → _minus_ C (f x) (g x))
      ≡ _minus_ C (aggregate f) (aggregate g)

open SignedFrequencyAggregation public

aggregateCenteredResolventSplit :
  (C : SignedFrequencyCarrier) →
  (A : SignedFrequencyAggregation C) →
  aggregate A (weightedFlux C)
  ≡
  _minus_ C
    (aggregate A (commonResolventFlux C))
    (aggregate A (centeredResolventCorrection C))
aggregateCenteredResolventSplit C A =
  trans
    (aggregateRespectsPointwise A
      (pointwiseCenteredResolventSplit C))
    (aggregateDifference A
      (commonResolventFlux C)
      (centeredResolventCorrection C))

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data PointwiseSplitAutomaticallyPaysAggregateEstimate : Set where
data AggregateSplitAutomaticallySuppliesLebesgueTheory : Set where
data PeriodicRealizationAutomaticallyImpliesEuclideanRealization : Set where
data SignedCarrierAutomaticallyPromotesClay : Set where

pointwiseSplitDoesNotAutoPayAggregateEstimate :
  PointwiseSplitAutomaticallyPaysAggregateEstimate → ⊥
pointwiseSplitDoesNotAutoPayAggregateEstimate ()

aggregateSplitDoesNotAutoSupplyLebesgueTheory :
  AggregateSplitAutomaticallySuppliesLebesgueTheory → ⊥
aggregateSplitDoesNotAutoSupplyLebesgueTheory ()

periodicDoesNotAutoImplyEuclidean :
  PeriodicRealizationAutomaticallyImpliesEuclideanRealization → ⊥
periodicDoesNotAutoImplyEuclidean ()

signedCarrierDoesNotAutoPromoteClay :
  SignedCarrierAutomaticallyPromotesClay → ⊥
signedCarrierDoesNotAutoPromoteClay ()

------------------------------------------------------------------------
-- Machine-readable boundary.
------------------------------------------------------------------------

domainIndependentSignedCarrierOwned : Bool
domainIndependentSignedCarrierOwned = true

aggregationCompilerOwned : Bool
aggregationCompilerOwned = true

concretePeriodicRealizationOwnedHere : Bool
concretePeriodicRealizationOwnedHere = false

concreteLebesgueRealizationOwnedHere : Bool
concreteLebesgueRealizationOwnedHere = false

centeredResolventAnalyticPaymentOwnedHere : Bool
centeredResolventAnalyticPaymentOwnedHere = false

clayPromotion : Bool
clayPromotion = false

domainIndependentSignedCarrierOwnedIsTrue :
  domainIndependentSignedCarrierOwned ≡ true
domainIndependentSignedCarrierOwnedIsTrue = refl

aggregationCompilerOwnedIsTrue :
  aggregationCompilerOwned ≡ true
aggregationCompilerOwnedIsTrue = refl

concretePeriodicRealizationOwnedHereIsFalse :
  concretePeriodicRealizationOwnedHere ≡ false
concretePeriodicRealizationOwnedHereIsFalse = refl

concreteLebesgueRealizationOwnedHereIsFalse :
  concreteLebesgueRealizationOwnedHere ≡ false
concreteLebesgueRealizationOwnedHereIsFalse = refl

centeredResolventAnalyticPaymentOwnedHereIsFalse :
  centeredResolventAnalyticPaymentOwnedHere ≡ false
centeredResolventAnalyticPaymentOwnedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
