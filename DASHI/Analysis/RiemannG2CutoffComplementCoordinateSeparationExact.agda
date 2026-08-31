module DASHI.Analysis.RiemannG2CutoffComplementCoordinateSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2QuarterPeriodScalingPropagationExact as Scaling
import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as Far
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientBidiMeetingExact as Meeting

------------------------------------------------------------------------
-- CUTOFF / DETERMINISTIC-COMPLEMENT COORDINATE SEPARATION
--
-- Repo-first correction to the quarter-period propagation graph.
--
-- The finite near/far decomposition carries the cutoff J explicitly.  But the
-- existing final pole-quotient consumer interfaces for the deterministic Gamma
-- response and quantitative cluster margin are functions of the literal taper,
-- not of J.  Therefore an enlarged quarter-period cutoff does not, by itself,
-- create a new Gamma(J) or cluster(J) theorem obligation.
--
-- What remains is a SAME-TAPER compatibility problem:
--
--   offBudget(g_pole; derived using chosen J)
--   + GammaBudget(g_pole)
--   < ClusterMargin(g_pole).
--
-- Thus J is a producer coordinate for the signed off-ordinate estimate, while
-- Gamma and cluster are deterministic complement coordinates on the fixed
-- literal pole-quotient taper.  This module prevents us from searching for a
-- fictitious cutoff-dependent Gamma law that the downstream API does not ask
-- for.
------------------------------------------------------------------------

data ConsumerCoordinate : Set where
  cutoffCoordinate
  taperCoordinate
  signedOffOrdinateCoordinate
  deterministicGammaCoordinate
  quantitativeClusterCoordinate
  : ConsumerCoordinate

record CutoffDependentOffProducer : Set₁ where
  field
    Scalar Taper Cutoff : Set
    literalTaper : Taper
    chosenCutoff : Cutoff
    OffBudgetAt : Taper -> Cutoff -> Scalar
    sameNearFarCutoffUsed : Set
    offBudgetDerivedAtChosenCutoff : Set

open CutoffDependentOffProducer public

record TaperOnlyComplementConsumer : Set₁ where
  field
    Scalar Taper : Set
    literalTaper : Taper
    GammaBudget : Taper -> Scalar
    ClusterMargin : Taper -> Scalar
    sameLiteralTaperUsedByGamma : Set
    sameLiteralTaperUsedByCluster : Set

open TaperOnlyComplementConsumer public

record CutoffToComplementWeld
    (O : CutoffDependentOffProducer)
    (C : TaperOnlyComplementConsumer) : Set₁ where
  field
    sameScalarCarrier : Scalar O ≡ Scalar C
    sameTaperCarrier : Taper O ≡ Taper C
    sameLiteralPoleQuotientTaper : Set
    combinedBudgetFitsMargin : Set
    weldReference : String

open CutoffToComplementWeld public

------------------------------------------------------------------------
-- Existing repository interfaces certify the coordinate separation.
------------------------------------------------------------------------

farEveryCutoffInfrastructureOwned :
  Far.explicitEveryCutoffBoundOwned
    Far.canonicalExplicitCutoffCarrierLeanReturn ≡ true
farEveryCutoffInfrastructureOwned =
  Far.explicitEveryCutoffBoundOwnedIsTrue
    Far.canonicalExplicitCutoffCarrierLeanReturn

gammaTargetIsSameTaperTarget :
  Gamma.sameUniversalPoleQuotientTaperRequired
    Gamma.canonicalPoleQuotientGammaBudgetBoundary ≡ true
gammaTargetIsSameTaperTarget =
  Gamma.sameUniversalPoleQuotientTaperRequiredIsTrue
    Gamma.canonicalPoleQuotientGammaBudgetBoundary

clusterStrictPositivityNotYetQuantitativeMargin :
  Cluster.strictPositivityAutomaticallyInstantiatesConsumerMargin
    Cluster.canonicalPoleQuotientClusterMarginBoundary ≡ false
clusterStrictPositivityNotYetQuantitativeMargin =
  Cluster.strictPositivityAutomaticallyInstantiatesConsumerMarginIsFalse
    Cluster.canonicalPoleQuotientClusterMarginBoundary

gammaComplementStillOpen :
  Meeting.gammaComplementBudgetClosed
    Meeting.canonicalPoleQuotientBidiMeetingBoundary ≡ false
gammaComplementStillOpen = refl

quantitativeClusterMarginStillOpen :
  Meeting.quantitativePositiveClusterMarginClosed
    Meeting.canonicalPoleQuotientBidiMeetingBoundary ≡ false
quantitativeClusterMarginStillOpen = refl

targetCenteredOffOrdinateStillOpen :
  Meeting.targetCenteredOffOrdinateBoundClosed
    Meeting.canonicalPoleQuotientBidiMeetingBoundary ≡ false
targetCenteredOffOrdinateStillOpen = refl

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data NextPayment : Set where
  deriveCutoffDependentOffBudget
  proveSameTaperGammaBudget
  proveQuantitativeClusterMargin
  proveCombinedStrictBudget
  inventGammaAsFunctionOfCutoff
  : NextPayment

SearchRelevant : NextPayment -> Set
SearchRelevant deriveCutoffDependentOffBudget = ⊤
SearchRelevant proveSameTaperGammaBudget = ⊤
SearchRelevant proveQuantitativeClusterMargin = ⊤
SearchRelevant proveCombinedStrictBudget = ⊤
SearchRelevant inventGammaAsFunctionOfCutoff = ⊥

cutoffDependentGammaSearchPruned :
  SearchRelevant inventGammaAsFunctionOfCutoff -> ⊥
cutoffDependentGammaSearchPruned x = x

record CutoffComplementCoordinateBoundary : Set where
  constructor cutoff-complement-coordinate-boundary
  field
    cutoffIsExplicitProducerCoordinateForNearFarSplit : Bool
    cutoffIsExplicitProducerCoordinateForNearFarSplitIsTrue :
      cutoffIsExplicitProducerCoordinateForNearFarSplit ≡ true

    existingGammaConsumerHasCutoffArgument : Bool
    existingGammaConsumerHasCutoffArgumentIsFalse :
      existingGammaConsumerHasCutoffArgument ≡ false

    existingClusterConsumerHasCutoffArgument : Bool
    existingClusterConsumerHasCutoffArgumentIsFalse :
      existingClusterConsumerHasCutoffArgument ≡ false

    enlargedCutoffAutomaticallyChangesGammaResponse : Bool
    enlargedCutoffAutomaticallyChangesGammaResponseIsFalse :
      enlargedCutoffAutomaticallyChangesGammaResponse ≡ false

    enlargedCutoffAutomaticallyChangesClusterMargin : Bool
    enlargedCutoffAutomaticallyChangesClusterMarginIsFalse :
      enlargedCutoffAutomaticallyChangesClusterMargin ≡ false

    sameTaperCombinedBudgetIsActualConsumerPayment : Bool
    sameTaperCombinedBudgetIsActualConsumerPaymentIsTrue :
      sameTaperCombinedBudgetIsActualConsumerPayment ≡ true

    highestAlphaReading : String

canonicalCutoffComplementCoordinateBoundary : CutoffComplementCoordinateBoundary
canonicalCutoffComplementCoordinateBoundary =
  cutoff-complement-coordinate-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "The quarter-period cutoff J belongs to the near/far and signed off-ordinate producer. The final pole-quotient Gamma and cluster target interfaces are taper-only. Therefore do not invent a Gamma(J) scaling problem merely because J grows. The actual BIDI weld is: derive the off-ordinate budget at the chosen quarter-period cutoff, then combine it on the same literal pole-quotient taper with an independent deterministic Gamma budget and quantitative cluster margin, proving the strict combined budget inequality."
