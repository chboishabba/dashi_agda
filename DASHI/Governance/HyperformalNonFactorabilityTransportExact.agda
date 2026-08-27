module DASHI.Governance.HyperformalNonFactorabilityTransportExact where

------------------------------------------------------------------------
-- HYPERFORMAL NON-FACTORABILITY TRANSPORT
--
-- Exact carrier recharting preserves a non-factorability obstruction: if a
-- consumer-relevant outcome cannot descend through a coarse projection on one
-- exact chart, changing to an isomorphic 369/dialectic chart cannot manufacture
-- the erased distinction.  This is the formal bridge between exact ternary
-- carrier equivalence and IntersectionalNonFactorability.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Trit as Trit
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Governance.HyperformalTernaryCarrierEquivalenceExact as Ternary
import DASHI.Reasoning.DialecticMotifKernel as Dialectic

record ExactChart (A B : Set) : Set₁ where
  constructor exactChart
  field
    to : A → B
    from : B → A
    toFrom : (b : B) → to (from b) ≡ b
    fromTo : (a : A) → from (to a) ≡ a

open ExactChart public

transportFlatten :
  ∀ {A B Flat} →
  ExactChart A B →
  (B → Flat) →
  A → Flat
transportFlatten chart flatten a = flatten (to chart a)

transportPhenomenon :
  ∀ {A B Outcome} →
  ExactChart A B →
  (B → Outcome) →
  A → Outcome
transportPhenomenon chart phenomenon a = phenomenon (to chart a)

transportNonFactorabilityAlongExactChart :
  ∀ {A B Flat Outcome}
    (chart : ExactChart A B)
    (flatten : B → Flat)
    (phenomenon : B → Outcome) →
  NF.NonFactorabilityWitness flatten phenomenon →
  NF.NonFactorabilityWitness
    (transportFlatten chart flatten)
    (transportPhenomenon chart phenomenon)
transportNonFactorabilityAlongExactChart chart flatten phenomenon witness =
  NF.nonFactorabilityWitness
    (from chart (NF.left witness))
    (from chart (NF.right witness))
    sameFlat
    differentOutcome
  where
    sameFlat :
      flatten (to chart (from chart (NF.left witness)))
      ≡ flatten (to chart (from chart (NF.right witness)))
    sameFlat
      rewrite toFrom chart (NF.left witness)
            | toFrom chart (NF.right witness) =
      NF.sameFlatProjection witness

    differentOutcome :
      phenomenon (to chart (from chart (NF.left witness)))
      ≡ phenomenon (to chart (from chart (NF.right witness))) → ⊥
    differentOutcome equality
      rewrite toFrom chart (NF.left witness)
            | toFrom chart (NF.right witness) =
      NF.situatedOutcomesDiffer witness equality

------------------------------------------------------------------------
-- Concrete dialectic witness: same present backbone, different past state and
-- different consumer outcome.  Present-state flattening cannot recover the
-- history-sensitive outcome.
------------------------------------------------------------------------

historyLow : Dialectic.State9
historyLow =
  Dialectic.state9
    Trit.neg Trit.zer Trit.zer
    Trit.zer Trit.zer Trit.zer
    Trit.zer Trit.zer Trit.zer

historyHigh : Dialectic.State9
historyHigh =
  Dialectic.state9
    Trit.pos Trit.zer Trit.zer
    Trit.zer Trit.zer Trit.zer
    Trit.zer Trit.zer Trit.zer

historySensitiveOutcome : Dialectic.State9 → Bool
historySensitiveOutcome state with Dialectic.self-past state
... | Trit.neg = false
... | Trit.zer = false
... | Trit.pos = true

samePresentBackbone :
  Dialectic.presentBackbone historyLow
  ≡ Dialectic.presentBackbone historyHigh
samePresentBackbone = refl

historyOutcomeDiffers :
  historySensitiveOutcome historyLow ≡ historySensitiveOutcome historyHigh → ⊥
historyOutcomeDiffers ()

dialecticPresentNonFactorability :
  NF.NonFactorabilityWitness
    Dialectic.presentBackbone
    historySensitiveOutcome
dialecticPresentNonFactorability =
  NF.nonFactorabilityWitness
    historyLow
    historyHigh
    samePresentBackbone
    historyOutcomeDiffers

dialecticPresentCannotDetermineHistoryOutcome :
  NF.FactorsThrough Dialectic.presentBackbone historySensitiveOutcome → ⊥
dialecticPresentCannotDetermineHistoryOutcome =
  NF.witnessRulesOutEveryFlatFactorisation dialecticPresentNonFactorability

------------------------------------------------------------------------
-- Transport the same obstruction into the exact Base369 chart.
------------------------------------------------------------------------

base369DialecticExactChart :
  ExactChart Cube.OneRoundInteractionState Dialectic.State9
base369DialecticExactChart =
  exactChart
    Ternary.base369ToDialectic
    Ternary.dialecticToBase369
    Ternary.dialecticBase369RoundTrip
    Ternary.base369DialecticRoundTrip

base369PresentProjection : Cube.OneRoundInteractionState → Dialectic.Backbone
base369PresentProjection =
  transportFlatten base369DialecticExactChart Dialectic.presentBackbone

base369HistorySensitiveOutcome : Cube.OneRoundInteractionState → Bool
base369HistorySensitiveOutcome =
  transportPhenomenon base369DialecticExactChart historySensitiveOutcome

base369TransportedNonFactorability :
  NF.NonFactorabilityWitness
    base369PresentProjection
    base369HistorySensitiveOutcome
base369TransportedNonFactorability =
  transportNonFactorabilityAlongExactChart
    base369DialecticExactChart
    Dialectic.presentBackbone
    historySensitiveOutcome
    dialecticPresentNonFactorability

base369PresentCannotDetermineHistoryOutcome :
  NF.FactorsThrough base369PresentProjection base369HistorySensitiveOutcome → ⊥
base369PresentCannotDetermineHistoryOutcome =
  NF.witnessRulesOutEveryFlatFactorisation base369TransportedNonFactorability

record HyperformalNonFactorabilityBoundary : Set where
  constructor hyperformalNonFactorabilityBoundary
  field
    exactRechartRepairsErasedConsumerRelation : Bool
    exactRechartTransportsNonFactorabilityWitness : Bool
    samePresentSurfaceCanHideHistorySensitiveOutcome : Bool
    shared369CarrierCreatesSemanticIdentity : Bool

canonicalHyperformalNonFactorabilityBoundary :
  HyperformalNonFactorabilityBoundary
canonicalHyperformalNonFactorabilityBoundary =
  hyperformalNonFactorabilityBoundary false true true false
