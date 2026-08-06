module DASHI.Physics.Closure.NSTriadKNDaLioRiviereThreeTermCommutatorSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Francesca Da Lio; Tristan Rivière.
-- Title: "Three-Term Commutator Estimates and the Regularity of
-- 1/2-Harmonic Maps into Spheres".
-- Analysis & PDE 4 (2011), no. 1, 149--190.
-- DOI: 10.2140/apde.2011.4.149.
-- arXiv:0901.2533.
--
-- PURPOSE
-- Record exactly what the supplied paper contributes to the Luo terminal-
-- interaction program.  The paper proves Hardy/BMO regularity gain for the
-- three-term fractional commutators T and S, using a Littlewood--Paley split
-- into high--low, low--high and high--high paraproducts.  This is genuine
-- structural support for compensated three-term cancellation and annular
-- localization, but it is not literally the periodic transport block
--
--   [Delta_q , a . grad] g
--
-- nor the DASHI (L6,L3) centered-kernel estimate.  The separation below
-- prevents the source theorem from being imported under the wrong operator
-- shape.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data OperatorShape : Set where
  fractionalThreeTermT : OperatorShape
  fractionalThreeTermS : OperatorShape
  dyadicTransportBlock : OperatorShape
  endpointSchattenCommutator : OperatorShape

sourcePrimaryShape : OperatorShape
sourcePrimaryShape = fractionalThreeTermT

sourcePrimaryIsNotDyadicTransport :
  sourcePrimaryShape ≢ dyadicTransportBlock
sourcePrimaryIsNotDyadicTransport ()

sourcePrimaryIsNotEndpointSchatten :
  sourcePrimaryShape ≢ endpointSchattenCommutator
sourcePrimaryIsNotEndpointSchatten ()

data SourceContribution : Set where
  threeTermCancellation : SourceContribution
  littlewoodPaleyParaproductSplit : SourceContribution
  hardyBmoRegularityGain : SourceContribution
  annularCrushingLocalization : SourceContribution
  completeSixThreeTransportEstimate : SourceContribution

sourceSuppliesCancellation : SourceContribution
sourceSuppliesCancellation = threeTermCancellation

sourceSuppliesParaproductSplit : SourceContribution
sourceSuppliesParaproductSplit = littlewoodPaleyParaproductSplit

sourceSuppliesHardyBmoGain : SourceContribution
sourceSuppliesHardyBmoGain = hardyBmoRegularityGain

sourceSuppliesAnnularLocalization : SourceContribution
sourceSuppliesAnnularLocalization = annularCrushingLocalization

sourceDoesNotDirectlySupplySixThree :
  sourceSuppliesCancellation ≢ completeSixThreeTransportEstimate
sourceDoesNotDirectlySupplySixThree ()

-- Exact algebra behind a three-term compensation.  Individually the three
-- summands may be large; after common terms are expanded, only the mixed
-- increments remain.
threeTermProductCancellation :
  (qCenter qShift uCenter uShift : ℚ) →
  qShift * uShift
    - qCenter * uShift
    - qShift * uCenter
    + qCenter * uCenter
  ≡ (qShift - qCenter) * (uShift - uCenter)
threeTermProductCancellation qCenter qShift uCenter uShift =
  solve (qCenter ∷ qShift ∷ uCenter ∷ uShift ∷ [])

-- The source's paraproduct architecture has three genuinely distinct lanes.
data ParaproductLane : Set where
  highLow lowHigh highHigh : ParaproductLane

allThreeLanesDistinct₁ : highLow ≢ lowHigh
allThreeLanesDistinct₁ ()

allThreeLanesDistinct₂ : lowHigh ≢ highHigh
allThreeLanesDistinct₂ ()

allThreeLanesDistinct₃ : highLow ≢ highHigh
allThreeLanesDistinct₃ ()
