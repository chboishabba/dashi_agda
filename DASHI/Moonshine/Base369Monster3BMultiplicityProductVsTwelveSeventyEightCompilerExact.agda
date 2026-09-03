module DASHI.Moonshine.Base369Monster3BMultiplicityProductVsTwelveSeventyEightCompilerExact where

------------------------------------------------------------------------
-- SAME FIN90, TWO STRUCTURAL CHARTS
--
-- Generated product chart:
--   Fin90 <-> Completed10 x T^2.
--
-- Existing scientific block target:
--   Fin90 <-> S12 + S78
-- with the SAME actual multiplicity inertia action.
--
-- Once the 12+78 attachment is supplied, there is no further recognition
-- theorem needed to compare these pictures: compose both charts through the
-- literal Fin90 carrier.  This owner makes that cross-chart explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual
import DASHI.Moonshine.Monster3BMultiplicityTwelveSeventyEightRecognitionExact as Split
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Product
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed

------------------------------------------------------------------------
-- 1. Cross-chart equivalence.
------------------------------------------------------------------------

completedToTwelveSeventyEight :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityTwelveSeventyEightAttachment source) →
  Completed.CompletedTenTritSquare →
  Actual.TwelveCarrier attachment ⊎ Actual.SeventyEightCarrier attachment
completedToTwelveSeventyEight attachment state =
  Split.toSum (Actual.blockRecognition attachment)
    (Product.completedToFin90 state)

twelveSeventyEightToCompleted :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityTwelveSeventyEightAttachment source) →
  Actual.TwelveCarrier attachment ⊎ Actual.SeventyEightCarrier attachment →
  Completed.CompletedTenTritSquare
twelveSeventyEightToCompleted attachment state =
  Product.fin90ToCompleted
    (Split.fromSum (Actual.blockRecognition attachment) state)

completedAfterBlock :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityTwelveSeventyEightAttachment source) →
  (state : Actual.TwelveCarrier attachment ⊎ Actual.SeventyEightCarrier attachment) →
  completedToTwelveSeventyEight attachment
    (twelveSeventyEightToCompleted attachment state)
  ≡ state
completedAfterBlock attachment state =
  trans
    (cong (Split.toSum (Actual.blockRecognition attachment))
      (Product.completedAfterFin90
        (Split.fromSum (Actual.blockRecognition attachment) state)))
    (Split.toAfterFrom (Actual.blockRecognition attachment) state)

blockAfterCompleted :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityTwelveSeventyEightAttachment source) →
  (state : Completed.CompletedTenTritSquare) →
  twelveSeventyEightToCompleted attachment
    (completedToTwelveSeventyEight attachment state)
  ≡ state
blockAfterCompleted attachment state =
  trans
    (cong Product.fin90ToCompleted
      (Split.fromAfterTo (Actual.blockRecognition attachment)
        (Product.completedToFin90 state)))
    (Product.fin90AfterCompleted state)

------------------------------------------------------------------------
-- 2. The 12 and 78 blocks therefore become typed regions of the product chart.
------------------------------------------------------------------------

data ProductBlockTag : Set where
  twelveRegion seventyEightRegion : ProductBlockTag

productBlockTag :
  ∀ {source : Action.ActualMonster3BActionRecognition} →
  (attachment : Actual.ActualMultiplicityTwelveSeventyEightAttachment source) →
  Completed.CompletedTenTritSquare → ProductBlockTag
productBlockTag attachment state with completedToTwelveSeventyEight attachment state
... | inj₁ _ = twelveRegion
... | inj₂ _ = seventyEightRegion

------------------------------------------------------------------------
-- 3. Boundary.
------------------------------------------------------------------------

record ProductVsBlockBoundary : Set where
  constructor productVsBlockBoundary
  field
    productChartGenerated : Bool
    twelvePlusSeventyEightStillRequiresActualBlockAttachment : Bool
    crossChartGeneratedAfterBlockAttachment : Bool
    twelveAndSeventyEightBecomeRegionsOfTenTimesTritSquare : Bool
    blockCardinalityAloneDeterminesGeometricRegionShape : Bool
    regionIncidenceComputationIsNextUsefulAnalysis : Bool

canonicalProductVsBlockBoundary : ProductVsBlockBoundary
canonicalProductVsBlockBoundary =
  productVsBlockBoundary
    true true true true false true
