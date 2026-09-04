module DASHI.Analysis.NonArchimedeanMonsterWilsonDyadicReconciliationExact where

------------------------------------------------------------------------
-- SOURCE DYADIC BULK / WILSON 3B-NORMALIZER RECONCILIATION
--
-- Wilson's published 3B-local degree pattern yields the arithmetic observer
--
--   65610 = 65520 + 90
--   143   = 90 + 53.
--
-- The source-17 / Monster dyadic chart yields
--
--   65610 = 65536 + 74
--   127   = 74 + 53.
--
-- Therefore the two bulk conventions differ by exactly 16:
--
--   65520 + 16 = 65536
--   16 + 74    = 90
--   16 + 127   = 143.
--
-- These are exact integer reconciliation identities.  They do NOT assert a
-- Suz-stable 16-dimensional submodule or a representation decomposition of the
-- irreducible degree-143 constituent.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Analysis.NonArchimedeanMonster3BDyadicCorrespondenceBidiExact as Corr
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as M3B

wilsonLinearBulk : Nat
wilsonLinearBulk = 65520

wilsonMultiplicityResidual : Nat
wilsonMultiplicityResidual = 90

wilsonFixedIrreducible : Nat
wilsonFixedIrreducible = 143

bulkShift : Nat
bulkShift = 16

sourceDyadicCorrection : Nat
sourceDyadicCorrection = 74

centralCharacterResidual : Nat
centralCharacterResidual = 53

sourceInvariantCorrection : Nat
sourceInvariantCorrection = 127

wilsonBulkPlusShiftIsSourceBulk :
  wilsonLinearBulk + bulkShift ≡ Corr.sourceTwistedCardinalityAt17
wilsonBulkPlusShiftIsSourceBulk = refl

bulkShiftPlusSourceCorrectionIsWilson90 :
  bulkShift + sourceDyadicCorrection ≡ wilsonMultiplicityResidual
bulkShiftPlusSourceCorrectionIsWilson90 = refl

sourceCorrectionPlusCharacterIs127 :
  sourceDyadicCorrection + centralCharacterResidual ≡ sourceInvariantCorrection
sourceCorrectionPlusCharacterIs127 = refl

wilson90PlusCharacterIs143 :
  wilsonMultiplicityResidual + centralCharacterResidual ≡ wilsonFixedIrreducible
wilson90PlusCharacterIs143 = refl

bulkShiftPlus127Is143 :
  bulkShift + sourceInvariantCorrection ≡ wilsonFixedIrreducible
bulkShiftPlus127Is143 = refl

wilsonBulkPlus90IsBalanced65610 :
  wilsonLinearBulk + wilsonMultiplicityResidual ≡ 65610
wilsonBulkPlus90IsBalanced65610 = refl

sourceBulkPlus74IsBalanced65610 :
  Corr.sourceTwistedCardinalityAt17 + sourceDyadicCorrection ≡ 65610
sourceBulkPlus74IsBalanced65610 = refl

------------------------------------------------------------------------
-- Commuting arithmetic square of bulk conventions.
--
--       65520 -- +16 --> 65536
--         |               |
--        +90             +74
--         |               |
--         v               v
--       65610 ========= 65610
--
-- The square reconciles observers; it is not a square of representation maps.
------------------------------------------------------------------------

record WilsonDyadicReconciliationBoundary : Set where
  constructor wilson-dyadic-reconciliation-boundary
  field
    arithmeticSquareOwned : Bool
    bulkShiftSixteenOwned : Bool
    bulkShiftSixteenIsInvariantSubmodule : Bool
    wilsonNinetyEqualsSourceSixteenPlusSeventyFourAsRepresentations : Bool
    suz143SplitsAsSixteenPlus127 : Bool
    sourceDyadicActionIdentifiedWithWilsonMonomialAction : Bool
    reconciliationCanGuideSameObjectSearch : Bool

canonicalWilsonDyadicReconciliationBoundary :
  WilsonDyadicReconciliationBoundary
canonicalWilsonDyadicReconciliationBoundary =
  wilson-dyadic-reconciliation-boundary
    true true false false false false true

------------------------------------------------------------------------
-- BIDI targets suggested by the square.
------------------------------------------------------------------------

data ReconciliationTarget : Set where
  compare65520And65536Carriers : ReconciliationTarget
  identifyMeaningOfBulkShift16 : ReconciliationTarget
  compareWilson90WithShift16PlusResidual74 : ReconciliationTarget
  compareActionsOnBalanced65610 : ReconciliationTarget
  constructRestrictionIntertwiner : ReconciliationTarget

highestAlphaReconciliationPath : List ReconciliationTarget
highestAlphaReconciliationPath =
  compare65520And65536Carriers ∷
  identifyMeaningOfBulkShift16 ∷
  compareActionsOnBalanced65610 ∷
  constructRestrictionIntertwiner ∷
  []
