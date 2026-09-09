module DASHI.GameTheory.GameComputationSourceAttributionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as R4
import DASHI.Biology.ConsciousAccessRound5SourceAtlas as SourceAtlas

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION FOR GAME / COMPUTATION CROSS-POLLINATION
--
-- Reuse the canonical source atlas.  These records motivate the computational
-- formalisms; they do not supply strategic preference, equilibrium, empirical
-- authority or a physical interpretation.
------------------------------------------------------------------------

fractranSource : R4.SourceRecord
fractranSource = SourceAtlas.conwayFRACTRANSource

wolframMultiwaySource : R4.SourceRecord
wolframMultiwaySource = SourceAtlas.wolframMultiwaySource

record GameComputationSourceBoundary : Set where
  constructor game-computation-source-boundary
  field
    conwaySourceReused : Bool
    wolframSourceReused : Bool
    sourceMotivationCreatesEquilibriumTheorem : Bool
    sourceMotivationCreatesEmpiricalGameModel : Bool

canonicalGameComputationSourceBoundary : GameComputationSourceBoundary
canonicalGameComputationSourceBoundary =
  game-computation-source-boundary true true false false
