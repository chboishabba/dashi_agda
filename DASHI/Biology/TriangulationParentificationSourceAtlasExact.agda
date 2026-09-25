module DASHI.Biology.TriangulationParentificationSourceAtlasExact where

------------------------------------------------------------------------
-- COMPATIBILITY OWNER
--
-- Reuses the bounded central source atlas rather than duplicating source rows.
-- Citation remains non-promoting under AttributedSourceCore.
------------------------------------------------------------------------

import DASHI.Core.RelationalTrialecticSourceAtlasExact as Atlas

triangulationParentificationSourceAtlas =
  Atlas.relationalTrialecticSourceAtlas
