module DASHI.EverythingHierarchy where

-- Hierarchical repository umbrella.
--
-- Migration rule:
--   leaf -> subfolder Everything -> domain Everything -> DASHI.Everything
--
-- This module is the bridge while DASHI.Everything is migrated away from its
-- historical flat import list.  It intentionally composes existing subject
-- rollups rather than duplicating their leaves.

import DASHI.Everything
import DASHI.Biology.Everything
import DASHI.Physics.Everything
import DASHI.Unified.Everything

-- Existing specialised Everything surfaces remain valid sub-rollups and
-- should be attached to their nearest domain-level Everything rather than
-- imported directly by the root as one-off leaves.
