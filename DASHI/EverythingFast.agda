module DASHI.EverythingFast where

-- Stable fast-check umbrella.
-- DASHI.Everything is intentionally lightweight and excludes the heavy
-- Yang--Mills / Navier--Stokes closure lanes.  Additional domain fast surfaces
-- may attach here only when their transitive closure is known to avoid those
-- heavy lanes.

import DASHI.Everything
import DASHI.Quantum.FastEverything
