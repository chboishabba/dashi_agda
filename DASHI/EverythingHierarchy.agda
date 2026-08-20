module DASHI.EverythingHierarchy where

-- Hierarchical repository umbrella.
--
-- Migration rule:
--   leaf -> subfolder Everything -> domain Everything -> repository umbrella
--
-- DASHI.Everything remains the historical lightweight/check-fast surface.
-- This module is the exhaustive hierarchical bridge: domains own their leaf
-- lists and the repository umbrella composes only domain rollups.

import DASHI.Everything

-- Mathematical / reasoning domains.
import DASHI.Algebra.Everything
import DASHI.Core.Everything
import DASHI.Cognition.Everything
import DASHI.Reasoning.Everything
import DASHI.Moonshine.Everything
import DASHI.Ontology.Everything
import DASHI.HME.Everything
import DASHI.DCHoTT.Everything
import DASHI.Energy.Everything
import DASHI.Quantum.ExhaustiveEverything

-- Natural / physical / applied domains.
import DASHI.Biology.DomainEverything
import DASHI.Chemistry.Everything
import DASHI.Physics.ExhaustiveEverything
import DASHI.Applied.Everything
import DASHI.Vision.Everything
import DASHI.Perception.Everything

-- Social / cultural / governance domains.
import DASHI.Culture.Everything
import DASHI.Social.Everything
import DASHI.Governance.Everything
import DASHI.Regulation.Everything
import DASHI.Philosophy.Everything
import DASHI.Music.Everything

-- Systems / tooling / cross-domain domains.
import DASHI.Context.Everything
import DASHI.Compression.Everything
import DASHI.Graph.Everything
import DASHI.Perf.Everything
import DASHI.Visualisation.Everything
import DASHI.Unified.Everything

-- Historical root-level tranche rollups.  New tranches should attach to the
-- nearest domain instead; this compatibility bucket keeps legacy Everything*
-- entrypoints reachable while that migration proceeds.
import DASHI.Tranches.Everything

-- Invariant for future migrations:
-- a specialized Everything surface should be imported by its nearest domain
-- parent, not directly here.  This file should stay a short domain manifest.
