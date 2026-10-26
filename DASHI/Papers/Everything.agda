module DASHI.Papers.Everything where

-- Paper-facing theorem/interface ownership surface.
-- This layer preserves live historical theorem interfaces and manuscript-facing
-- contracts without moving them into implementation namespaces.

import DASHI.Papers.NavierStokes.Everything

-- Original source identities and non-promoting cross-paper source roles.
import DASHI.Papers.ThreePaperSourceAtlas20261025Exact

-- Consumer-relative semantic-fidelity obstructions reuse existing generic owners.
import DASHI.Papers.ThreePaperConsumerFidelity20261026Exact
