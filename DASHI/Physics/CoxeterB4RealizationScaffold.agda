module DASHI.Physics.CoxeterB4RealizationScaffold where

-- Repo-facing aggregation surface for the current B₄ direction.
-- This now points to an independent shell/profile computation built from
-- explicit root-shell points and a Weyl-style action.
-- It is still not routed into the admissible rigidity harness, because
-- orientation/signature have not yet been justified for this realization.

open import DASHI.Physics.RootSystemB4Carrier public
open import DASHI.Physics.RootSystemB4WeylAction public
open import DASHI.Physics.OrbitProfileComputedRootSystemB4 public
