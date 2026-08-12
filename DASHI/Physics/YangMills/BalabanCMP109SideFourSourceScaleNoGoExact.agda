module DASHI.Physics.YangMills.BalabanCMP109SideFourSourceScaleNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The source setup preceding equations (0.1)--(0.12) requires the blocking
-- integer L to be odd and strictly greater than 11.  Several fixed-volume
-- Gate-I estimates in the repository use a side-four test torus.  Those are
-- useful finite estimates, but side four cannot be identified literally with
-- the source-admissible CMP109 equation-(0.12) scale.
--
-- This executable no-go keeps the two lanes separate:
--
--   side-four local carrier: L = 4, fails 12 <= L;
--   minimal source CMP109 carrier: L = 13, satisfies 12 <= L.
--
-- Therefore a same-object proof must either migrate the quantitative Gate-I
-- estimates to an admissible L (the source-faithful route), or independently
-- reprove the analytic averaging hypotheses at L=4.  Merely renaming the
-- side-four map as the CMP109 map is not a valid bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤ᵇ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as SideFour
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

sideFourFailsSourceLowerScale :
  (12 ≤ᵇ SideFour.side4) ≡ false
sideFourFailsSourceLowerScale = refl

minimalCMP109ScalePassesSourceLowerScale :
  (12 ≤ᵇ Minimal.side) ≡ true
minimalCMP109ScalePassesSourceLowerScale = Minimal.sideAboveEleven

cmp109SideFourSourceScaleNoGoLevel : ProofLevel
cmp109SideFourSourceScaleNoGoLevel = machineChecked

cmp109MinimalSourceScalePassesLevel : ProofLevel
cmp109MinimalSourceScalePassesLevel = machineChecked
