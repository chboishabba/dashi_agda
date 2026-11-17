module DASHI.Physics.Gravity.KSW668F8AxialProjectionSourceShellTransferExact where

------------------------------------------------------------------------
-- XXXV: ORIGINAL KSW F8 angular projector -> radial shell source weld.
--
-- Original owners, reused unchanged:
--  KSW668F8RationalAxialTTCubatureExact
--  KSW668AdS5TTFiniteVolumeFirstCellRationalExact
--  scripts/ksw668_f8_fv_source_flux.py (p0/p2/p4 primitives).
--
-- The exact 12-node axial cubature is linear. Hence for a fixed
-- tensor angular polynomial and ANY scalar effective radial cell mass,
-- angular projection commutes with multiplying that mass. Original
-- source FV computes the latter with d=3+2ell shell weights, NOT the
-- naive ordinary 3D physical source cell mean.
--
-- SOURCE MASS: if weighted source density is primitive derivative,
-- cell mass P(b)-P(a) telescopes on arbitrary rational partitions.
-- For ell=4, the original primitive has a separately integrated
-- 27*r²*f(r) remainder. These identities alone do not prove the
-- derivative relation or a numerical error rate.
--
-- Crucial origin counterexample: with nondimensional h/eps=1/5
-- and regularized source g=1, the *physical* ordinary 3D first-cell
-- average of u^ell*g is 3/500 for ell=2, 3/70000 for ell=4;
-- evaluating u^ell at centre u=0 instead gives zero. The actual
-- solver averages g with effective d=7 or 11 radial weights.
--
-- No new tensor-to-FV isometry or full moving PDE convergence claim.
-- Pinned Agda kernel acceptance OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8RationalAxialTTCubatureExact as Angular
import DASHI.Physics.Gravity.KSW668F8TTSymbolDiscreteCompatibilityExact as TT

-- Original 12-node finite angular linearity: exact for arbitrary
-- rational samples and any common scalar shell mass.
angularShellScale :
  (f : ℚ → ℚ → ℚ) (m : ℚ) →
  Angular.rationalAzimuthalMean (λ y z → m * f y z)
  ≡ m * Angular.rationalAzimuthalMean f
angularShellScale f m = solve []

angularShellAdd :
  (f g : ℚ → ℚ → ℚ) →
  Angular.rationalAzimuthalMean (λ y z → f y z + g y z)
  ≡ Angular.rationalAzimuthalMean f
      + Angular.rationalAzimuthalMean g
angularShellAdd f g = solve []

-- For the ACTUAL full tensor at fixed Fourier (x,rho), angular
-- projection can therefore be performed before or after applying
-- the radial mass multiplier at that cell.
originalYYProjectedMass :
  (x rho mass : ℚ) →
  Angular.rationalAzimuthalMean
    (λ y z → mass * TT.ttYY x (rho * y) (rho * z))
    ≡ mass * Angular.axisA0 x rho
originalYYProjectedMass x rho mass
  rewrite angularShellScale
    (λ y z → TT.ttYY x (rho * y) (rho * z)) mass
    | Angular.axisAverageYY x rho = refl

originalZZProjectedMass :
  (x rho mass : ℚ) →
  Angular.rationalAzimuthalMean
    (λ y z → mass * TT.ttZZ x (rho * y) (rho * z))
    ≡ - (mass * Angular.axisA0 x rho)
originalZZProjectedMass x rho mass
  rewrite angularShellScale
    (λ y z → TT.ttZZ x (rho * y) (rho * z)) mass
    | Angular.axisAverageZZ x rho = solve []

-- Generic additive source-mass primitive telescope, for the exact
-- original endpoint-primitive construction in fv_source_flux.py.
-- For l=4, a separately integrated smooth remainder is also needed.
primitiveCellMass : (ℚ → ℚ) → ℚ → ℚ → ℚ
primitiveCellMass p a b = p b + - p a

primitivePartitionMass : (ℚ → ℚ) → List ℚ → ℚ
primitivePartitionMass p (a ∷ b ∷ xs) =
  primitiveCellMass p a b + primitivePartitionMass p (b ∷ xs)
primitivePartitionMass p _ = 0ℚ

lastEndpoint : List ℚ → ℚ
lastEndpoint [] = 0ℚ
lastEndpoint (a ∷ []) = a
lastEndpoint (a ∷ b ∷ xs) = lastEndpoint (b ∷ xs)

firstEndpoint : List ℚ → ℚ
firstEndpoint [] = 0ℚ
firstEndpoint (a ∷ xs) = a

sourcePrimitivePartitionTelescope :
  (p : ℚ → ℚ) (xs : List ℚ) →
  primitivePartitionMass p xs
    ≡ primitiveCellMass p (firstEndpoint xs) (lastEndpoint xs)
sourcePrimitivePartitionTelescope p [] = solve []
sourcePrimitivePartitionTelescope p (a ∷ []) = solve []
sourcePrimitivePartitionTelescope p (a ∷ b ∷ xs)
  rewrite sourcePrimitivePartitionTelescope p (b ∷ xs) = solve []

-- Constant regularized source g=1, first cell [0,1/10].
-- Physical 3D volume mean of u^ell is
-- (3/(3+ell))*(1/10)^ell; both are nonzero for ell>0.
originalPhysicalMeanEll2AtFirst :
  ((+ 3) / 5) * ((+ 1) / 10) * ((+ 1) / 10)
    ≡ (+ 3) / 500
originalPhysicalMeanEll2AtFirst = solve []

originalPhysicalMeanEll4AtFirst :
  ((+ 3) / 7) * ((+ 1) / 10) * ((+ 1) / 10)
    * ((+ 1) / 10) * ((+ 1) / 10)
    ≡ (+ 3) / 70000
originalPhysicalMeanEll4AtFirst = solve []

-- A centre-reconstructed physical origin sample vanishes (ell>0).
-- Do NOT confuse it with either of the positive physical cell means.
centrePhysicalEll2 : 0ℚ * 1ℚ ≡ 0ℚ
centrePhysicalEll2 = solve []

centrePhysicalEll4 : 0ℚ * 1ℚ ≡ 0ℚ
centrePhysicalEll4 = solve []
