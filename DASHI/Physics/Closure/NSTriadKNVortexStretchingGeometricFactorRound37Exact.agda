module DASHI.Physics.Closure.NSTriadKNVortexStretchingGeometricFactorRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- DASHI CONTRIBUTION
--
-- Push the HH-good projector idea one step into the *actual strain action*.
-- The repository's corrected Fourier angular strain symbol is
--
--   S_theta(w) = -1/2 [ theta tensor (theta cross w)
--                     + (theta cross w) tensor theta ].
--
-- For a target vorticity v, this module proves exactly
--
--   v dot S_theta(w) v
--     = - (theta dot v) ((theta cross w) dot v)
--     = - (theta dot v) (theta dot (w cross v)).
--
-- Hence every cross-mode stretching contribution contains the vorticity
-- misalignment factor `w cross v` *before any estimate is taken*.  If source
-- and target vorticities are parallel, the interaction vanishes exactly.
-- This is the algebraic geometric-depletion factor that the later periodic PV
-- estimate should combine with the Round-37 projector identity
--
--   a^2 b^2 ||Pi_xi-Pi_eta||_F^2 = 2 |omega_x cross omega_y|^2.
--
-- No singular-kernel or integrability estimate is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Strain

stretchingScalar : V.Vector3 → V.Vector3 → V.Vector3 → ℚ
stretchingScalar theta source target =
  V.dot target (Strain.apply (Strain.angularStrain theta source) target)

stretchingScalarBilinearFactor : ∀ theta source target →
  stretchingScalar theta source target
  ≡
  (- 1ℚ)
    * V.dot theta target
    * V.dot (BS.cross theta source) target
stretchingScalarBilinearFactor
    (V.v3 tx ty tz)
    (V.v3 sx sy sz)
    (V.v3 vx vy vz) =
  solve
    ( tx ∷ ty ∷ tz
    ∷ sx ∷ sy ∷ sz
    ∷ vx ∷ vy ∷ vz
    ∷ [])

scalarTripleCyclic : ∀ left middle right →
  V.dot (BS.cross left middle) right
  ≡ V.dot left (BS.cross middle right)
scalarTripleCyclic
    (V.v3 lx ly lz)
    (V.v3 mx my mz)
    (V.v3 rx ry rz) =
  solve
    ( lx ∷ ly ∷ lz
    ∷ mx ∷ my ∷ mz
    ∷ rx ∷ ry ∷ rz
    ∷ [])

stretchingScalarMisalignmentFactor : ∀ theta source target →
  stretchingScalar theta source target
  ≡
  (- 1ℚ)
    * V.dot theta target
    * V.dot theta (BS.cross source target)
stretchingScalarMisalignmentFactor theta source target =
  trans
    (stretchingScalarBilinearFactor theta source target)
    (cong
      (λ triple → (- 1ℚ) * V.dot theta target * triple)
      (scalarTripleCyclic theta source target))

parallelCrossZeroKillsStretching : ∀ theta source target →
  BS.cross source target ≡ V.v3 0ℚ 0ℚ 0ℚ →
  stretchingScalar theta source target ≡ 0ℚ
parallelCrossZeroKillsStretching theta source target crossZero =
  trans
    (stretchingScalarMisalignmentFactor theta source target)
    (trans
      (cong
        (λ crossValue →
          (- 1ℚ)
            * V.dot theta target
            * V.dot theta crossValue)
        crossZero)
      (solve (V.dot theta target ∷ [])))

vortexStretchingGeometricFactorClosed : Bool
vortexStretchingGeometricFactorClosed = true

periodicPVStretchingEstimateConstructed : Bool
periodicPVStretchingEstimateConstructed = false

vortexStretchingGeometricFactorClosedIsTrue :
  vortexStretchingGeometricFactorClosed ≡ true
vortexStretchingGeometricFactorClosedIsTrue = refl

periodicPVStretchingEstimateConstructedIsFalse :
  periodicPVStretchingEstimateConstructed ≡ false
periodicPVStretchingEstimateConstructedIsFalse = refl
