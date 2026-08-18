module DASHI.Physics.Closure.NSTriadKNPositiveStretchingNotB2NoGoRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Zoran Grujic.
-- Title: "Vortex stretching and anisotropic diffusion in the 3D
-- Navier-Stokes equations".
-- DOI: 10.48550/arXiv.1405.3498.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- ROUND78 / SIGN INFORMATION IS STRICTLY WEAKER THAN B2
--
-- Multiscale positivity of S omega . omega and a transfer-favourable helical
-- class are useful search diagnostics, but B2 consumes a STRICT NET weighted
-- surplus after pressure/geometry/allocation depletion.  This concrete exact
-- rational witness has positive enabling stretching and nevertheless negative
-- net surplus.  Therefore positive stretching alone cannot be promoted to B2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _<_; 0ℚ)

import DASHI.Physics.Closure.NSTriadKNPressureStretchingCompetitionRound78Exact as Competition

one two : ℚ
one = Int.+ 1 / 1
two = Int.+ 2 / 1

positiveStretchingButDepleted : Competition.PressureStretchingBudget
positiveStretchingButDepleted =
  Competition.pressure-stretching-budget one 0ℚ two 0ℚ

rawEnablingIsPositive :
  0ℚ < Competition.enablingSide positiveStretchingButDepleted
rawEnablingIsPositive = _

netSurplusIsNegative :
  Competition.netStretchingSurplus positiveStretchingButDepleted < 0ℚ
netSurplusIsNegative = _

round78PositiveVortexStretchingImpliesB2 : Bool
round78PositiveVortexStretchingImpliesB2 = false

round78WaleffeOrGrujicSignDataStillNeedsNetSurplusEstimate : Bool
round78WaleffeOrGrujicSignDataStillNeedsNetSurplusEstimate = true

round78PositiveVortexStretchingImpliesB2IsFalse :
  round78PositiveVortexStretchingImpliesB2 ≡ false
round78PositiveVortexStretchingImpliesB2IsFalse = refl
