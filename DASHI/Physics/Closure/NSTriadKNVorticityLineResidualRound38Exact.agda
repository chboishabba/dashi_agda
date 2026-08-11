module DASHI.Physics.Closure.NSTriadKNVorticityLineResidualRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- Communications in Partial Differential Equations 21 (1996), 559--571.
-- DOI: 10.1080/03605309608821197.
--
-- DASHI CONTRIBUTION
--
-- Round 37 put the physical vorticity-misalignment factor directly inside
-- the corrected Fourier strain action.  This module makes the associated
-- quotient residual exact without dividing by |v|^2:
--
--   delta_v(w) = w x v.
--
-- Adding any component parallel to the target line leaves delta_v unchanged,
-- and the corrected stretching scalar is therefore invariant under the same
-- parallel shift of its source vorticity.  Thus HH-good stretching depends
-- only on the source class modulo span(v), with the cross product serving as
-- a provenance-bearing receipt for the discarded direction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNVortexStretchingGeometricFactorRound37Exact as Stretch

lineResidual : V.Vector3 → V.Vector3 → V.Vector3
lineResidual target source = BS.cross source target

parallelShift : ℚ → V.Vector3 → V.Vector3 → V.Vector3
parallelShift amount target source =
  V.add source (V.scale amount target)

lineResidualOfParallelComponentZero :
  ∀ amount target →
  lineResidual target (V.scale amount target)
  ≡ V.v3 0ℚ 0ℚ 0ℚ
lineResidualOfParallelComponentZero amount
    (V.v3 tx ty tz) =
  V.vectorExt
    (solve (amount ∷ tx ∷ ty ∷ tz ∷ []))
    (solve (amount ∷ tx ∷ ty ∷ tz ∷ []))
    (solve (amount ∷ tx ∷ ty ∷ tz ∷ []))

lineResidualIgnoresParallelComponent :
  ∀ amount target source →
  lineResidual target (parallelShift amount target source)
  ≡ lineResidual target source
lineResidualIgnoresParallelComponent amount
    (V.v3 tx ty tz) (V.v3 sx sy sz) =
  V.vectorExt
    (solve (amount ∷ tx ∷ ty ∷ tz ∷ sx ∷ sy ∷ sz ∷ []))
    (solve (amount ∷ tx ∷ ty ∷ tz ∷ sx ∷ sy ∷ sz ∷ []))
    (solve (amount ∷ tx ∷ ty ∷ tz ∷ sx ∷ sy ∷ sz ∷ []))

record SameModuloTargetLine
    (target left right : V.Vector3) : Set where
  constructor same-modulo-target-line
  field
    shiftAmount : ℚ
    rightIsParallelShift :
      right ≡ parallelShift shiftAmount target left

open SameModuloTargetLine public

lineResidualDescendsToLineQuotient :
  ∀ {target left right} →
  SameModuloTargetLine target left right →
  lineResidual target right ≡ lineResidual target left
lineResidualDescendsToLineQuotient
    {target} {left} {right} witness =
  trans
    (cong (lineResidual target) (rightIsParallelShift witness))
    (lineResidualIgnoresParallelComponent
      (shiftAmount witness) target left)

stretchingIgnoresParallelSourceComponent :
  ∀ amount theta source target →
  Stretch.stretchingScalar theta
      (parallelShift amount target source) target
  ≡ Stretch.stretchingScalar theta source target
stretchingIgnoresParallelSourceComponent amount theta source target =
  trans
    (Stretch.stretchingScalarMisalignmentFactor
      theta (parallelShift amount target source) target)
    (trans
      (cong
        (λ residual →
          (- 1ℚ) * V.dot theta target * V.dot theta residual)
        (lineResidualIgnoresParallelComponent amount target source))
      (sym (Stretch.stretchingScalarMisalignmentFactor
        theta source target)))

stretchingDescendsToSourceLineQuotient :
  ∀ theta {source target shifted} →
  SameModuloTargetLine target source shifted →
  Stretch.stretchingScalar theta shifted target
  ≡ Stretch.stretchingScalar theta source target
stretchingDescendsToSourceLineQuotient
    theta {source} {target} {shifted} witness =
  trans
    (cong
      (λ actualSource →
        Stretch.stretchingScalar theta actualSource target)
      (rightIsParallelShift witness))
    (stretchingIgnoresParallelSourceComponent
      (shiftAmount witness) theta source target)

vorticityLineResidualQuotientClosed : Bool
vorticityLineResidualQuotientClosed = true

vorticityLineResidualQuotientClosedIsTrue :
  vorticityLineResidualQuotientClosed ≡ true
vorticityLineResidualQuotientClosedIsTrue = refl
