module DASHI.Physics.Closure.NSTriadKNQCriterionPressurePoissonRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. C. R. Hunt; A. A. Wray; P. Moin.
-- Title: "Eddies, streams, and convergence zones in turbulent flows".
-- Center for Turbulence Research, Proceedings of the 1988 Summer Program.
-- NASA NTRS: 19890015184.  DOI: not assigned in the cited report record.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- Journal of Fluid Mechanics 285 (1995), 69--94.
-- DOI: 10.1017/S0022112095000462.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND85 / EXACT Q-CRITERION NORMALIZATION AND ITS AUTHORITY BOUNDARY
--
-- The repository's Round78 convention is
--
--   Omega = |omega|^2,
--   Sigma = 2 S:S,
--   tr Hess(p) = Delta p = (Omega-Sigma)/2.
--
-- With the standard Q-criterion
--
--   Q = 1/2 (||Omega_tensor||_F^2 - ||S||_F^2)
--     = (Omega-Sigma)/4,
--
-- because ||Omega_tensor||_F^2 = |omega|^2/2.  Hence exactly
--
--   Delta p  =  2 Q,
--   -Delta p = -2 Q.
--
-- This corrects the tempting but incompatible coefficient
-- `S:S - |omega|^2/4` for the repository's Poisson source.  In the present
-- convention the source of -Delta p is
--
--   (Sigma-Omega)/2 = S:S - |omega|^2/2.
--
-- There is a useful positive compression: Round78's isotropic pressure
-- contraction is exactly
--
--   omega^T H^I omega = (2/3) Omega Q.
--
-- But Q controls only the trace/isotropic pressure information.  Reusing the
-- Round79 exact pair of trace-zero Hessians, this module proves that the same Q
-- (indeed Q=0 and the same trace) can coexist with different off-diagonal
-- eigenframe injection.  Therefore Q sign cannot replace the full C3 pressure
-- contraction + off-diagonal/gap record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNIsotropicPressureEnstrophyStrainCriterionRound78Exact as Iso
import DASHI.Physics.Closure.NSTriadKNPressureContractionInjectionSeparationRound79Exact as Sep

half quarter twoThirds two : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4
twoThirds = Int.+ 2 / 3
two = Int.+ 2 / 1

qCriterion : ℚ → ℚ → ℚ
qCriterion enstrophy strainIntensity =
  quarter * (enstrophy - strainIntensity)

pressureLaplacianTrace : ℚ → ℚ → ℚ
pressureLaplacianTrace enstrophy strainIntensity =
  half * (enstrophy - strainIntensity)

pressurePoissonSource : ℚ → ℚ → ℚ
pressurePoissonSource enstrophy strainIntensity =
  half * (strainIntensity - enstrophy)

pressureTraceEqualsTwoQ : ∀ enstrophy strainIntensity →
  pressureLaplacianTrace enstrophy strainIntensity
  ≡ two * qCriterion enstrophy strainIntensity
pressureTraceEqualsTwoQ enstrophy strainIntensity =
  solve (enstrophy ∷ strainIntensity ∷ [])

negativePressureTraceEqualsPoissonSource : ∀ enstrophy strainIntensity →
  - pressureLaplacianTrace enstrophy strainIntensity
  ≡ pressurePoissonSource enstrophy strainIntensity
negativePressureTraceEqualsPoissonSource enstrophy strainIntensity =
  solve (enstrophy ∷ strainIntensity ∷ [])

pressurePoissonSourceEqualsNegativeTwoQ : ∀ enstrophy strainIntensity →
  pressurePoissonSource enstrophy strainIntensity
  ≡ - (two * qCriterion enstrophy strainIntensity)
pressurePoissonSourceEqualsNegativeTwoQ enstrophy strainIntensity =
  solve (enstrophy ∷ strainIntensity ∷ [])

isotropicPressureContractionEqualsTwoThirdsOmegaQ :
  ∀ enstrophy strainIntensity →
  Iso.isotropicPressureContraction enstrophy strainIntensity
  ≡ twoThirds * enstrophy * qCriterion enstrophy strainIntensity
isotropicPressureContractionEqualsTwoThirdsOmegaQ enstrophy strainIntensity =
  solve (enstrophy ∷ strainIntensity ∷ [])

qZeroWhenEnstrophyEqualsStrain : ∀ value →
  qCriterion value value ≡ 0ℚ
qZeroWhenEnstrophyEqualsStrain value = solve (value ∷ [])

isotropicPressureZeroOnQZeroDiagonal : ∀ value →
  Iso.isotropicPressureContraction value value ≡ 0ℚ
isotropicPressureZeroOnQZeroDiagonal value = solve (value ∷ [])

------------------------------------------------------------------------
-- Q / trace cannot determine off-diagonal pressure injection.
------------------------------------------------------------------------

matrixTrace : Matrix.Matrix3 → ℚ
matrixTrace pressure =
  Matrix.m11 pressure + Matrix.m22 pressure + Matrix.m33 pressure

zeroPressureTraceZero : matrixTrace Sep.zeroPressure ≡ 0ℚ
zeroPressureTraceZero = solve []

mixedPressureTraceZero : matrixTrace Sep.mixedPressure ≡ 0ℚ
mixedPressureTraceZero = solve []

zeroPressureTraceMatchesQZero :
  matrixTrace Sep.zeroPressure ≡ two * 0ℚ
zeroPressureTraceMatchesQZero = solve []

mixedPressureTraceMatchesQZero :
  matrixTrace Sep.mixedPressure ≡ two * 0ℚ
mixedPressureTraceMatchesQZero = solve []

record QTraceDeterminesFrameInjection : Set where
  field
    determine :
      (q : ℚ) (left right : Matrix.Matrix3) →
      matrixTrace left ≡ two * q →
      matrixTrace right ≡ two * q →
      Sep.frameInjection23 left ≡ Sep.frameInjection23 right

open QTraceDeterminesFrameInjection public

qTraceCannotDetermineFrameInjection :
  QTraceDeterminesFrameInjection → 0ℚ ≡ Int.+ 1 / 1
qTraceCannotDetermineFrameInjection candidate =
  let
    equalInjection = determine candidate
      0ℚ Sep.zeroPressure Sep.mixedPressure
      zeroPressureTraceMatchesQZero mixedPressureTraceMatchesQZero
  in
  trans
    (sym Sep.zeroFrameInjection)
    (trans equalInjection Sep.mixedFrameInjection)

round85QCriterionPressurePoissonNormalizationExact : Bool
round85QCriterionPressurePoissonNormalizationExact = true

round85IsotropicPressureDepletionEqualsTwoThirdsOmegaQ : Bool
round85IsotropicPressureDepletionEqualsTwoThirdsOmegaQ = true

round85QScalarDeterminesOffDiagonalPressureInjection : Bool
round85QScalarDeterminesOffDiagonalPressureInjection = false

round85QSignCanReplaceFullPressureDichotomy : Bool
round85QSignCanReplaceFullPressureDichotomy = false

round85QCriterionPressurePoissonNormalizationExactIsTrue :
  round85QCriterionPressurePoissonNormalizationExact ≡ true
round85QCriterionPressurePoissonNormalizationExactIsTrue = refl

round85QScalarDeterminesOffDiagonalPressureInjectionIsFalse :
  round85QScalarDeterminesOffDiagonalPressureInjection ≡ false
round85QScalarDeterminesOffDiagonalPressureInjectionIsFalse = refl
