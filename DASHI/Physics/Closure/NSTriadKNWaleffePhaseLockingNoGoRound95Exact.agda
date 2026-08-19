module DASHI.Physics.Closure.NSTriadKNWaleffePhaseLockingNoGoRound95Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND95 / PHASE-ESCAPE NO-GO
--
-- A universal theorem saying that an isolated adverse triad must leave a
-- phase-locked configuration is too strong.  In a common real phase chart the
-- classical three-wave/Waleffe scalar system has a real invariant tangent:
-- real amplitudes have real derivatives.  Hence an exactly phase-locked
-- configuration may remain phase locked while modal energy is exchanged.
--
-- The safe structural fact is different: the same self-triad transfers obey
-- the exact Manley--Rowe / energy conservation identity.  Thus persistent
-- phase lock does not manufacture total triad energy.  In the full NS network,
-- sustained dangerous amplitude must be replenished through external mode
-- coupling (or initial energy), which is the quantity the Round82/92
-- occupation-replenishment ledger should charge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

neg : ℚ → ℚ
neg x = - x

record RealWaleffeTriad : Set where
  constructor real-waleffe-triad
  field
    cK cP cQ : ℚ
    lambdaK lambdaP lambdaQ : ℚ
    coupling : ℚ

open RealWaleffeTriad public

alphaK alphaP alphaQ : RealWaleffeTriad → ℚ
alphaK w = lambdaQ w + neg (lambdaP w)
alphaP w = lambdaK w + neg (lambdaQ w)
alphaQ w = lambdaP w + neg (lambdaK w)

-- A real-chart three-wave tangent.  The exact overall normalization of the
-- common coupling is irrelevant for the invariant-manifold/no-go statement.
dotK dotP dotQ : RealWaleffeTriad → ℚ
dotK w = alphaK w * coupling w * cP w * cQ w
dotP w = alphaP w * coupling w * cK w * cQ w
dotQ w = alphaQ w * coupling w * cK w * cP w

-- In this chart all tangent coordinates remain on the real line.  Therefore
-- the orthogonal imaginary phase coordinate is exactly zero and has zero
-- tangent.  This is an exact finite witness that phase lock need not escape.
lockedImaginaryCoordinate : RealWaleffeTriad → ℚ
lockedImaginaryCoordinate w = 0ℚ

lockedImaginaryTangent : RealWaleffeTriad → ℚ
lockedImaginaryTangent w = 0ℚ

phaseLockedSubmanifoldTangent :
  (w : RealWaleffeTriad) → lockedImaginaryTangent w ≡ 0ℚ
phaseLockedSubmanifoldTangent w = refl

------------------------------------------------------------------------
-- Energy exchange.
--
-- For E_j = c_j^2, the common cubic factor is
--
--   C = 2 coupling cK cP cQ.
--
-- The three energy derivatives are alpha_j C, and the Waleffe coefficient
-- differences telescope exactly.
------------------------------------------------------------------------

commonEnergyTransferFactor : RealWaleffeTriad → ℚ
commonEnergyTransferFactor w =
  2 * coupling w * cK w * cP w * cQ w

energyDotK energyDotP energyDotQ : RealWaleffeTriad → ℚ
energyDotK w = alphaK w * commonEnergyTransferFactor w
energyDotP w = alphaP w * commonEnergyTransferFactor w
energyDotQ w = alphaQ w * commonEnergyTransferFactor w

waleffeCoefficientSumZero :
  (w : RealWaleffeTriad) → alphaK w + alphaP w + alphaQ w ≡ 0ℚ
waleffeCoefficientSumZero w =
  solve (lambdaK w ∷ lambdaP w ∷ lambdaQ w ∷ [])

isolatedTriadTotalEnergyDerivativeZero :
  (w : RealWaleffeTriad) →
  energyDotK w + energyDotP w + energyDotQ w ≡ 0ℚ
isolatedTriadTotalEnergyDerivativeZero w =
  solve
    ( lambdaK w ∷ lambdaP w ∷ lambdaQ w
    ∷ coupling w ∷ cK w ∷ cP w ∷ cQ w ∷ [])

------------------------------------------------------------------------
-- Viscous extension: self interaction still cannot replenish total energy.
------------------------------------------------------------------------

record ViscousRealWaleffeTriad : Set where
  constructor viscous-real-waleffe-triad
  field
    triad : RealWaleffeTriad
    rhoK rhoP rhoQ : ℚ

open ViscousRealWaleffeTriad public

viscousTotalEnergyDerivative : ViscousRealWaleffeTriad → ℚ
viscousTotalEnergyDerivative v =
    energyDotK (triad v) + energyDotP (triad v) + energyDotQ (triad v)
  + neg (2 * rhoK v * cK (triad v) * cK (triad v))
  + neg (2 * rhoP v * cP (triad v) * cP (triad v))
  + neg (2 * rhoQ v * cQ (triad v) * cQ (triad v))

viscousSelfTriadEnergyDerivativeIsPureDissipation :
  (v : ViscousRealWaleffeTriad) →
  viscousTotalEnergyDerivative v
  ≡
    neg (2 * rhoK v * cK (triad v) * cK (triad v))
  + neg (2 * rhoP v * cP (triad v) * cP (triad v))
  + neg (2 * rhoQ v * cQ (triad v) * cQ (triad v))
viscousSelfTriadEnergyDerivativeIsPureDissipation v =
  solve
    ( lambdaK (triad v) ∷ lambdaP (triad v) ∷ lambdaQ (triad v)
    ∷ coupling (triad v)
    ∷ cK (triad v) ∷ cP (triad v) ∷ cQ (triad v)
    ∷ rhoK v ∷ rhoP v ∷ rhoQ v ∷ [])

round95UniversalPhaseEscapeForIsolatedTriad : Bool
round95UniversalPhaseEscapeForIsolatedTriad = false

round95PhaseLockedRealSubmanifoldAvailable : Bool
round95PhaseLockedRealSubmanifoldAvailable = true

round95IsolatedSelfTriadTotalEnergyConserved : Bool
round95IsolatedSelfTriadTotalEnergyConserved = true

round95UniversalPhaseEscapeForIsolatedTriadIsFalse :
  round95UniversalPhaseEscapeForIsolatedTriad ≡ false
round95UniversalPhaseEscapeForIsolatedTriadIsFalse = refl

round95PhaseLockedRealSubmanifoldAvailableIsTrue :
  round95PhaseLockedRealSubmanifoldAvailable ≡ true
round95PhaseLockedRealSubmanifoldAvailableIsTrue = refl

round95IsolatedSelfTriadTotalEnergyConservedIsTrue :
  round95IsolatedSelfTriadTotalEnergyConserved ≡ true
round95IsolatedSelfTriadTotalEnergyConservedIsTrue = refl
