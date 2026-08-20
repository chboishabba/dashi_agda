module DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND104 / UNIFORM GALERKIN SIGNED-CRITICAL-PRODUCTION COMPILER
--
-- The Clay-level discovery theorem should be stated on the COMPLETE SIGNED
-- H^(1/2) production, before per-owner absolute values.  The analytic target is
-- an integrated estimate of the schematic form
--
--   N_N <= a D_N + F_N
--
-- together with the exact critical energy inequality
--
--   X_N(T) + v D_N <= X_N(0) + N_N.
--
-- This file proves, over exact rationals and without a target receipt, the
-- elimination step
--
--   X_N(T) + (v-a) D_N <= X_N(0) + F_N.
--
-- If X_N(0)+F_N has one cutoff-independent ceiling, the retained-viscosity
-- critical barrier is uniform in N.  Thus after a physical signed-production
-- theorem is proved there is no second nonlinear estimate to discover.
--
-- IMPORTANT SCALING BOUNDARY
--
-- Round43 already proves on the literal vorticity carrier that nonlinear
-- production is cubic under common amplitude scaling whereas viscous charge is
-- quadratic.  Therefore a universal arbitrary-data theorem with F_N=0 and a
-- fixed sub-viscous coefficient cannot be manufactured from instantaneous
-- homogeneity alone.  The surviving frontier must exploit signed network
-- cancellation and/or a data/history-dependent integrable remainder F_N.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNHHBadAmplitudeHomogeneityRound43Exact as Amplitude

record IntegratedSignedCriticalSlice : Set where
  constructor integrated-signed-critical-slice
  field
    initialCritical : ℚ
    terminalCritical : ℚ
    criticalDissipation : ℚ
    integratedSignedProduction : ℚ
    integrableRemainder : ℚ
    viscousCoefficient : ℚ
    absorbedCoefficient : ℚ

    criticalEnergyInequality :
      terminalCritical + viscousCoefficient * criticalDissipation
      ≤ initialCritical + integratedSignedProduction

    signedProductionEstimate :
      integratedSignedProduction
      ≤ absorbedCoefficient * criticalDissipation + integrableRemainder

open IntegratedSignedCriticalSlice public

retainedViscosity : IntegratedSignedCriticalSlice → ℚ
retainedViscosity S = viscousCoefficient S - absorbedCoefficient S

signedCriticalProductionAbsorbsIntoViscosity :
  (S : IntegratedSignedCriticalSlice) →
  terminalCritical S
    + retainedViscosity S * criticalDissipation S
  ≤ initialCritical S + integrableRemainder S
signedCriticalProductionAbsorbsIntoViscosity S =
  let
    energyThenProduction :
      terminalCritical S + viscousCoefficient S * criticalDissipation S
      ≤
      initialCritical S
      + (absorbedCoefficient S * criticalDissipation S
        + integrableRemainder S)
    energyThenProduction =
      ℚP.≤-trans
        (criticalEnergyInequality S)
        (ℚP.+-mono-≤
          ℚP.≤-refl
          (signedProductionEstimate S))

    shifted :
      terminalCritical S
        + viscousCoefficient S * criticalDissipation S
        - absorbedCoefficient S * criticalDissipation S
      ≤
      initialCritical S
        + (absorbedCoefficient S * criticalDissipation S
          + integrableRemainder S)
        - absorbedCoefficient S * criticalDissipation S
    shifted =
      ℚP.+-mono-≤
        energyThenProduction
        ℚP.≤-refl

    leftMeaning :
      terminalCritical S
        + viscousCoefficient S * criticalDissipation S
        - absorbedCoefficient S * criticalDissipation S
      ≡
      terminalCritical S
        + retainedViscosity S * criticalDissipation S
    leftMeaning =
      solve
        ( terminalCritical S ∷ viscousCoefficient S
        ∷ absorbedCoefficient S ∷ criticalDissipation S ∷ [])

    rightMeaning :
      initialCritical S
        + (absorbedCoefficient S * criticalDissipation S
          + integrableRemainder S)
        - absorbedCoefficient S * criticalDissipation S
      ≡ initialCritical S + integrableRemainder S
    rightMeaning =
      solve
        ( initialCritical S ∷ absorbedCoefficient S
        ∷ criticalDissipation S ∷ integrableRemainder S ∷ [])
  in
  subst
    (λ left → left ≤ initialCritical S + integrableRemainder S)
    leftMeaning
    (subst
      (λ right →
        terminalCritical S
          + viscousCoefficient S * criticalDissipation S
          - absorbedCoefficient S * criticalDissipation S
        ≤ right)
      rightMeaning
      shifted)

record UniformSignedCriticalProductionFamily : Set₁ where
  constructor uniform-signed-critical-production-family
  field
    Cutoff : Set
    slice : Cutoff → IntegratedSignedCriticalSlice
    uniformCriticalCeiling : ℚ
    uniformInitialPlusRemainder :
      (N : Cutoff) →
      initialCritical (slice N) + integrableRemainder (slice N)
      ≤ uniformCriticalCeiling

open UniformSignedCriticalProductionFamily public

-- This is the exact algebraic theorem represented by the requested name.
-- The physical work is constructing `slice N` from the complete literal
-- heterochiral Galerkin network with a cutoff-uniform remainder budget.
uniformGalerkinSignedCriticalProduction :
  (F : UniformSignedCriticalProductionFamily) →
  (N : Cutoff F) →
  terminalCritical (slice F N)
    + retainedViscosity (slice F N)
        * criticalDissipation (slice F N)
  ≤ uniformCriticalCeiling F
uniformGalerkinSignedCriticalProduction F N =
  ℚP.≤-trans
    (signedCriticalProductionAbsorbsIntoViscosity (slice F N))
    (uniformInitialPlusRemainder F N)

round104SignedProductionToUniformBarrierCompilerClosed : Bool
round104SignedProductionToUniformBarrierCompilerClosed = true

round104LiteralProductionCubicViscosityQuadraticReused : Bool
round104LiteralProductionCubicViscosityQuadraticReused =
  Amplitude.literalProductionAmplitudeDegree

-- NEW 3-D DISCOVERY THEOREM: construct the family above from the literal
-- complete Galerkin Waleffe network for arbitrary smooth data, with strictly
-- positive retained viscosity and one cutoff-independent remainder ceiling.
round104PhysicalUniformSignedCriticalProductionClosed : Bool
round104PhysicalUniformSignedCriticalProductionClosed = false

round104SignedProductionToUniformBarrierCompilerClosedIsTrue :
  round104SignedProductionToUniformBarrierCompilerClosed ≡ true
round104SignedProductionToUniformBarrierCompilerClosedIsTrue = refl

round104PhysicalUniformSignedCriticalProductionClosedIsFalse :
  round104PhysicalUniformSignedCriticalProductionClosed ≡ false
round104PhysicalUniformSignedCriticalProductionClosedIsFalse = refl