module DASHI.Physics.Closure.NSTriadKNSupercriticalExternalExcessOccupationRound96Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Author: Gregory L. Eyink.
-- Title: "Locality of turbulent cascades".
-- Physica D 207 (2005), 91--116.
-- DOI: 10.1016/j.physd.2005.05.018.
--
-- Authors: Gregory L. Eyink; Hussein Aluie.
-- Title: "Localness of energy cascade in hydrodynamic turbulence. I.
-- Smooth coarse graining".
-- Physics of Fluids 21 (2009), 115107.
-- DOI: 10.1063/1.3266883.
--
-- ROUND96 / TOP-DOWN SUPERCRITICAL-EXCESS REDUCTION
--
-- The strict replenishment target must not be strengthened into a global
-- inertial-manifold-style spectral-gap statement.  The existing compact-Gamma
-- absorption core is state dependent, and Cheskidov--Shvydkoy supplies the
-- correct local algebraic scale:
--
--   R_ext <= C D A.
--
-- Choose A_* and delta with
--
--   C A_* + delta <= nu.
--
-- Instead of assuming A <= A_* everywhere, write only
--
--   A <= A_* + X,   X >= 0,
--
-- where physically X is the supercritical excess (A-A_*)_+.  Then the exact
-- pointwise consequence is
--
--   R_ext + delta D <= nu D + C D X.
--
-- Thus the whole failure of strict viscous absorption is localized into ONE
-- nonnegative currency C D X.  Finite summation preserves the same identity:
--
--   sum R_ext + delta sum D
--     <= nu sum D + C sum (D X).
--
-- The remaining PDE theorem is therefore not a uniform worst-case spectral
-- gap.  It is an occupation/replenishment estimate paying the integrated
-- supercritical excess on the SAME physical solution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record ExternalCriticalExcessCell
    (nonlinearConstant threshold : ℚ) : Set where
  constructor external-critical-excess-cell
  field
    dissipation amplitude excess externalFlux : ℚ

    dissipationNonnegative : 0ℚ ≤ dissipation
    excessNonnegative : 0ℚ ≤ excess

    -- X may be chosen as (A-A_*)_+ in the physical realization.  The algebra
    -- needs only this division-free domination.
    amplitudeBelowThresholdPlusExcess :
      amplitude ≤ threshold + excess

    -- Literal external packet flux after the Round95 self/external split.
    externalFluxBelowCriticalProduct :
      externalFlux ≤ nonlinearConstant * (dissipation * amplitude)

open ExternalCriticalExcessCell public

externalCellAbsorbedModuloExcess :
  ∀ {C threshold viscosity delta : ℚ} →
  0ℚ ≤ C →
  C * threshold + delta ≤ viscosity →
  (cell : ExternalCriticalExcessCell C threshold) →
  externalFlux cell + delta * dissipation cell
  ≤ viscosity * dissipation cell
      + C * (dissipation cell * excess cell)
externalCellAbsorbedModuloExcess {C} {threshold} {viscosity} {delta}
    cNN headroom cell =
  let
    D = dissipation cell
    A = amplitude cell
    X = excess cell

    DA≤DThresholdPlusX :
      D * A ≤ D * (threshold + X)
    DA≤DThresholdPlusX =
      let instance dNN = nonNegative (dissipationNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg D (amplitudeBelowThresholdPlusExcess cell)

    CDA≤CDThresholdPlusX :
      C * (D * A) ≤ C * (D * (threshold + X))
    CDA≤CDThresholdPlusX =
      let instance cNNI = nonNegative cNN
      in ℚP.*-monoˡ-≤-nonNeg C DA≤DThresholdPlusX

    fluxToExpanded :
      externalFlux cell ≤ C * (D * (threshold + X))
    fluxToExpanded =
      ℚP.≤-trans
        (externalFluxBelowCriticalProduct cell)
        CDA≤CDThresholdPlusX

    addMargin :
      externalFlux cell + delta * D
      ≤ C * (D * (threshold + X)) + delta * D
    addMargin = ℚP.+-mono-≤ fluxToExpanded ℚP.≤-refl

    splitUpper :
      C * (D * (threshold + X)) + delta * D
      ≡ (C * threshold + delta) * D + C * (D * X)
    splitUpper = solve (C ∷ threshold ∷ delta ∷ D ∷ X ∷ [])

    expanded :
      externalFlux cell + delta * D
      ≤ (C * threshold + delta) * D + C * (D * X)
    expanded =
      subst
        (λ upper → externalFlux cell + delta * D ≤ upper)
        splitUpper addMargin

    headroomTimesD :
      (C * threshold + delta) * D ≤ viscosity * D
    headroomTimesD =
      let instance dNN = nonNegative (dissipationNonnegative cell)
      in ℚP.*-monoʳ-≤-nonNeg D headroom

    addExcess :
      (C * threshold + delta) * D + C * (D * X)
      ≤ viscosity * D + C * (D * X)
    addExcess = ℚP.+-mono-≤ headroomTimesD ℚP.≤-refl
  in
  ℚP.≤-trans expanded addExcess

sumExternalFlux :
  ∀ {C threshold} →
  List (ExternalCriticalExcessCell C threshold) → ℚ
sumExternalFlux [] = 0ℚ
sumExternalFlux (cell ∷ rest) =
  externalFlux cell + sumExternalFlux rest

sumDissipation :
  ∀ {C threshold} →
  List (ExternalCriticalExcessCell C threshold) → ℚ
sumDissipation [] = 0ℚ
sumDissipation (cell ∷ rest) =
  dissipation cell + sumDissipation rest

sumExcessCost :
  ∀ {C threshold} →
  List (ExternalCriticalExcessCell C threshold) → ℚ
sumExcessCost {C} [] = 0ℚ
sumExcessCost {C} (cell ∷ rest) =
  C * (dissipation cell * excess cell) + sumExcessCost rest

finiteExternalFluxAbsorbedModuloSupercriticalExcess :
  ∀ {C threshold viscosity delta : ℚ} →
  0ℚ ≤ C →
  C * threshold + delta ≤ viscosity →
  (cells : List (ExternalCriticalExcessCell C threshold)) →
  sumExternalFlux cells + delta * sumDissipation cells
  ≤ viscosity * sumDissipation cells + sumExcessCost cells
finiteExternalFluxAbsorbedModuloSupercriticalExcess cNN headroom [] =
  ℚP.≤-refl
finiteExternalFluxAbsorbedModuloSupercriticalExcess
    {C} {threshold} {viscosity} {delta}
    cNN headroom (cell ∷ rest) =
  let
    head = externalCellAbsorbedModuloExcess cNN headroom cell
    tail = finiteExternalFluxAbsorbedModuloSupercriticalExcess
      cNN headroom rest
    added = ℚP.+-mono-≤ head tail

    leftMeaning :
      (externalFlux cell + delta * dissipation cell)
        + (sumExternalFlux rest + delta * sumDissipation rest)
      ≡ sumExternalFlux (cell ∷ rest)
        + delta * sumDissipation (cell ∷ rest)
    leftMeaning = solve
      ( externalFlux cell ∷ dissipation cell
      ∷ sumExternalFlux rest ∷ sumDissipation rest ∷ delta ∷ [])

    rightMeaning :
      (viscosity * dissipation cell + C * (dissipation cell * excess cell))
        + (viscosity * sumDissipation rest + sumExcessCost rest)
      ≡ viscosity * sumDissipation (cell ∷ rest)
        + sumExcessCost (cell ∷ rest)
    rightMeaning = solve
      ( viscosity ∷ dissipation cell ∷ C ∷ excess cell
      ∷ sumDissipation rest ∷ sumExcessCost rest ∷ [])
  in
  subst
    (λ left → left ≤
      viscosity * sumDissipation (cell ∷ rest)
        + sumExcessCost (cell ∷ rest))
    leftMeaning
    (subst
      (λ right →
        (externalFlux cell + delta * dissipation cell)
          + (sumExternalFlux rest + delta * sumDissipation rest)
        ≤ right)
      rightMeaning added)

record ExternalSupercriticalExcessOccupationBudget : Set₁ where
  constructor external-supercritical-excess-occupation-budget
  field
    nonlinearConstant threshold viscosity strictMargin : ℚ
    nonlinearConstantNonnegative : 0ℚ ≤ nonlinearConstant
    viscosityHeadroom :
      nonlinearConstant * threshold + strictMargin ≤ viscosity

    cells : List
      (ExternalCriticalExcessCell nonlinearConstant threshold)

    marginEscape : ℚ

    -- THIS is the source-facing occupation theorem after the top-down split.
    -- It is solution-dependent and does not assert a global Lipschitz/spectral
    -- gap for the Navier--Stokes vector field.
    supercriticalExcessPaidByEscape :
      sumExcessCost cells ≤ marginEscape

open ExternalSupercriticalExcessOccupationBudget public

externalFluxAbsorbedUpToEscapeMargin :
  (budget : ExternalSupercriticalExcessOccupationBudget) →
  sumExternalFlux (cells budget)
    + strictMargin budget * sumDissipation (cells budget)
  ≤ viscosity budget * sumDissipation (cells budget)
    + marginEscape budget
externalFluxAbsorbedUpToEscapeMargin budget =
  let
    base = finiteExternalFluxAbsorbedModuloSupercriticalExcess
      (nonlinearConstantNonnegative budget)
      (viscosityHeadroom budget)
      (cells budget)
    replaceExcess = ℚP.+-mono-≤ ℚP.≤-refl
      (supercriticalExcessPaidByEscape budget)
  in
  ℚP.≤-trans base replaceExcess

round96WorstCaseUniformSpectralGapRequired : Bool
round96WorstCaseUniformSpectralGapRequired = false

round96SubcriticalCriticalAmplitudeAbsorbsAutomatically : Bool
round96SubcriticalCriticalAmplitudeAbsorbsAutomatically = true

round96OnlySupercriticalExcessRemainsUnabsorbed : Bool
round96OnlySupercriticalExcessRemainsUnabsorbed = true

round96ExternalFluxAbsorbedModuloExcessConstructed : Bool
round96ExternalFluxAbsorbedModuloExcessConstructed = true

round96PhysicalSupercriticalExcessOccupationConstructed : Bool
round96PhysicalSupercriticalExcessOccupationConstructed = false

round96ExternalFluxAbsorbedModuloExcessConstructedIsTrue :
  round96ExternalFluxAbsorbedModuloExcessConstructed ≡ true
round96ExternalFluxAbsorbedModuloExcessConstructedIsTrue = refl

round96PhysicalSupercriticalExcessOccupationConstructedIsFalse :
  round96PhysicalSupercriticalExcessOccupationConstructed ≡ false
round96PhysicalSupercriticalExcessOccupationConstructedIsFalse = refl
