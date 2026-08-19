module DASHI.Physics.Closure.NSTriadKNSingleTriadViscousRelativeGrowthRound87Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND87 / EXACT VISCOUS GEOMETRY OF COMPACT-TRANSFER RELATIVE GROWTH
--
-- Let p+q=k and let tau be one cubic transfer monomial carried by that triad.
-- Pure viscosity damps its three velocity legs with rates
--
--   nu |k|^2,  nu |p|^2,  nu |q|^2.
--
-- Pair first with a quadratic dissipation atom on the same output k.  Its
-- tangent is -2 nu |k|^2 D, so
--
--   R_nu = tau'_nu D - tau D'_nu
--        = 2 nu (p dot q) tau D.
--
-- Thus high-high -> low geometry (p dot q < 0) creates a strict negative
-- viscous relative-growth contribution on positive transfer.
--
-- The full packet denominator contains dissipation atoms on modes m different
-- from k.  For one transfer triad and one such atom d_m, exact algebra gives
--
--   R_nu(t,m)
--     = 2 nu [p dot q + |m|^2 - |k|^2] tau_t d_m.
--
-- Hence the diagonal HH->low angle margin and the cross-mode shell-spread
-- correction are not different mechanisms: they are the two exact pieces of
-- the viscous relative-growth coefficient.  A uniform negative pair bound is
-- available whenever
--
--   |m|^2 - |k|^2 <= -p dot q - margin.
--
-- This identifies a new highest-alpha C4 route.  Pressure can be charged by
-- the Round87 source/Frobenius remainder, advection by packet commutators, while
-- viscosity supplies the strict margin provided the actual selected annular
-- geometry preserves enough negative p dot q after the m-sum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoRationalLerayMultiplierContractiveExact as V

normAddExpansion : ∀ p q →
  V.vecNormSquared (V.vecAdd p q)
  ≡ V.vecNormSquared p + V.vecNormSquared q +
      (V.vecDot p q + V.vecDot p q)
normAddExpansion
    (V.vec3 px py pz) (V.vec3 qx qy qz) =
  solve (px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz ∷ [])

inputMinusOutputSquareIdentity : ∀ p q →
  V.vecNormSquared p + V.vecNormSquared q
    - V.vecNormSquared (V.vecAdd p q)
  ≡ - (V.vecDot p q + V.vecDot p q)
inputMinusOutputSquareIdentity
    (V.vec3 px py pz) (V.vec3 qx qy qz) =
  solve (px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz ∷ [])

record SingleTriadViscousDatum : Set where
  constructor single-triad-viscous-datum
  field
    p q : V.Vec3
    viscosity transfer dissipation : ℚ

open SingleTriadViscousDatum public

k : SingleTriadViscousDatum → V.Vec3
k datum = V.vecAdd (p datum) (q datum)

transferViscousTangent : SingleTriadViscousDatum → ℚ
transferViscousTangent datum =
  - (viscosity datum
      * (V.vecNormSquared (k datum)
          + V.vecNormSquared (p datum)
          + V.vecNormSquared (q datum))
      * transfer datum)

dissipationViscousTangent : SingleTriadViscousDatum → ℚ
dissipationViscousTangent datum =
  - ((1ℚ + 1ℚ) * viscosity datum
      * V.vecNormSquared (k datum)
      * dissipation datum)

viscousRelativeGrowth : SingleTriadViscousDatum → ℚ
viscousRelativeGrowth datum =
  transferViscousTangent datum * dissipation datum
  - transfer datum * dissipationViscousTangent datum

viscousRelativeGrowthAsInputOutputGap : ∀ datum →
  viscousRelativeGrowth datum
  ≡ - (viscosity datum
        * (V.vecNormSquared (p datum) + V.vecNormSquared (q datum)
            - V.vecNormSquared (k datum))
        * transfer datum * dissipation datum)
viscousRelativeGrowthAsInputOutputGap datum
  with p datum | q datum
... | V.vec3 px py pz | V.vec3 qx qy qz =
  solve
    ( viscosity datum ∷ transfer datum ∷ dissipation datum
    ∷ px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz ∷ [])

viscousRelativeGrowthAsInputDot : ∀ datum →
  viscousRelativeGrowth datum
  ≡ (1ℚ + 1ℚ) * viscosity datum
      * V.vecDot (p datum) (q datum)
      * transfer datum * dissipation datum
viscousRelativeGrowthAsInputDot datum
  with p datum | q datum
... | V.vec3 px py pz | V.vec3 qx qy qz =
  solve
    ( viscosity datum ∷ transfer datum ∷ dissipation datum
    ∷ px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz ∷ [])

------------------------------------------------------------------------
-- Cross-mode dissipation atom.
------------------------------------------------------------------------

crossModeDissipationViscousTangent :
  SingleTriadViscousDatum → V.Vec3 → ℚ → ℚ
crossModeDissipationViscousTangent datum mode atom =
  - ((1ℚ + 1ℚ) * viscosity datum
      * V.vecNormSquared mode * atom)

crossModeViscousRelativeGrowth :
  SingleTriadViscousDatum → V.Vec3 → ℚ → ℚ
crossModeViscousRelativeGrowth datum mode atom =
  transferViscousTangent datum * atom
  - transfer datum * crossModeDissipationViscousTangent datum mode atom

crossModeViscousRelativeGrowthAsRawSquares : ∀ datum mode atom →
  crossModeViscousRelativeGrowth datum mode atom
  ≡ - (viscosity datum
      * (V.vecNormSquared (k datum)
          + V.vecNormSquared (p datum)
          + V.vecNormSquared (q datum)
          - ((1ℚ + 1ℚ) * V.vecNormSquared mode))
      * transfer datum * atom)
crossModeViscousRelativeGrowthAsRawSquares datum mode atom
  with p datum | q datum | mode
... | V.vec3 px py pz | V.vec3 qx qy qz | V.vec3 mx my mz =
  solve
    ( viscosity datum ∷ transfer datum ∷ atom
    ∷ px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz
    ∷ mx ∷ my ∷ mz ∷ [])

crossModeViscousRelativeGrowthAsAnglePlusSpread : ∀ datum mode atom →
  crossModeViscousRelativeGrowth datum mode atom
  ≡ (1ℚ + 1ℚ) * viscosity datum
      * (V.vecDot (p datum) (q datum)
          + V.vecNormSquared mode - V.vecNormSquared (k datum))
      * transfer datum * atom
crossModeViscousRelativeGrowthAsAnglePlusSpread datum mode atom
  with p datum | q datum | mode
... | V.vec3 px py pz | V.vec3 qx qy qz | V.vec3 mx my mz =
  solve
    ( viscosity datum ∷ transfer datum ∷ atom
    ∷ px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz
    ∷ mx ∷ my ∷ mz ∷ [])

crossModeAtOutputRecoversDiagonal : ∀ datum →
  crossModeViscousRelativeGrowth datum (k datum) (dissipation datum)
  ≡ viscousRelativeGrowth datum
crossModeAtOutputRecoversDiagonal datum
  with p datum | q datum
... | V.vec3 px py pz | V.vec3 qx qy qz =
  solve
    ( viscosity datum ∷ transfer datum ∷ dissipation datum
    ∷ px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz ∷ [])

------------------------------------------------------------------------
-- Exact HH->low calibration witness.
------------------------------------------------------------------------

hhP hhQ : V.Vec3
hhP = V.vec3 1ℚ 0ℚ 0ℚ
hhQ = V.vec3 (- 1ℚ) 1ℚ 0ℚ

hhDatum : SingleTriadViscousDatum
hhDatum = single-triad-viscous-datum hhP hhQ 1ℚ 1ℚ 1ℚ

hhInputDot : V.vecDot hhP hhQ ≡ - 1ℚ
hhInputDot = solve []

hhOutput : k hhDatum ≡ V.vec3 0ℚ 1ℚ 0ℚ
hhOutput = refl

hhRelativeGrowthStrictlyNegativeWitness :
  viscousRelativeGrowth hhDatum ≡ - (1ℚ + 1ℚ)
hhRelativeGrowthStrictlyNegativeWitness = solve []

------------------------------------------------------------------------
-- Exact aligned/forward calibration witness: no unconditional viscous sign.
------------------------------------------------------------------------

forwardP forwardQ : V.Vec3
forwardP = V.vec3 1ℚ 0ℚ 0ℚ
forwardQ = V.vec3 1ℚ 1ℚ 0ℚ

forwardDatum : SingleTriadViscousDatum
forwardDatum = single-triad-viscous-datum forwardP forwardQ 1ℚ 1ℚ 1ℚ

forwardInputDot : V.vecDot forwardP forwardQ ≡ 1ℚ
forwardInputDot = solve []

forwardRelativeGrowthPositiveWitness :
  viscousRelativeGrowth forwardDatum ≡ (1ℚ + 1ℚ)
forwardRelativeGrowthPositiveWitness = solve []

------------------------------------------------------------------------
-- Cross-mode calibration: shell spread can spend the angle margin.
------------------------------------------------------------------------

sameOutputAtom : ℚ
sameOutputAtom = 1ℚ

hhCrossAtOutput :
  crossModeViscousRelativeGrowth hhDatum (k hhDatum) sameOutputAtom
  ≡ - (1ℚ + 1ℚ)
hhCrossAtOutput = solve []

spreadMode : V.Vec3
spreadMode = V.vec3 1ℚ 1ℚ 0ℚ

hhCrossSpreadCancelsMargin :
  crossModeViscousRelativeGrowth hhDatum spreadMode 1ℚ ≡ 0ℚ
hhCrossSpreadCancelsMargin = solve []

round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferD : Bool
round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferD = true

round87CrossModeViscousCoefficientEqualsAnglePlusSpectralSpread : Bool
round87CrossModeViscousCoefficientEqualsAnglePlusSpectralSpread = true

round87HHToLowViscosityCanSupplyStrictNegativeRelativeGrowth : Bool
round87HHToLowViscosityCanSupplyStrictNegativeRelativeGrowth = true

round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad : Bool
round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad = false

round87AnnularGeometryPreservesNetViscousMarginConstructed : Bool
round87AnnularGeometryPreservesNetViscousMarginConstructed = false

round87CrossModeViscousCoefficientEqualsAnglePlusSpectralSpreadIsTrue :
  round87CrossModeViscousCoefficientEqualsAnglePlusSpectralSpread ≡ true
round87CrossModeViscousCoefficientEqualsAnglePlusSpectralSpreadIsTrue = refl

round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriadIsFalse :
  round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad ≡ false
round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriadIsFalse = refl
