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
-- ROUND87 / EXACT VISCOUS SIGN ON A SINGLE TRANSFER TRIAD
--
-- Let p+q=k and let tau be one cubic transfer monomial carried by that triad.
-- Pure viscosity damps its three velocity legs with rates
--
--   nu |k|^2,  nu |p|^2,  nu |q|^2,
--
-- while the output-shell quadratic dissipation D damps at twice the output
-- rate.  Therefore
--
--   tau'_nu = -nu (|k|^2+|p|^2+|q|^2) tau,
--   D'_nu   = -2 nu |k|^2 D,
--
-- and the compact-transfer relative-growth numerator contributed by this
-- monomial is
--
--   R_nu = tau'_nu D - tau D'_nu
--        = -nu (|p|^2+|q|^2-|k|^2) tau D
--        =  2 nu (p dot q) tau D.
--
-- Thus the sign is geometric.  In the high-high -> low regime the input modes
-- point substantially against one another, p dot q < 0, so positive transfer
-- receives a strictly negative viscous relative-growth contribution.  In a
-- forward/aligned triad p dot q can be positive, so viscosity is not a global
-- sign theorem without the triad geometry.
--
-- This exact identity suggests a sharper C4 architecture: extract the
-- negatively correlated HH->low triad mass as the strict margin and charge
-- the remaining triads/pressure/commutator pieces as remainders.  The missing
-- theorem is then an aggregation theorem preserving enough negative p dot q
-- mass, not a pointwise pressure-Hessian sign theorem.
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
-- Exact HH->low calibration witness.
------------------------------------------------------------------------

hhP hhQ : V.Vec3
hhP = V.vec3 1ℚ 0ℚ 0ℚ
hhQ = V.vec3 (- 1ℚ) 1ℚ 0ℚ

hhDatum : SingleTriadViscousDatum
hhDatum = single-triad-viscous-datum hhP hhQ 1ℚ 1ℚ 1ℚ

hhInputDot : V.vecDot hhP hhQ ≡ - 1ℚ
hhInputDot = refl

hhOutput : k hhDatum ≡ V.vec3 0ℚ 1ℚ 0ℚ
hhOutput = refl

hhRelativeGrowthStrictlyNegativeWitness :
  viscousRelativeGrowth hhDatum ≡ - (1ℚ + 1ℚ)
hhRelativeGrowthStrictlyNegativeWitness = refl

------------------------------------------------------------------------
-- Exact aligned/forward calibration witness: no unconditional viscous sign.
------------------------------------------------------------------------

forwardP forwardQ : V.Vec3
forwardP = V.vec3 1ℚ 0ℚ 0ℚ
forwardQ = V.vec3 1ℚ 1ℚ 0ℚ

forwardDatum : SingleTriadViscousDatum
forwardDatum = single-triad-viscous-datum forwardP forwardQ 1ℚ 1ℚ 1ℚ

forwardInputDot : V.vecDot forwardP forwardQ ≡ 1ℚ
forwardInputDot = refl

forwardRelativeGrowthPositiveWitness :
  viscousRelativeGrowth forwardDatum ≡ (1ℚ + 1ℚ)
forwardRelativeGrowthPositiveWitness = refl

round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferD : Bool
round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferD = true

round87HHToLowViscosityCanSupplyStrictNegativeRelativeGrowth : Bool
round87HHToLowViscosityCanSupplyStrictNegativeRelativeGrowth = true

round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad : Bool
round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad = false

round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferDIsTrue :
  round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferD ≡ true
round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferDIsTrue = refl

round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriadIsFalse :
  round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad ≡ false
round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriadIsFalse = refl
