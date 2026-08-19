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
-- Using p+q=k, the bracket is
--
--   |m|^2 - (|k|^2+|p|^2+|q|^2)/2.
--
-- Therefore a very cheap sufficient HH->low criterion is available.  For any
-- scale mass M>=0, if
--
--   |p|^2 >= 4M,  |q|^2 >= 4M,  |m|^2 <= 3M,
--
-- then the bracket is <= -M (the extra -|k|^2/2 is simply discarded).
-- This is deliberately matched to the repository's max-norm dyadic shell
-- convention: a packet mode in shell K has Euclidean square <= 3*4^K, while a
-- leg separated upward by three dyadic shells has far more than the required
-- 4*4^K square.  The remaining physical bridge is finite shell/integer
-- arithmetic from the existing `Csep = 3` policy, not a new PDE inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; -_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

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

crossModeBracket : SingleTriadViscousDatum → V.Vec3 → ℚ
crossModeBracket datum mode =
  V.vecDot (p datum) (q datum)
    + V.vecNormSquared mode - V.vecNormSquared (k datum)

crossModeBracketAsSquares : ∀ datum mode →
  crossModeBracket datum mode
  ≡ V.vecNormSquared mode
      - ((V.vecNormSquared (k datum)
          + V.vecNormSquared (p datum)
          + V.vecNormSquared (q datum)) * (Int.+ 1 / 2))
crossModeBracketAsSquares datum mode
  with p datum | q datum | mode
... | V.vec3 px py pz | V.vec3 qx qy qz | V.vec3 mx my mz =
  solve (px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz ∷ mx ∷ my ∷ mz ∷ [])

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
      * crossModeBracket datum mode
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
-- Cheap quantitative HH->low angle-vs-packet-spread criterion.
------------------------------------------------------------------------

four three : ℚ
four = Int.+ 4 / 1
three = Int.+ 3 / 1

record HHToLowSquareEnvelope
    (datum : SingleTriadViscousDatum)
    (mode : V.Vec3) : Set where
  field
    scaleMass : ℚ
    scaleMassNonnegative : 0ℚ ≤ scaleMass
    pSquareLarge : four * scaleMass ≤ V.vecNormSquared (p datum)
    qSquareLarge : four * scaleMass ≤ V.vecNormSquared (q datum)
    packetModeSquareSmall : V.vecNormSquared mode ≤ three * scaleMass

open HHToLowSquareEnvelope public

vecNormSquaredNonnegative : ∀ value → 0ℚ ≤ V.vecNormSquared value
vecNormSquaredNonnegative (V.vec3 vx vy vz) =
  let
    sx = vx * vx
    sy = vy * vy
    sz = vz * vz
    sxNN = ℚP.squareNonnegative vx
    syNN = ℚP.squareNonnegative vy
    szNN = ℚP.squareNonnegative vz
  in
  ℚP.+-mono-≤ (ℚP.+-mono-≤ sxNN syNN) szNN

hhToLowEnvelopeForcesBracketBelowNegativeMass :
  ∀ {datum mode} →
  HHToLowSquareEnvelope datum mode →
  crossModeBracket datum mode ≤ - scaleMass _
hhToLowEnvelopeForcesBracketBelowNegativeMass {datum} {mode} envelope =
  let
    M = scaleMass envelope
    p2 = V.vecNormSquared (p datum)
    q2 = V.vecNormSquared (q datum)
    k2 = V.vecNormSquared (k datum)
    m2 = V.vecNormSquared mode

    pqLarge : (four * M) + (four * M) ≤ p2 + q2
    pqLarge = ℚP.+-mono-≤ (pSquareLarge envelope) (qSquareLarge envelope)

    withK : k2 + ((four * M) + (four * M)) ≤ k2 + (p2 + q2)
    withK = ℚP.+-monoˡ-≤ k2 pqLarge

    mBound : m2 + M ≤ four * M
    mBound =
      let raw = ℚP.+-mono-≤ (packetModeSquareSmall envelope) ℚP.≤-refl
      in subst (λ rhs → m2 + M ≤ rhs) (solve (M ∷ [])) raw

    doubled : (m2 + M) + (m2 + M) ≤ k2 + p2 + q2
    doubled =
      let
        twoLeftToEight : (m2 + M) + (m2 + M) ≤ (four * M) + (four * M)
        twoLeftToEight = ℚP.+-mono-≤ mBound mBound
        eightToWithK : (four * M) + (four * M) ≤ k2 + ((four * M) + (four * M))
        eightToWithK =
          let kNN = vecNormSquaredNonnegative (k datum)
              raw = ℚP.+-monoˡ-≤ ((four * M) + (four * M)) kNN
          in subst (λ rhs → (four * M) + (four * M) ≤ rhs)
               (solve (k2 ∷ M ∷ [])) raw
      in ℚP.≤-trans twoLeftToEight (ℚP.≤-trans eightToWithK
           (subst (λ rhs → k2 + ((four * M) + (four * M)) ≤ rhs)
             (solve (k2 ∷ p2 ∷ q2 ∷ [])) withK))

    finalSquareForm :
      m2 - ((k2 + p2 + q2) * (Int.+ 1 / 2)) ≤ - M
    finalSquareForm =
      -- Multiply the desired inequality by the positive factor two; `doubled`
      -- is exactly that statement after ring normalization.
      ℚP.≤-from-positive-scale-two
        (m2 - ((k2 + p2 + q2) * (Int.+ 1 / 2)))
        (- M)
        doubled
  in
  subst (λ lhs → lhs ≤ - M)
    (sym (crossModeBracketAsSquares datum mode)) finalSquareForm

------------------------------------------------------------------------
-- Exact HH->low and aligned calibration witnesses.
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

spreadMode : V.Vec3
spreadMode = V.vec3 1ℚ 1ℚ 0ℚ

hhCrossSpreadCancelsMargin :
  crossModeViscousRelativeGrowth hhDatum spreadMode 1ℚ ≡ 0ℚ
hhCrossSpreadCancelsMargin = solve []

round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferD : Bool
round87SingleTriadViscousRelativeGrowthEqualsTwoNuPDotQTransferD = true

round87CrossModeViscousCoefficientEqualsAnglePlusSpectralSpread : Bool
round87CrossModeViscousCoefficientEqualsAnglePlusSpectralSpread = true

round87HHToLowSquareEnvelopeForcesUniformNegativeBracket : Bool
round87HHToLowSquareEnvelopeForcesUniformNegativeBracket = true

round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad : Bool
round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad = false

round87LiteralCsepThreeShellEnvelopeConstructed : Bool
round87LiteralCsepThreeShellEnvelopeConstructed = false

round87HHToLowSquareEnvelopeForcesUniformNegativeBracketIsTrue :
  round87HHToLowSquareEnvelopeForcesUniformNegativeBracket ≡ true
round87HHToLowSquareEnvelopeForcesUniformNegativeBracketIsTrue = refl

round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriadIsFalse :
  round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriad ≡ false
round87ViscosityHasUnconditionalNegativeRelativeGrowthOnEveryTriadIsFalse = refl
