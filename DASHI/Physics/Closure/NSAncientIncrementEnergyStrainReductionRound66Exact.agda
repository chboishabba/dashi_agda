module DASHI.Physics.Closure.NSAncientIncrementEnergyStrainReductionRound66Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Theodore von Karman; Leslie Howarth.
-- Title: "On the Statistical Theory of Isotropic Turbulence".
-- Proceedings of the Royal Society A 164 (1938), 192--215.
-- DOI: 10.1098/rspa.1938.0013.
--
-- ROUND66 / INCREMENT ENERGY: EXACT CANCELLATION + STRAIN REDUCTION
--
-- For the velocity increment w(x)=u(x+h)-u(x), subtraction of the two
-- Navier--Stokes equations gives
--
--   d_t w + u(x+h).grad w
--     = -(w.grad)u - grad(delta_h p) + nu Delta w.
--
-- Pairing with w over a translation-invariant periodic cell (or over the
-- whole space when the integrations are justified) kills two terms exactly:
--
--   <w, u_h.grad w> = 0             (div u_h = 0),
--   <w, grad(delta_h p)> = 0        (div w = 0).
--
-- Hence
--
--   E'_h + nu D_h = - <w, (w.grad)u>.
--
-- The remaining contraction is w_i w_j partial_j u_i.  Since w_i w_j is
-- symmetric, the antisymmetric part of grad u is invisible: only the rate of
-- strain S=(grad u + grad u^T)/2 survives.  This file proves that algebra
-- exactly over rationals and gives the scalar energy-ledger reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

record Vector3 : Set where
  constructor v3
  field
    x y z : ℚ

open Vector3 public

record Gradient3 : Set where
  constructor grad3
  field
    g11 g12 g13 : ℚ
    g21 g22 g23 : ℚ
    g31 g32 g33 : ℚ

open Gradient3 public

transpose : Gradient3 → Gradient3
transpose G = grad3
  (g11 G) (g21 G) (g31 G)
  (g12 G) (g22 G) (g32 G)
  (g13 G) (g23 G) (g33 G)

bilinearContraction : Gradient3 → Vector3 → Vector3 → ℚ
bilinearContraction G a b =
    x a * (g11 G * x b + g12 G * y b + g13 G * z b)
  + y a * (g21 G * x b + g22 G * y b + g23 G * z b)
  + z a * (g31 G * x b + g32 G * y b + g33 G * z b)

incrementStretching : Gradient3 → Vector3 → ℚ
incrementStretching G w = bilinearContraction G w w

transposeInvisibleToQuadraticContraction :
  (G : Gradient3) →
  (w : Vector3) →
  incrementStretching (transpose G) w ≡ incrementStretching G w
transposeInvisibleToQuadraticContraction G w =
  solve
    ( g11 G ∷ g12 G ∷ g13 G
    ∷ g21 G ∷ g22 G ∷ g23 G
    ∷ g31 G ∷ g32 G ∷ g33 G
    ∷ x w ∷ y w ∷ z w ∷ [])

-- Twice the symmetric strain, avoiding division by two:
--
--   2 S = G + G^T.
--
twiceSymmetricPart : Gradient3 → Gradient3
twiceSymmetricPart G = grad3
  (g11 G + g11 G) (g12 G + g21 G) (g13 G + g31 G)
  (g21 G + g12 G) (g22 G + g22 G) (g23 G + g32 G)
  (g31 G + g13 G) (g32 G + g23 G) (g33 G + g33 G)

twiceStrainContraction : Gradient3 → Vector3 → ℚ
twiceStrainContraction G w = incrementStretching (twiceSymmetricPart G) w

incrementStretchingIsHalfSymmetricContractionDivisionFree :
  (G : Gradient3) →
  (w : Vector3) →
  twiceStrainContraction G w ≡ incrementStretching G w + incrementStretching G w
incrementStretchingIsHalfSymmetricContractionDivisionFree G w =
  solve
    ( g11 G ∷ g12 G ∷ g13 G
    ∷ g21 G ∷ g22 G ∷ g23 G
    ∷ g31 G ∷ g32 G ∷ g33 G
    ∷ x w ∷ y w ∷ z w ∷ [])

-- Literal skew gradient.  Its quadratic contraction vanishes identically,
-- which is the exact algebraic reason local rigid rotation does not contribute
-- to the increment-energy production.
antisymmetricGradient : ℚ → ℚ → ℚ → Gradient3
antisymmetricGradient a b c = grad3
  0ℚ a b
  (- a) 0ℚ c
  (- b) (- c) 0ℚ

antisymmetricGradientInvisible :
  (a b c : ℚ) →
  (w : Vector3) →
  incrementStretching (antisymmetricGradient a b c) w ≡ 0ℚ
antisymmetricGradientInvisible a b c w =
  solve (a ∷ b ∷ c ∷ x w ∷ y w ∷ z w ∷ [])

record IncrementEnergyLedger : Set where
  constructor increment-ledger
  field
    energyDerivative : ℚ
    viscousDissipation : ℚ
    transportPairing : ℚ
    pressurePairing : ℚ
    stretchingPairing : ℚ

    exactPairedIncrementEquation :
      energyDerivative + viscousDissipation + transportPairing
        ≡ - stretchingPairing - pressurePairing

    transportCancellation : transportPairing ≡ 0ℚ
    pressureCancellation : pressurePairing ≡ 0ℚ

open IncrementEnergyLedger public

incrementEnergyReducesExactlyToStretching :
  (L : IncrementEnergyLedger) →
  energyDerivative L + viscousDissipation L ≡ - stretchingPairing L
incrementEnergyReducesExactlyToStretching L =
  let
    full = exactPairedIncrementEquation L
    noTransport =
      subst
        (λ t → energyDerivative L + viscousDissipation L + t
          ≡ - stretchingPairing L - pressurePairing L)
        (transportCancellation L)
        full
    noPressure =
      subst
        (λ p → energyDerivative L + viscousDissipation L + 0ℚ
          ≡ - stretchingPairing L - p)
        (pressureCancellation L)
        noTransport
  in
  trans
    (solve (energyDerivative L ∷ viscousDissipation L ∷ []))
    (trans noPressure (solve (stretchingPairing L ∷ [])))
