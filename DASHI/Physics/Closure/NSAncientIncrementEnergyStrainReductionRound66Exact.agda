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

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

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

-- A purely antisymmetric velocity gradient contributes exactly zero.
record AntisymmetricGradientWitness (G : Gradient3) : Set where
  constructor antisymmetric-gradient
  field
    diagonal11Zero : g11 G ≡ 0ℚ
    diagonal22Zero : g22 G ≡ 0ℚ
    diagonal33Zero : g33 G ≡ 0ℚ
    pair12 : g21 G ≡ - g12 G
    pair13 : g31 G ≡ - g13 G
    pair23 : g32 G ≡ - g23 G

open AntisymmetricGradientWitness public

antisymmetricGradientInvisible :
  (G : Gradient3) →
  AntisymmetricGradientWitness G →
  (w : Vector3) →
  incrementStretching G w ≡ 0ℚ
antisymmetricGradientInvisible G anti w =
  subst
    (λ a33 →
      bilinearContraction
        (grad3 0ℚ (g12 G) (g13 G)
          (- g12 G) 0ℚ (g23 G)
          (- g13 G) (- g23 G) a33)
        w w ≡ 0ℚ)
    (diagonal33Zero anti)
    (subst
      (λ a32 →
        bilinearContraction
          (grad3 0ℚ (g12 G) (g13 G)
            (- g12 G) 0ℚ (g23 G)
            (- g13 G) a32 (g33 G))
          w w ≡ 0ℚ)
      (pair23 anti)
      (subst
        (λ a31 →
          bilinearContraction
            (grad3 0ℚ (g12 G) (g13 G)
              (- g12 G) 0ℚ (g23 G)
              a31 (g32 G) (g33 G))
            w w ≡ 0ℚ)
        (pair13 anti)
        (subst
          (λ a22 →
            bilinearContraction
              (grad3 0ℚ (g12 G) (g13 G)
                (- g12 G) a22 (g23 G)
                (g31 G) (g32 G) (g33 G))
              w w ≡ 0ℚ)
          (diagonal22Zero anti)
          (subst
            (λ a21 →
              bilinearContraction
                (grad3 0ℚ (g12 G) (g13 G)
                  a21 (g22 G) (g23 G)
                  (g31 G) (g32 G) (g33 G))
                w w ≡ 0ℚ)
            (pair12 anti)
            (subst
              (λ a11 →
                bilinearContraction
                  (grad3 a11 (g12 G) (g13 G)
                    (g21 G) (g22 G) (g23 G)
                    (g31 G) (g32 G) (g33 G))
                  w w ≡ 0ℚ)
              (diagonal11Zero anti)
              (solve
                ( g12 G ∷ g13 G ∷ g23 G
                ∷ x w ∷ y w ∷ z w ∷ [])))))))

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
