module DASHI.Physics.Closure.NSAncientStructureFluxDivergenceNoGoRound66Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Theodore von Karman; Leslie Howarth.
-- Title: "On the Statistical Theory of Isotropic Turbulence".
-- Proceedings of the Royal Society A 164 (1938), 192--215.
-- DOI: 10.1098/rspa.1938.0013.
--
-- Authors: Jean Duchon; Raoul Robert.
-- Title: "Inertial energy dissipation for weak solutions of incompressible
--         Euler and Navier-Stokes equations".
-- Nonlinearity 13 (2000), 249--255.
-- DOI: 10.1088/0951-7715/13/1/312.
--
-- ROUND66 / BOUNDED STRUCTURE FLUX DOES NOT ALGEBRAICALLY CONTROL ITS
-- SEPARATION-SPACE DIVERGENCE.
--
-- Round66 proved the positive bound |F_3| <= B S_2 after bounded ancient
-- normalization.  This file proves why that is not itself the oscillation
-- contraction theorem.  On a two-point separation stencil let
--
--   F_plus  =  B S,
--   F_minus = -B S,
--
-- so both endpoint fluxes saturate the same envelope.  If N is the inverse
-- mesh scale, the discrete separation derivative is
--
--   N (F_plus - F_minus) = 2 N B S.
--
-- Thus for fixed B,S > 0 it can exceed any prescribed theta*S by taking N
-- large.  A positive C-unit theorem must therefore use PDE regularity,
-- parabolic smoothing/Harnack, or another mechanism controlling variation of
-- the structure flux in h.  Pointwise flux linearization alone is insufficient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Relation.Nullary.Negation.Core using (¬_)

fluxPlus : ℚ → ℚ → ℚ
fluxPlus B S = B * S

fluxMinus : ℚ → ℚ → ℚ
fluxMinus B S = - (B * S)

discreteSeparationDivergence : ℚ → ℚ → ℚ → ℚ
discreteSeparationDivergence inverseMesh B S =
  inverseMesh * (fluxPlus B S - fluxMinus B S)

fluxPlusSaturatesEnvelope :
  (B S : ℚ) → fluxPlus B S ≡ B * S
fluxPlusSaturatesEnvelope B S = refl

fluxMinusSaturatesNegativeEnvelope :
  (B S : ℚ) → fluxMinus B S ≡ - (B * S)
fluxMinusSaturatesNegativeEnvelope B S = refl

divergenceIsTwiceInverseMeshFlux :
  (inverseMesh B S : ℚ) →
  discreteSeparationDivergence inverseMesh B S
    ≡ (1ℚ + 1ℚ) * inverseMesh * B * S
divergenceIsTwiceInverseMeshFlux inverseMesh B S =
  solve (inverseMesh ∷ B ∷ S ∷ [])

fixedDivergenceCoefficientFailsAtFineSeparationScale :
  (theta inverseMesh B S : ℚ) →
  0ℚ < S →
  theta < (1ℚ + 1ℚ) * inverseMesh * B →
  ¬ (discreteSeparationDivergence inverseMesh B S ≤ theta * S)
fixedDivergenceCoefficientFailsAtFineSeparationScale
    theta inverseMesh B S sPositive thetaBelow proposed =
  let
    instance sPos : Positive S
        sPos = positive sPositive

    scaledStrict :
      theta * S < ((1ℚ + 1ℚ) * inverseMesh * B) * S
    scaledStrict = ℚP.*-monoʳ-<-pos S thetaBelow

    proposedNormalized :
      ((1ℚ + 1ℚ) * inverseMesh * B) * S ≤ theta * S
    proposedNormalized =
      subst₂ _≤_
        (divergenceIsTwiceInverseMeshFlux inverseMesh B S)
        (solve (theta ∷ S ∷ []))
        proposed
  in
  ℚP.<-irrefl (theta * S)
    (ℚP.<-≤-trans scaledStrict proposedNormalized)
