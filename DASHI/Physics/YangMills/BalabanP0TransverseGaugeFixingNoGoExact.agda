module DASHI.Physics.YangMills.BalabanP0TransverseGaugeFixingNoGoExact where

-- Adversarial check for proposed "Wilson quadratic K=d*d = Σ Δμ" weld.
-- The ORIGINAL Wilson flat curl only produces a TRANSVERSE symbol
-- K_{μν}(q)=hat(q)^2 delta_{μν}-hat(q)_μ hat(q)_ν.
-- The omitted longitudinal projector is not zero in general.
--
-- Correct positive producer:
-- K + (background-Feynman gauge fixing) = hat(q)^2 delta.
-- This simple rational identity is independent of any analytic or
-- Fourier source assumptions; physical identification with the real
-- lattice operators is separately required.
--
-- SU(2) adjoint C_A is TWO in the selected generator normalization,
-- not 2N=4. The universal rational beta normalization shown below
-- is ONLY color/numerical arithmetic, not the physical one-loop sum.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Physics.YangMills.BalabanClayT4LiteralVacuumPolarizationIntegralExact as VP
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopConventionExact as Convention

flatCurlSymbol : (hatSq delta hatMu hatNu : ℚ) → ℚ
flatCurlSymbol hatSq delta hatMu hatNu =
  hatSq * delta - hatMu * hatNu

feynmanGaugeLongitudinalSymbol : (hatMu hatNu : ℚ) → ℚ
feynmanGaugeLongitudinalSymbol hatMu hatNu = hatMu * hatNu

gaugeFixedSymbol : (hatSq delta hatMu hatNu : ℚ) → ℚ
gaugeFixedSymbol hatSq delta hatMu hatNu =
  flatCurlSymbol hatSq delta hatMu hatNu
    + feynmanGaugeLongitudinalSymbol hatMu hatNu

feynmanGaugeRestoresComponentLaplacian :
  ∀ hatSq delta hatMu hatNu →
  gaugeFixedSymbol hatSq delta hatMu hatNu
    ≡ hatSq * delta
feynmanGaugeRestoresComponentLaplacian hatSq delta hatMu hatNu =
  Ring.solve-∀ hatSq delta hatMu hatNu

-- A longitudinal example q=(1,0,0,0), mu=nu=0, hatSq=1.
-- The FLAT CURL symbol has value zero on the longitudinal component;
-- the componentwise scalar Laplacian has value one.
flatCurlLongitudinalExample :
  flatCurlSymbol 1ℚ 1ℚ 1ℚ 1ℚ ≡ 0ℚ
flatCurlLongitudinalExample = refl

componentLaplacianLongitudinalExample :
  1ℚ * 1ℚ ≡ 1ℚ
componentLaplacianLongitudinalExample = refl

flatCurlNotUnfixedComponentLaplacian :
  flatCurlSymbol 1ℚ 1ℚ 1ℚ 1ℚ ≢ (1ℚ * 1ℚ)
flatCurlNotUnfixedComponentLaplacian ()

-- Exact repo-source color/gauge convention consistency.
-- No false identification of the Wilson/ghost/Haar physical integrals
-- is manufactured from this purely rational coefficient arithmetic.
su2PureGaugeBetaRationalPrefactor :
  (VP.elevenThird * VP.su2AdjointCasimir)
    * (+ 1 / 16)
    ≡ Convention.universalColorCoefficient
su2PureGaugeBetaRationalPrefactor = Ring.solve-∀

-- Concrete SU(2) countercontrol for the attachment's 2N claim:
-- C_A=2, not 4, in Tr_fund(Ta Tb)=delta_ab/2 convention.
su2AdjointCasimirNotFour :
  VP.su2AdjointCasimir ≢ (+ 4 / 1)
su2AdjointCasimirNotFour ()
