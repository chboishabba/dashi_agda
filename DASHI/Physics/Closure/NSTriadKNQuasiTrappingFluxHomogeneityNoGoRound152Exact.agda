module DASHI.Physics.Closure.NSTriadKNQuasiTrappingFluxHomogeneityNoGoRound152Exact where

------------------------------------------------------------------------
-- ROUND152 / AUDIT OF A RECENT HELICAL QUASI-TRAPPING CLAIM
--
-- Source audited (not adopted as authority):
--   Luca Eliseo Pavesi,
--   "Global Regularity for the Three-Dimensional Incompressible Navier-Stokes
--   Equations via Geometric Frustration and Helical Quasi-Trapping" (2026),
--   Zenodo DOI 10.5281/zenodo.21194906.
--
-- The preprint states an absolute spectral-flux estimate of the form
--
--   |Pi(K)| <= C E_{>K}^{1/2} E^{1/2} / K.
--
-- Independently of any geometric detail, an amplitude-independent estimate of
-- this exact homogeneity cannot hold for the full quadratic NS nonlinearity:
-- under u -> A u,
--
--   spectral flux (one tested quadratic nonlinearity) scales as A^3,
--   E_{>K}^{1/2} E^{1/2} scales as A^2.
--
-- The theorem below makes the obstruction exact over positive rationals.  If a
-- nonzero base flux F and positive quadratic right-side carrier R are fixed,
-- any A satisfying C R < A F produces
--
--   C A^2 R < A^3 F.
--
-- Hence this recent claimed estimate is NOT imported into package A.  Any valid
-- flux theorem must carry cubic amplitude homogeneity (or a constant depending
-- on amplitude/energy in a way that restores it).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _<_; Positive; positive)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

data PositiveAmplitudeCounterScale : Set where
  counter-scale :
    (constant baseRhs baseFlux amplitude : ℚ) →
    0ℚ < amplitude →
    constant * baseRhs < amplitude * baseFlux →
    PositiveAmplitudeCounterScale

absoluteFluxScaled : ℚ → ℚ → ℚ
absoluteFluxScaled amplitude baseFlux =
  amplitude * amplitude * amplitude * baseFlux

quadraticEnergyRhsScaled : ℚ → ℚ → ℚ → ℚ
quadraticEnergyRhsScaled constant amplitude baseRhs =
  constant * (amplitude * amplitude * baseRhs)

cubicEventuallyBeatsQuadraticEnergyRhs :
  (constant baseRhs baseFlux amplitude : ℚ) →
  0ℚ < amplitude →
  constant * baseRhs < amplitude * baseFlux →
  quadraticEnergyRhsScaled constant amplitude baseRhs
  < absoluteFluxScaled amplitude baseFlux
cubicEventuallyBeatsQuadraticEnergyRhs constant baseRhs baseFlux amplitude
    amplitudePositive baseComparison =
  let
    amplitudeSquared = amplitude * amplitude
    amplitudeSquaredPositive : 0ℚ < amplitudeSquared
    amplitudeSquaredPositive =
      let
        instance aPos = positive amplitudePositive
      in ℚₚ.pos*pos⇒pos amplitude amplitude

    scaled :
      amplitudeSquared * (constant * baseRhs)
      < amplitudeSquared * (amplitude * baseFlux)
    scaled =
      let instance a2Pos = positive amplitudeSquaredPositive
      in ℚₚ.*-monoˡ-<-pos amplitudeSquared baseComparison

    lhsMeaning :
      amplitudeSquared * (constant * baseRhs)
      ≡ quadraticEnergyRhsScaled constant amplitude baseRhs
    lhsMeaning = solve (constant ∷ baseRhs ∷ amplitude ∷ [])

    rhsMeaning :
      amplitudeSquared * (amplitude * baseFlux)
      ≡ absoluteFluxScaled amplitude baseFlux
    rhsMeaning = solve (baseFlux ∷ amplitude ∷ [])
  in
  subst
    (λ left → left < absoluteFluxScaled amplitude baseFlux)
    lhsMeaning
    (subst
      (λ right → amplitudeSquared * (constant * baseRhs) < right)
      rhsMeaning
      scaled)

round152QuadraticEnergyFluxBoundFailsAmplitudeHomogeneity : Bool
round152QuadraticEnergyFluxBoundFailsAmplitudeHomogeneity = true

round152PavesiQuasiTrappingEstimateImportedAsPackageAAuthority : Bool
round152PavesiQuasiTrappingEstimateImportedAsPackageAAuthority = false

round152PackageAClosed : Bool
round152PackageAClosed = false

round152QuadraticEnergyFluxBoundFailsAmplitudeHomogeneityIsTrue :
  round152QuadraticEnergyFluxBoundFailsAmplitudeHomogeneity ≡ true
round152QuadraticEnergyFluxBoundFailsAmplitudeHomogeneityIsTrue = refl

round152PackageAClosedIsFalse : round152PackageAClosed ≡ false
round152PackageAClosedIsFalse = refl
