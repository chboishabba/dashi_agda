module DASHI.Physics.Closure.NSTriadKNNonlinearProfileMixedDefectSourceRound261Exact where

------------------------------------------------------------------------
-- ROUND261 / NONLINEAR PROFILE DECOMPOSITION -> MIXED-DEFECT DECOUPLING
--
-- Sources:
-- * I. Gallagher, Bull. Soc. Math. France 129 (2001), 285--316,
--   DOI 10.24033/bsmf.2398.
--   For orthogonal nonlinear Navier--Stokes profiles, distinct-profile
--   products vanish in L^4_t L^2_x; on finite time intervals this implies the
--   L^2_t L^2_x decay needed here.
-- * I. Gallagher, G. Koch, F. Planchon, Math. Ann. 355 (2013), 1527--1559,
--   DOI 10.1007/s00208-012-0830-0, arXiv:1012.0145.
--   Profile decomposition / critical-element method in critical NS spaces.
--
-- The mixed-helicity defect has the algebraic form
--
--   M(u) = H u x u,
--
-- with H = |D|^-1 curl an order-zero Fourier multiplier.  For a profile sum
-- u = sum_j v^j + r,
--
--   M(u) = sum_j M(v^j)
--          + sum_{j != k} (H v^j) x v^k
--          + profile/remainder cross terms + M(r).
--
-- H commutes with translations and NS scaling and preserves the profile
-- parameter orthogonality.  Gallagher's distinct-profile product decay
-- therefore kills every j != k term with H in either slot.  Smallness of the
-- remainder in the critical L^3 class plus the standard energy control pays
-- the remainder cross terms.  Hence the spacetime mixed defect is asymptotic
-- to the sum of the individual profile defects.
--
-- This is the exact bridge needed by Round256.  No new nonlinear invariant is
-- introduced: the profile theorem acts on the same M(u) used by Round227--241.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record NonlinearMixedDefectProfileTheorem
    {ℓ : Level} (Profile : Set ℓ) : Set (lsuc ℓ) where
  field
    nonlinearProfiles : Set ℓ
    profileParameterOrthogonality : Set ℓ

    normalizedCurlOrderZero : Set ℓ
    normalizedCurlTranslationEquivariant : Set ℓ
    normalizedCurlScalingEquivariant : Set ℓ

    distinctProfileProductsVanishL4tL2x : Set ℓ
    finiteTimeDistinctProfileProductsVanishL2tL2x : Set ℓ
    normalizedCurlCrossProfileTermsVanish : Set ℓ

    remainderCriticalSmall : Set ℓ
    remainderMixedTermsVanish : Set ℓ

    mixedDefectAsymptoticAdditivity : Set ℓ

open NonlinearMixedDefectProfileTheorem public

round261GallagherDistinctProfileDecayDirectlyMatchesMixedDefectCrossTerms : Bool
round261GallagherDistinctProfileDecayDirectlyMatchesMixedDefectCrossTerms = true

round261NoSeparateMixedHelicityProfileTheoremNeeded : Bool
round261NoSeparateMixedHelicityProfileTheoremNeeded = true

round261MixedDefectAsymptoticAdditivitySourceDerived : Bool
round261MixedDefectAsymptoticAdditivitySourceDerived = true

round261AnalyticProfileLimitsKernelDerivedInFiniteAgda : Bool
round261AnalyticProfileLimitsKernelDerivedInFiniteAgda = false

round261PackageAClosed : Bool
round261PackageAClosed = false

round261MixedDefectAsymptoticAdditivitySourceDerivedIsTrue :
  round261MixedDefectAsymptoticAdditivitySourceDerived ≡ true
round261MixedDefectAsymptoticAdditivitySourceDerivedIsTrue = refl
