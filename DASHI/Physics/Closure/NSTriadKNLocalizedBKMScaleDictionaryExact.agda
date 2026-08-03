module DASHI.Physics.Closure.NSTriadKNLocalizedBKMScaleDictionaryExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Venue/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prevent the several cutoff variables used by the Closure spine from being
-- conflated.  Luo's shell index p, dyadic wavenumber lambda_p = 2^p,
-- parabolic denominator lambda_p^2 = 2^(2p), finite Fourier-mode count,
-- profile depth, and Galerkin cutoff are distinct mathematical objects.
--
-- This module fixes a typed vocabulary and the exact dyadic identities used
-- by the localized-continuation lane.  It intentionally proves no asymptotic
-- comparison between mode count or profile depth and the physical dyadic
-- wavenumber; those require repository-specific identifications.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

------------------------------------------------------------------------
-- Typed roles.
------------------------------------------------------------------------

data ScaleRole : Set where
  shellIndexRole
  dyadicWavenumberRole
  parabolicDenominatorRole
  finiteModeCountRole
  profileDepthRole
  galerkinCutoffRole : ScaleRole

record TaggedScale : Set where
  constructor tagged
  field
    role : ScaleRole
    value : Nat

open TaggedScale public

------------------------------------------------------------------------
-- Exact dyadic convention used by Luo: lambda_p = 2^p.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc exponent) = suc (suc zero) * pow2 exponent

shellWavenumber : Nat → Nat
shellWavenumber = pow2

parabolicWindowDenominator : Nat → Nat
parabolicWindowDenominator shell = pow2 (shell + shell)

shellWavenumberMeaning :
  (shell : Nat) → shellWavenumber shell ≡ pow2 shell
shellWavenumberMeaning shell = refl

parabolicWindowMeaning :
  (shell : Nat) →
  parabolicWindowDenominator shell ≡ pow2 (shell + shell)
parabolicWindowMeaning shell = refl

------------------------------------------------------------------------
-- Explicit scale bundle.  No equality between the independent fields is
-- assumed merely because older modules happened to call each one `N`.
------------------------------------------------------------------------

record LocalizedBKMScaleDictionary : Set where
  constructor dictionary
  field
    shellIndex : Nat
    dyadicWavenumber : Nat
    parabolicDenominator : Nat
    finiteModeCount : Nat
    profileDepth : Nat
    galerkinCutoff : Nat

    dyadicWavenumberIsTwoToShell :
      dyadicWavenumber ≡ shellWavenumber shellIndex

    parabolicDenominatorIsLambdaSquared :
      parabolicDenominator ≡
        parabolicWindowDenominator shellIndex

open LocalizedBKMScaleDictionary public

canonicalScaleDictionary :
  (shell finiteCount depth cutoff : Nat) →
  LocalizedBKMScaleDictionary
canonicalScaleDictionary shell finiteCount depth cutoff =
  dictionary
    shell
    (shellWavenumber shell)
    (parabolicWindowDenominator shell)
    finiteCount
    depth
    cutoff
    refl
    refl

shellTag : LocalizedBKMScaleDictionary → TaggedScale
shellTag scale = tagged shellIndexRole (shellIndex scale)

wavenumberTag : LocalizedBKMScaleDictionary → TaggedScale
wavenumberTag scale = tagged dyadicWavenumberRole (dyadicWavenumber scale)

parabolicTag : LocalizedBKMScaleDictionary → TaggedScale
parabolicTag scale =
  tagged parabolicDenominatorRole (parabolicDenominator scale)

modeCountTag : LocalizedBKMScaleDictionary → TaggedScale
modeCountTag scale = tagged finiteModeCountRole (finiteModeCount scale)

profileDepthTag : LocalizedBKMScaleDictionary → TaggedScale
profileDepthTag scale = tagged profileDepthRole (profileDepth scale)

galerkinCutoffTag : LocalizedBKMScaleDictionary → TaggedScale
galerkinCutoffTag scale = tagged galerkinCutoffRole (galerkinCutoff scale)

------------------------------------------------------------------------
-- Honest status ledger.
------------------------------------------------------------------------

localizedBKMScaleRolesSeparated : Bool
localizedBKMScaleRolesSeparated = true

luoDyadicConventionRecorded : Bool
luoDyadicConventionRecorded = true

luoParabolicWindowScalingRecorded : Bool
luoParabolicWindowScalingRecorded = true

modeCountIdentifiedWithDyadicWavenumber : Bool
modeCountIdentifiedWithDyadicWavenumber = false

profileDepthIdentifiedWithShellIndex : Bool
profileDepthIdentifiedWithShellIndex = false

galerkinCutoffIdentifiedWithShellIndex : Bool
galerkinCutoffIdentifiedWithShellIndex = false

localizedBKMScaleRolesSeparatedIsTrue :
  localizedBKMScaleRolesSeparated ≡ true
localizedBKMScaleRolesSeparatedIsTrue = refl

luoDyadicConventionRecordedIsTrue :
  luoDyadicConventionRecorded ≡ true
luoDyadicConventionRecordedIsTrue = refl

luoParabolicWindowScalingRecordedIsTrue :
  luoParabolicWindowScalingRecorded ≡ true
luoParabolicWindowScalingRecordedIsTrue = refl

modeCountIdentifiedWithDyadicWavenumberIsFalse :
  modeCountIdentifiedWithDyadicWavenumber ≡ false
modeCountIdentifiedWithDyadicWavenumberIsFalse = refl

profileDepthIdentifiedWithShellIndexIsFalse :
  profileDepthIdentifiedWithShellIndex ≡ false
profileDepthIdentifiedWithShellIndexIsFalse = refl

galerkinCutoffIdentifiedWithShellIndexIsFalse :
  galerkinCutoffIdentifiedWithShellIndex ≡ false
galerkinCutoffIdentifiedWithShellIndexIsFalse = refl
