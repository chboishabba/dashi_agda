module DASHI.Physics.QFT.MMPDiracCauchyNoncompactCompactDoubleBidiExact where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Geometry.LCP.Stream as Stream
import DASHI.Geometry.LCP.Cauchy as Sequence
import DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact as Lorentz
import DASHI.Physics.Gravity.PenroseGlobalHorismosContradictionExact as Horismos
import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFT

------------------------------------------------------------------------
-- Existing theorem owners reused at their ACTUAL level of generality:
-- * constructive Cauchy moduli for streams / Banach-LCP;
-- * Lorentzian global Cauchy / Minguzzi authority boundary;
-- * QFT time-slice/Cauchy-evolution target-only owner.
-- No new Lorentzian manifold or free spin-c field is postulated as an
-- inhabited mathematical object by these definitions.
------------------------------------------------------------------------

nativeConstructiveCauchyModulus :
  ∀ {ℓ : Level} {A : Set ℓ}
  (xs : Nat → Stream.Stream A) → Set ℓ
nativeConstructiveCauchyModulus xs = Sequence.CauchyMod xs

nativeGlobalCausalityOwner : Set
nativeGlobalCausalityOwner = Lorentz.GlobalCausalityAuthorityReceipt

nativeGlobalHorismosOwner : Set
nativeGlobalHorismosOwner = Horismos.PenroseGlobalHorismosBoundary

nativeAQFTCauchyEvolutionOwner : Set
nativeAQFTCauchyEvolutionOwner = AQFT.CauchyEvolutionStatus

nativeAQFTTimeSliceOwner : Set
nativeAQFTTimeSliceOwner = AQFT.TimeSliceTheoremStatus

data CauchyMeaning : Set where
  sequenceOrMetricLimit : CauchyMeaning
  lorentzianHypersurface : CauchyMeaning
  hyperbolicInitialValueProblem : CauchyMeaning
  aqftTimeSliceIsomorphism : CauchyMeaning

-- This is a source-typed semantic distinction, not a theorem about
-- Lorentzian global hyperbolicity.
sequenceCauchyIsNotSpacetimeCauchy :
  sequenceOrMetricLimit ≡ lorentzianHypersurface → ⊥
sequenceCauchyIsNotSpacetimeCauchy ()

------------------------------------------------------------------------
-- Capoferri--Murro 2025, Remark 3.8(2), DOI 10.1002/mana.12032:
-- For finite time, COMPACTLY SUPPORTED data on a globally hyperbolic
-- noncompact-Cauchy spacetime have a compact causal hull.
-- A relatively compact collar with smooth boundary can be doubled.
-- Finite propagation + Cauchy uniqueness identify the SAME solution
-- locally with compact-Cauchy evolution.  The following proof is
-- CONDITIONAL on supplied support, collar and uniqueness witnesses.
------------------------------------------------------------------------

record LocalFiniteTimeDiracCompactDouble
    (InitialDatum LocalObservation : Set) : Set₁ where
  field
    compactlySupported : InitialDatum → Set
    permittedFiniteTime : Nat → Set
    causalHullInsideSmoothDouble : InitialDatum → Nat → Set

    originalDataOnCausalHull : InitialDatum → Nat → LocalObservation
    doubleDataOnCausalHull : InitialDatum → Nat → LocalObservation
    originalEvolutionObserved : InitialDatum → Nat → LocalObservation
    doubledEvolutionObserved : InitialDatum → Nat → LocalObservation

    -- PAY THESE separately by the actual geometric support theorem,
    -- chosen compact doubling, and spin-c/gauge connection compatibility.
    finitePropagationAndCollarAgreement :
      ∀ datum t →
      compactlySupported datum →
      permittedFiniteTime t →
      causalHullInsideSmoothDouble datum t →
      originalDataOnCausalHull datum t ≡
        doubleDataOnCausalHull datum t

    -- PAY by source-specific hyperbolic Dirac Cauchy uniqueness.
    cauchyUniqueOnSameLocalData :
      ∀ datum t →
      originalDataOnCausalHull datum t ≡
        doubleDataOnCausalHull datum t →
      originalEvolutionObserved datum t ≡
        doubledEvolutionObserved datum t

open LocalFiniteTimeDiracCompactDouble public

-- A nontrivial composition of SAME INITIAL DATA, finite support,
-- and Cauchy uniqueness. No new external source theorem is asserted.
finiteTimeLocalSolutionsAgree :
  ∀ {InitialDatum LocalObservation}
  (model : LocalFiniteTimeDiracCompactDouble InitialDatum LocalObservation)
  (datum : InitialDatum) (t : Nat) →
  compactlySupported model datum →
  permittedFiniteTime model t →
  causalHullInsideSmoothDouble model datum t →
  originalEvolutionObserved model datum t ≡
    doubledEvolutionObserved model datum t
finiteTimeLocalSolutionsAgree model datum t support time hull =
  cauchyUniqueOnSameLocalData model datum t
    (finitePropagationAndCollarAgreement model datum t support time hull)

------------------------------------------------------------------------
-- Source / proof / physical promotion firewall.
--
-- Gérard--Stoskopf (2022), DOI 10.1142/S0129055X22500088:
-- general free Dirac Hadamard-state existence on globally hyperbolic
-- spin spacetimes, subject to their exact operator/state assumptions.
-- This EXTERNAL EXISTENCE THEOREM is not proved here, and does NOT
-- select a magnetic-loop Casimir state with negative stress.
--
-- Zahn (2014), DOI 10.1142/S0129055X13300124:
-- local covariant charged Dirac renormalized current/stress.
-- Existence != physical selected state != self-consistent Einstein.
------------------------------------------------------------------------

record NoncompactCauchyDiracSourceBoundary : Set where
  field
    nativeConstructiveSequenceCauchyOwnerExists : Bool
    nativeLorentzianGlobalCausalityOwnerExists : Bool
    nativeAQFTCauchyTimeSliceTargetExists : Bool
    compactDoublingFiniteTimeSourceRootIdentified : Bool

    compactDoubleIsGlobalMagneticReturnGeometry : Bool
    finiteTimeEqualityProvesGlobalHadamardState : Bool
    qftTimeSliceTheoremAlreadyProvedLocally : Bool
    chargedSpinCBundleAndPhysicalStateSelected : Bool
    fullEinsteinMaxwellDiracSaddleSolved : Bool

canonicalNoncompactCauchyBoundary : NoncompactCauchyDiracSourceBoundary
canonicalNoncompactCauchyBoundary = record
  { nativeConstructiveSequenceCauchyOwnerExists = true
  ; nativeLorentzianGlobalCausalityOwnerExists = true
  ; nativeAQFTCauchyTimeSliceTargetExists = true
  ; compactDoublingFiniteTimeSourceRootIdentified = true
  ; compactDoubleIsGlobalMagneticReturnGeometry = false
  ; finiteTimeEqualityProvesGlobalHadamardState = false
  ; qftTimeSliceTheoremAlreadyProvedLocally = false
  ; chargedSpinCBundleAndPhysicalStateSelected = false
  ; fullEinsteinMaxwellDiracSaddleSolved = false
  }

globalStateNotPaid :
  NoncompactCauchyDiracSourceBoundary.finiteTimeEqualityProvesGlobalHadamardState
    canonicalNoncompactCauchyBoundary ≡ false
globalStateNotPaid = refl

physicalEinsteinSaddleNotPaid :
  NoncompactCauchyDiracSourceBoundary.fullEinsteinMaxwellDiracSaddleSolved
    canonicalNoncompactCauchyBoundary ≡ false
physicalEinsteinSaddleNotPaid = refl
