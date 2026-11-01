module DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- ROUND72 / SAME-OBJECT FACTORIZATION OVERLAY
--
-- The Round62 LocalizedPDEAtom list remains the sole PDE source language.
-- Weighted/effective-complexity Cauchy must therefore NOT introduce a parallel
-- atom carrier.  Instead this file defines an overlay indexed by that exact
-- list.  Every TRIADIC physicalAtom of value a carries factors x,y with
--
--      a = x*y.
--
-- All Com/tail/kernel/boundary entries are traversed but contribute no factor.
-- Extracting the factor list is proved to reproduce exactly the Round71
-- triadic signed sum.  Consequently finite factorized Cauchy applies to the
-- SAME structured remainder:
--
--   (triadicSignedSum atoms)^2
--      <= overlayCharge * overlayEffectiveComplexity.
--
-- The unit overlay x=a,y=1 is always constructible and recovers the old raw
-- cardinality route.  The genuinely new physical theorem is to construct a
-- better overlay from the localized trajectory where overlayCharge is charged
-- to the physical budget and overlayEffectiveComplexity is uniformly/slowly
-- controlled by low-leg energy, dominant-hat self-mass, dissipation or Gram
-- geometry.  That theorem is intentionally not fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

data TriadicFactorizationOverlay :
    List Structured.LocalizedPDEAtom → Set where
  overlay[] : TriadicFactorizationOverlay []

  overlayTriadic :
    ∀ {classified selected compatible value rest}
      (left right : ℚ) →
    value ≡ left * right →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay
      (Structured.physicalAtom (Support.triadicSource classified)
        selected compatible value ∷ rest)

  overlayCom :
    ∀ {output selected compatible value rest} →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay
      (Structured.physicalAtom (Support.differentiatedCommutator output)
        selected compatible value ∷ rest)

  overlayTail : ∀ {value rest} →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay (Structured.tailAtom value ∷ rest)

  overlayDuplicateKernel : ∀ {value rest} →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay (Structured.duplicateKernelAtom value ∷ rest)

  overlayCancellingKernel : ∀ {left right cancellation rest} →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay
      (Structured.cancellingKernelPair left right cancellation ∷ rest)

  overlayIndependentKernel : ∀ {value rest} →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay (Structured.independentKernelAtom value ∷ rest)

  overlayLowerBoundary : ∀ {reason value rest} →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay
      (Structured.lowerBoundaryAtom reason value ∷ rest)

  overlayUpperBoundary : ∀ {reason value rest} →
    TriadicFactorizationOverlay rest →
    TriadicFactorizationOverlay
      (Structured.upperBoundaryAtom reason value ∷ rest)

overlayFactors :
  ∀ {atoms} → TriadicFactorizationOverlay atoms →
  List Effective.FactorizedContribution
overlayFactors overlay[] = []
overlayFactors (overlayTriadic left right exact rest) =
  Effective.factorized-contribution left right ∷ overlayFactors rest
overlayFactors (overlayCom rest) = overlayFactors rest
overlayFactors (overlayTail rest) = overlayFactors rest
overlayFactors (overlayDuplicateKernel rest) = overlayFactors rest
overlayFactors (overlayCancellingKernel rest) = overlayFactors rest
overlayFactors (overlayIndependentKernel rest) = overlayFactors rest
overlayFactors (overlayLowerBoundary rest) = overlayFactors rest
overlayFactors (overlayUpperBoundary rest) = overlayFactors rest

overlaySignedSumExact :
  ∀ {atoms} (overlay : TriadicFactorizationOverlay atoms) →
  Effective.factorizedSignedSum (overlayFactors overlay)
  ≡ R71.triadicSignedSum atoms
overlaySignedSumExact overlay[] = refl
overlaySignedSumExact
    (overlayTriadic {value = value} left right exact rest) =
  trans
    (cong
      (λ head → head + Effective.factorizedSignedSum (overlayFactors rest))
      (sym exact))
    (cong (value +_) (overlaySignedSumExact rest))
overlaySignedSumExact (overlayCom rest) = overlaySignedSumExact rest
overlaySignedSumExact (overlayTail rest) = overlaySignedSumExact rest
overlaySignedSumExact (overlayDuplicateKernel rest) = overlaySignedSumExact rest
overlaySignedSumExact (overlayCancellingKernel rest) = overlaySignedSumExact rest
overlaySignedSumExact (overlayIndependentKernel rest) = overlaySignedSumExact rest
overlaySignedSumExact (overlayLowerBoundary rest) = overlaySignedSumExact rest
overlaySignedSumExact (overlayUpperBoundary rest) = overlaySignedSumExact rest

overlayCharge : ∀ {atoms} → TriadicFactorizationOverlay atoms → ℚ
overlayCharge overlay = Effective.concentrationCharge (overlayFactors overlay)

overlayEffectiveComplexity :
  ∀ {atoms} → TriadicFactorizationOverlay atoms → ℚ
overlayEffectiveComplexity overlay =
  Effective.effectiveComplexity (overlayFactors overlay)

overlayCauchy :
  ∀ {atoms} (overlay : TriadicFactorizationOverlay atoms) →
  L2.square (R71.triadicSignedSum atoms)
  ≤ overlayCharge overlay * overlayEffectiveComplexity overlay
overlayCauchy overlay =
  subst
    (λ signed → L2.square signed
      ≤ overlayCharge overlay * overlayEffectiveComplexity overlay)
    (overlaySignedSumExact overlay)
    (Effective.factorizedCauchy (overlayFactors overlay))

unitOverlay :
  (atoms : List Structured.LocalizedPDEAtom) →
  TriadicFactorizationOverlay atoms
unitOverlay [] = overlay[]
unitOverlay
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest) =
  overlayTriadic value 1ℚ
    (sym (ℚP.*-identityʳ value))
    (unitOverlay rest)
unitOverlay
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = overlayCom (unitOverlay rest)
unitOverlay (Structured.tailAtom value ∷ rest) = overlayTail (unitOverlay rest)
unitOverlay (Structured.duplicateKernelAtom value ∷ rest) =
  overlayDuplicateKernel (unitOverlay rest)
unitOverlay (Structured.cancellingKernelPair left right cancellation ∷ rest) =
  overlayCancellingKernel (unitOverlay rest)
unitOverlay (Structured.independentKernelAtom value ∷ rest) =
  overlayIndependentKernel (unitOverlay rest)
unitOverlay (Structured.lowerBoundaryAtom reason value ∷ rest) =
  overlayLowerBoundary (unitOverlay rest)
unitOverlay (Structured.upperBoundaryAtom reason value ∷ rest) =
  overlayUpperBoundary (unitOverlay rest)

round72SameObjectFactorizationOverlayConstructed : Bool
round72SameObjectFactorizationOverlayConstructed = true

round72UnitOverlayRecoversRawCardinalityRoute : Bool
round72UnitOverlayRecoversRawCardinalityRoute = true

round72PhysicalEnergyControlledOverlayConstructed : Bool
round72PhysicalEnergyControlledOverlayConstructed = false

round72SameObjectFactorizationOverlayConstructedIsTrue :
  round72SameObjectFactorizationOverlayConstructed ≡ true
round72SameObjectFactorizationOverlayConstructedIsTrue = refl

round72PhysicalEnergyControlledOverlayConstructedIsFalse :
  round72PhysicalEnergyControlledOverlayConstructed ≡ false
round72PhysicalEnergyControlledOverlayConstructedIsFalse = refl
