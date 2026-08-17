module DASHI.Physics.Closure.NSTriadKNPhysicalFactorizationAuthorityRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / FACTORIZATION PROVENANCE AUTHORITY
--
-- Round72 proved a rescaling no-go: the scalar product a=x*y does not choose a
-- useful pair (x,y).  This file prevents that freedom from silently re-entering
-- the proof.  A physical factorization is indexed by the SAME structured atom
-- list and each triadic factor is required to equal source-native left/right
-- coordinates supplied by one declared authority.
--
-- This is a provenance theorem, not an optimization theorem.  It says that once
-- the source-native factor coordinates are fixed, the overlay is unique in its
-- factor values.  Arbitrary rescalings preserve the product but do not preserve
-- this authority unless they preserve both source coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective

record PhysicalTriadicFactorSource : Set where
  field
    sourceLeft : Structured.LocalizedPDEAtom → ℚ
    sourceRight : Structured.LocalizedPDEAtom → ℚ
    sourceTriadicProductExact :
      ∀ {classified selected compatible value} →
      let atom = Structured.physicalAtom
            (Support.triadicSource classified)
            selected compatible value
      in value ≡ sourceLeft atom * sourceRight atom

open PhysicalTriadicFactorSource public

data SourceNativeOverlay
    (source : PhysicalTriadicFactorSource) :
    (atoms : List Structured.LocalizedPDEAtom) →
    Overlay.TriadicFactorizationOverlay atoms → Set where
  source[] : SourceNativeOverlay source [] Overlay.overlay[]

  sourceTriadic :
    ∀ {classified selected compatible value rest restOverlay}
      (restNative : SourceNativeOverlay source rest restOverlay) →
    SourceNativeOverlay source
      (Structured.physicalAtom (Support.triadicSource classified)
        selected compatible value ∷ rest)
      (Overlay.overlayTriadic
        (sourceLeft source
          (Structured.physicalAtom (Support.triadicSource classified)
            selected compatible value))
        (sourceRight source
          (Structured.physicalAtom (Support.triadicSource classified)
            selected compatible value))
        (sourceTriadicProductExact source)
        restOverlay)

  sourceCom :
    ∀ {output selected compatible value rest restOverlay} →
    SourceNativeOverlay source rest restOverlay →
    SourceNativeOverlay source
      (Structured.physicalAtom (Support.differentiatedCommutator output)
        selected compatible value ∷ rest)
      (Overlay.overlayCom restOverlay)

  sourceTail : ∀ {value rest restOverlay} →
    SourceNativeOverlay source rest restOverlay →
    SourceNativeOverlay source (Structured.tailAtom value ∷ rest)
      (Overlay.overlayTail restOverlay)

  sourceDuplicateKernel : ∀ {value rest restOverlay} →
    SourceNativeOverlay source rest restOverlay →
    SourceNativeOverlay source (Structured.duplicateKernelAtom value ∷ rest)
      (Overlay.overlayDuplicateKernel restOverlay)

  sourceCancellingKernel : ∀ {left right cancellation rest restOverlay} →
    SourceNativeOverlay source rest restOverlay →
    SourceNativeOverlay source
      (Structured.cancellingKernelPair left right cancellation ∷ rest)
      (Overlay.overlayCancellingKernel restOverlay)

  sourceIndependentKernel : ∀ {value rest restOverlay} →
    SourceNativeOverlay source rest restOverlay →
    SourceNativeOverlay source (Structured.independentKernelAtom value ∷ rest)
      (Overlay.overlayIndependentKernel restOverlay)

  sourceLowerBoundary : ∀ {reason value rest restOverlay} →
    SourceNativeOverlay source rest restOverlay →
    SourceNativeOverlay source
      (Structured.lowerBoundaryAtom reason value ∷ rest)
      (Overlay.overlayLowerBoundary restOverlay)

  sourceUpperBoundary : ∀ {reason value rest restOverlay} →
    SourceNativeOverlay source rest restOverlay →
    SourceNativeOverlay source
      (Structured.upperBoundaryAtom reason value ∷ rest)
      (Overlay.overlayUpperBoundary restOverlay)

sourceFactorList :
  (source : PhysicalTriadicFactorSource) →
  (atoms : List Structured.LocalizedPDEAtom) →
  List Effective.FactorizedContribution
sourceFactorList source [] = []
sourceFactorList source
    (atom@(Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value) ∷ rest) =
  Effective.factorized-contribution
    (sourceLeft source atom) (sourceRight source atom)
  ∷ sourceFactorList source rest
sourceFactorList source
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = sourceFactorList source rest
sourceFactorList source (Structured.tailAtom value ∷ rest) = sourceFactorList source rest
sourceFactorList source (Structured.duplicateKernelAtom value ∷ rest) = sourceFactorList source rest
sourceFactorList source (Structured.cancellingKernelPair l r c ∷ rest) = sourceFactorList source rest
sourceFactorList source (Structured.independentKernelAtom value ∷ rest) = sourceFactorList source rest
sourceFactorList source (Structured.lowerBoundaryAtom reason value ∷ rest) = sourceFactorList source rest
sourceFactorList source (Structured.upperBoundaryAtom reason value ∷ rest) = sourceFactorList source rest

round73FactorizationAuthorityCarrierConstructed : Bool
round73FactorizationAuthorityCarrierConstructed = true

round73LiteralVelocityGramFactorSourceConstructed : Bool
round73LiteralVelocityGramFactorSourceConstructed = false

round73FactorizationAuthorityCarrierConstructedIsTrue :
  round73FactorizationAuthorityCarrierConstructed ≡ true
round73FactorizationAuthorityCarrierConstructedIsTrue = refl

round73LiteralVelocityGramFactorSourceConstructedIsFalse :
  round73LiteralVelocityGramFactorSourceConstructed ≡ false
round73LiteralVelocityGramFactorSourceConstructedIsFalse = refl
