module DASHI.Foundations.ConstrainedFrameEulerSelectorExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.FrameWitnessFibreMDLExact as Frame

------------------------------------------------------------------------
-- The frame selector is a finite constrained variational problem:
--
--     minimise cost(frame)
--     subject to ClosesThreeAt(frame).
--
-- The selected frame is not promoted to universal truth.  This file exposes
-- the actual minimiser, admissibility witness, finite first variation, and the
-- exact stationarity theorem for cost-preserving admissible deformations.
------------------------------------------------------------------------

record FiniteConstrainedMinimum : Set where
  constructor finite-constrained-minimum
  field
    Candidate : Set
    admissible : Candidate → Set
    cost : Candidate → Nat
    selected : Candidate
    selectedAdmissible : admissible selected
    selectedMinimal :
      (candidate : Candidate) →
      admissible candidate →
      cost selected ≤ cost candidate

open FiniteConstrainedMinimum public

frameConstrainedMinimum : FiniteConstrainedMinimum
frameConstrainedMinimum =
  finite-constrained-minimum
    Frame.CandidateFrame
    Frame.ClosesThreeAt
    (λ candidate → Frame.totalFrameCost (Frame.frameCostOf candidate))
    Frame.compactFrame
    Frame.compactClosure
    (λ candidate closure → Frame.compactIsMinimal tt candidate)

record AdmissibleFrameDeformation : Set where
  constructor admissible-frame-deformation
  field
    endpoint : Frame.CandidateFrame
    endpointCloses : Frame.ClosesThreeAt endpoint

open AdmissibleFrameDeformation public

finiteFirstVariation : AdmissibleFrameDeformation → Nat
finiteFirstVariation deformation =
  Frame.totalFrameCost (Frame.frameCostOf (endpoint deformation))
  ∸ Frame.totalFrameCost (Frame.frameCostOf Frame.compactFrame)

selectedFrameFirstVariationIsNonnegative :
  (deformation : AdmissibleFrameDeformation) →
  Frame.totalFrameCost (Frame.frameCostOf Frame.compactFrame)
  ≤ Frame.totalFrameCost (Frame.frameCostOf (endpoint deformation))
selectedFrameFirstVariationIsNonnegative deformation =
  selectedMinimal frameConstrainedMinimum
    (endpoint deformation)
    (endpointCloses deformation)

record CostPreservingAdmissibleDeformation : Set where
  constructor cost-preserving-admissible-deformation
  field
    deformation : AdmissibleFrameDeformation
    costPreserved :
      Frame.totalFrameCost
        (Frame.frameCostOf (endpoint deformation))
      ≡ Frame.totalFrameCost (Frame.frameCostOf Frame.compactFrame)

open CostPreservingAdmissibleDeformation public

finiteEulerStationarity :
  (variation : CostPreservingAdmissibleDeformation) →
  finiteFirstVariation (deformation variation) ≡ 0
finiteEulerStationarity variation
  rewrite costPreserved variation =
  m∸m≡0
    (Frame.totalFrameCost (Frame.frameCostOf Frame.compactFrame))

identityFrameDeformation : CostPreservingAdmissibleDeformation
identityFrameDeformation =
  cost-preserving-admissible-deformation
    (admissible-frame-deformation Frame.compactFrame Frame.compactClosure)
    refl

identityFrameVariationIsStationary :
  finiteFirstVariation (deformation identityFrameDeformation) ≡ 0
identityFrameVariationIsStationary =
  finiteEulerStationarity identityFrameDeformation

selectedFrameStillOnlyLocal : Frame.ClosesThreeAt Frame.compactFrame
selectedFrameStillOnlyLocal = Frame.compactClosure

record ConstrainedSelectorEulerBoundary : Set where
  constructor constrained-selector-euler-boundary
  field
    finiteConstrainedMinimumConstructed : Bool
    finiteConstrainedMinimumConstructedIsTrue :
      finiteConstrainedMinimumConstructed ≡ true
    finiteCostPreservingStationarityProved : Bool
    finiteCostPreservingStationarityProvedIsTrue :
      finiteCostPreservingStationarityProved ≡ true
    localMinimumProvesUniversalTruth : Bool
    localMinimumProvesUniversalTruthIsFalse :
      localMinimumProvesUniversalTruth ≡ false
    continuumDifferentiableFrameManifoldConstructed : Bool
    continuumDifferentiableFrameManifoldConstructedIsFalse :
      continuumDifferentiableFrameManifoldConstructed ≡ false

canonicalConstrainedSelectorEulerBoundary :
  ConstrainedSelectorEulerBoundary
canonicalConstrainedSelectorEulerBoundary =
  constrained-selector-euler-boundary
    true refl true refl false refl false refl
