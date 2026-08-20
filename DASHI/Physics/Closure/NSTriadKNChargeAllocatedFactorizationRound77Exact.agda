module DASHI.Physics.Closure.NSTriadKNChargeAllocatedFactorizationRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- ROUND77 / CHARGE ALLOCATION BEFORE CAUCHY
--
-- A final antichain need not be physically disjoint if shared primitive charge
-- is allocated BEFORE Cauchy.  For a source-native factor x*y choose a positive
-- rational allocation scale s and reciprocal r with s*r=1, and replace
--
--      x*y  by  (s*x) * (r*y).
--
-- The signed physical atom is unchanged exactly, while Cauchy sees
--
--      Q_alloc = sum (s*x)^2,
--      W_alloc = sum (r*y)^2.
--
-- Repeated consumers of one primitive x may use scales s_e satisfying
--
--      sum_e s_e^2 <= 1,
--
-- which guarantees that TOTAL allocated left charge does not exceed x^2.
-- The cost of sharing appears exactly as reciprocal growth in W_alloc rather
-- than being hidden in a disjointness/orthogonality assumption.
--
-- The second half of this module lifts that rescaling directly onto the SAME
-- Round62 structured PDE atom list.  It constructs another
-- TriadicFactorizationOverlay indexed by the identical atom carrier, so charge
-- allocation cannot change the PDE remainder it is intended to fund.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay

record AllocationScale : Set where
  constructor allocation-scale
  field
    scale reciprocal : ℚ
    scaleNonnegative : 0ℚ ≤ scale
    reciprocalNonnegative : 0ℚ ≤ reciprocal
    reciprocalExact : scale * reciprocal ≡ 1ℚ

open AllocationScale public

allocatedContribution :
  Effective.FactorizedContribution → AllocationScale →
  Effective.FactorizedContribution
allocatedContribution contribution allocation =
  Effective.factorized-contribution
    (scale allocation * Effective.leftFactor contribution)
    (reciprocal allocation * Effective.rightFactor contribution)

allocatedContributionProductExact :
  ∀ contribution allocation →
  Effective.leftFactor (allocatedContribution contribution allocation)
    * Effective.rightFactor (allocatedContribution contribution allocation)
  ≡ Effective.leftFactor contribution * Effective.rightFactor contribution
allocatedContributionProductExact contribution allocation =
  let
    s = scale allocation
    r = reciprocal allocation
    x = Effective.leftFactor contribution
    y = Effective.rightFactor contribution
  in
  trans
    (solve (s ∷ r ∷ x ∷ y ∷ []))
    (trans
      (cong (_* (x * y)) (reciprocalExact allocation))
      (ℚP.*-identityˡ (x * y)))

record AllocatedContribution : Set where
  constructor allocated-contribution
  field
    source : Effective.FactorizedContribution
    allocation : AllocationScale

open AllocatedContribution public

allocatedFactors : List AllocatedContribution → List Effective.FactorizedContribution
allocatedFactors [] = []
allocatedFactors (entry ∷ rest) =
  allocatedContribution (source entry) (allocation entry)
  ∷ allocatedFactors rest

sourceFactors : List AllocatedContribution → List Effective.FactorizedContribution
sourceFactors [] = []
sourceFactors (entry ∷ rest) = source entry ∷ sourceFactors rest

allocatedSignedSumExact : ∀ entries →
  Effective.factorizedSignedSum (allocatedFactors entries)
  ≡ Effective.factorizedSignedSum (sourceFactors entries)
allocatedSignedSumExact [] = refl
allocatedSignedSumExact (entry ∷ rest) =
  cong₂ _+_
    (allocatedContributionProductExact (source entry) (allocation entry))
    (allocatedSignedSumExact rest)

allocatedCharge : List AllocatedContribution → ℚ
allocatedCharge entries =
  Effective.concentrationCharge (allocatedFactors entries)

allocatedEffectiveComplexity : List AllocatedContribution → ℚ
allocatedEffectiveComplexity entries =
  Effective.effectiveComplexity (allocatedFactors entries)

allocatedCauchy : ∀ entries →
  L2.square (Effective.factorizedSignedSum (sourceFactors entries))
  ≤ allocatedCharge entries * allocatedEffectiveComplexity entries
allocatedCauchy entries =
  subst
    (λ selectedSum →
      L2.square selectedSum
      ≤ allocatedCharge entries * allocatedEffectiveComplexity entries)
    (allocatedSignedSumExact entries)
    (Effective.factorizedCauchy (allocatedFactors entries))

------------------------------------------------------------------------
-- Lift allocation onto the SAME structured overlay.
------------------------------------------------------------------------

data ChargeAllocatedOverlay :
  ∀ {atoms} → Overlay.TriadicFactorizationOverlay atoms → Set where
  allocatedOverlay[] : ChargeAllocatedOverlay Overlay.overlay[]

  allocatedOverlayTriadic :
    ∀ {classified selected compatible value rest left right exact sourceRest} →
    (allocation : AllocationScale) →
    ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay
      (Overlay.overlayTriadic
        {classified = classified}
        {selected = selected}
        {compatible = compatible}
        {value = value}
        {rest = rest}
        left right exact sourceRest)

  allocatedOverlayCom :
    ∀ {output selected compatible value rest sourceRest} →
    ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay
      (Overlay.overlayCom
        {output = output} {selected = selected} {compatible = compatible}
        {value = value} {rest = rest} sourceRest)

  allocatedOverlayTail :
    ∀ {value rest sourceRest} → ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay (Overlay.overlayTail {value = value} {rest = rest} sourceRest)

  allocatedOverlayDuplicateKernel :
    ∀ {value rest sourceRest} → ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay
      (Overlay.overlayDuplicateKernel {value = value} {rest = rest} sourceRest)

  allocatedOverlayCancellingKernel :
    ∀ {left right cancellation rest sourceRest} →
    ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay
      (Overlay.overlayCancellingKernel
        {left = left} {right = right} {cancellation = cancellation}
        {rest = rest} sourceRest)

  allocatedOverlayIndependentKernel :
    ∀ {value rest sourceRest} → ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay
      (Overlay.overlayIndependentKernel {value = value} {rest = rest} sourceRest)

  allocatedOverlayLowerBoundary :
    ∀ {reason value rest sourceRest} → ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay
      (Overlay.overlayLowerBoundary
        {reason = reason} {value = value} {rest = rest} sourceRest)

  allocatedOverlayUpperBoundary :
    ∀ {reason value rest sourceRest} → ChargeAllocatedOverlay sourceRest →
    ChargeAllocatedOverlay
      (Overlay.overlayUpperBoundary
        {reason = reason} {value = value} {rest = rest} sourceRest)

allocateOverlay :
  ∀ {atoms} {sourceOverlay : Overlay.TriadicFactorizationOverlay atoms} →
  ChargeAllocatedOverlay sourceOverlay → Overlay.TriadicFactorizationOverlay atoms
allocateOverlay allocatedOverlay[] = Overlay.overlay[]
allocateOverlay
    (allocatedOverlayTriadic {left = left} {right = right} {exact = exact}
      allocation rest) =
  let
    sourceContribution = Effective.factorized-contribution left right
    allocated = allocatedContribution sourceContribution allocation
    productExact = allocatedContributionProductExact sourceContribution allocation
    allocatedExact = trans exact (sym productExact)
  in
  Overlay.overlayTriadic
    (Effective.leftFactor allocated)
    (Effective.rightFactor allocated)
    allocatedExact
    (allocateOverlay rest)
allocateOverlay (allocatedOverlayCom rest) = Overlay.overlayCom (allocateOverlay rest)
allocateOverlay (allocatedOverlayTail rest) = Overlay.overlayTail (allocateOverlay rest)
allocateOverlay (allocatedOverlayDuplicateKernel rest) =
  Overlay.overlayDuplicateKernel (allocateOverlay rest)
allocateOverlay (allocatedOverlayCancellingKernel rest) =
  Overlay.overlayCancellingKernel (allocateOverlay rest)
allocateOverlay (allocatedOverlayIndependentKernel rest) =
  Overlay.overlayIndependentKernel (allocateOverlay rest)
allocateOverlay (allocatedOverlayLowerBoundary rest) =
  Overlay.overlayLowerBoundary (allocateOverlay rest)
allocateOverlay (allocatedOverlayUpperBoundary rest) =
  Overlay.overlayUpperBoundary (allocateOverlay rest)

allocatedOverlaySignedRemainderUnchanged :
  ∀ {atoms} {sourceOverlay : Overlay.TriadicFactorizationOverlay atoms}
    (allocation : ChargeAllocatedOverlay sourceOverlay) →
  Effective.factorizedSignedSum
    (Overlay.overlayFactors (allocateOverlay allocation))
  ≡ Effective.factorizedSignedSum (Overlay.overlayFactors sourceOverlay)
allocatedOverlaySignedRemainderUnchanged allocatedOverlay[] = refl
allocatedOverlaySignedRemainderUnchanged
    (allocatedOverlayTriadic {left = left} {right = right} allocation rest) =
  cong₂ _+_
    (allocatedContributionProductExact
      (Effective.factorized-contribution left right) allocation)
    (allocatedOverlaySignedRemainderUnchanged rest)
allocatedOverlaySignedRemainderUnchanged (allocatedOverlayCom rest) =
  allocatedOverlaySignedRemainderUnchanged rest
allocatedOverlaySignedRemainderUnchanged (allocatedOverlayTail rest) =
  allocatedOverlaySignedRemainderUnchanged rest
allocatedOverlaySignedRemainderUnchanged (allocatedOverlayDuplicateKernel rest) =
  allocatedOverlaySignedRemainderUnchanged rest
allocatedOverlaySignedRemainderUnchanged (allocatedOverlayCancellingKernel rest) =
  allocatedOverlaySignedRemainderUnchanged rest
allocatedOverlaySignedRemainderUnchanged (allocatedOverlayIndependentKernel rest) =
  allocatedOverlaySignedRemainderUnchanged rest
allocatedOverlaySignedRemainderUnchanged (allocatedOverlayLowerBoundary rest) =
  allocatedOverlaySignedRemainderUnchanged rest
allocatedOverlaySignedRemainderUnchanged (allocatedOverlayUpperBoundary rest) =
  allocatedOverlaySignedRemainderUnchanged rest

------------------------------------------------------------------------
-- Primitive subpartition theorem.
------------------------------------------------------------------------

sumScaleSquares : List AllocationScale → ℚ
sumScaleSquares [] = 0ℚ
sumScaleSquares (allocation ∷ rest) =
  L2.square (scale allocation) + sumScaleSquares rest

sumScaleSquaresNonnegative : ∀ allocations →
  0ℚ ≤ sumScaleSquares allocations
sumScaleSquaresNonnegative [] = ℚP.≤-refl
sumScaleSquaresNonnegative (allocation ∷ rest) =
  L2.addNonnegative
    (L2.squareNonnegative (scale allocation))
    (sumScaleSquaresNonnegative rest)

allocatedPrimitiveCharge : ℚ → List AllocationScale → ℚ
allocatedPrimitiveCharge primitive allocations =
  L2.square primitive * sumScaleSquares allocations

record PrimitiveChargeSubpartition
    (allocations : List AllocationScale) : Set where
  field
    scaleSquaresBelowOne : sumScaleSquares allocations ≤ 1ℚ

open PrimitiveChargeSubpartition public

primitiveSubpartitionFundsAllAllocatedCopies :
  ∀ primitive allocations →
  PrimitiveChargeSubpartition allocations →
  allocatedPrimitiveCharge primitive allocations ≤ L2.square primitive
primitiveSubpartitionFundsAllAllocatedCopies primitive allocations partition =
  let
    primitiveNN = L2.squareNonnegative primitive
    allocationNN = sumScaleSquaresNonnegative allocations
    productBound :
      L2.square primitive * sumScaleSquares allocations
      ≤ L2.square primitive * 1ℚ
    productBound =
      L2.nonnegativeProductMonotone
        primitiveNN allocationNN primitiveNN ℚP.0≤1
        ℚP.≤-refl (scaleSquaresBelowOne partition)
  in
  subst
    (allocatedPrimitiveCharge primitive allocations ≤_)
    (ℚP.*-identityʳ (L2.square primitive))
    productBound

round77DistinctOutputsImplyPhysicalChargeDisjointness : Bool
round77DistinctOutputsImplyPhysicalChargeDisjointness = false

round77ChargeAllocationPreservesEverySourceAtom : Bool
round77ChargeAllocationPreservesEverySourceAtom = true

round77ChargeAllocatedSameObjectOverlayConstructed : Bool
round77ChargeAllocatedSameObjectOverlayConstructed = true

round77AllocatedCauchyConstructed : Bool
round77AllocatedCauchyConstructed = true

round77PrimitiveChargeSubpartitionConstructed : Bool
round77PrimitiveChargeSubpartitionConstructed = true

round77PhysicalFinalAntichainChargeAllocationConstructed : Bool
round77PhysicalFinalAntichainChargeAllocationConstructed = false

round77ChargeAllocatedSameObjectOverlayConstructedIsTrue :
  round77ChargeAllocatedSameObjectOverlayConstructed ≡ true
round77ChargeAllocatedSameObjectOverlayConstructedIsTrue = refl

round77PrimitiveChargeSubpartitionConstructedIsTrue :
  round77PrimitiveChargeSubpartitionConstructed ≡ true
round77PrimitiveChargeSubpartitionConstructedIsTrue = refl
