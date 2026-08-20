module DASHI.Physics.Closure.NSTriadKNAllocatedBranchingConvexityNoGoRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite weighted-average/Cauchy arithmetic; DOI not applicable.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
-- Uses: candidate physical sectors only.  The theorem below says precisely why
-- branching multiplicity by itself cannot be promoted into deterministic gain.
--
-- ROUND77 / SHARED-CHARGE CONVEXITY NO-GO
--
-- Suppose many descendant/event candidates reuse ONE primitive physical charge.
-- Charge allocation gives each consumer a squared fraction
--
--      theta_i = s_i^2,       sum_i theta_i <= 1.
--
-- Let g_i be that child's RAW propagation efficiency after all non-allocation
-- frame costs have been included.  Its funded contribution is theta_i g_i.
-- If every child is individually below the parent threshold P,
--
--      0 <= g_i <= P,
--
-- then exactly
--
--      sum_i theta_i g_i <= P sum_i theta_i <= P.
--
-- Thus formal branching cannot manufacture positive weighted excess from many
-- subcritical children sharing the same primitive budget.  A successful D2
-- proof must exhibit at least one of:
--
--   * a genuinely supercritical raw child efficiency;
--   * physically distinct primitive charge sectors that may be funded
--     independently;
--   * a sharper signed/cancellation mechanism changing the effective frame
--     cost before this convexity bound applies.
--
-- Waleffe's helical classes can guide the search for the first/third mechanisms,
-- but their statistical transfer interpretation is not itself such a proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNChargeAllocatedFactorizationRound77Exact as Allocation

record AllocatedGain (parentThreshold : ℚ) : Set where
  constructor allocated-gain
  field
    allocation : Allocation.AllocationScale
    rawGain : ℚ
    rawGainNonnegative : 0ℚ ≤ rawGain
    rawGainBelowParent : rawGain ≤ parentThreshold

open AllocatedGain public

allocatedGainValue : ∀ {parentThreshold} → AllocatedGain parentThreshold → ℚ
allocatedGainValue entry =
  L2.square (Allocation.scale (allocation entry)) * rawGain entry

sumAllocatedGain : ∀ {parentThreshold} → List (AllocatedGain parentThreshold) → ℚ
sumAllocatedGain [] = 0ℚ
sumAllocatedGain (entry ∷ rest) =
  allocatedGainValue entry + sumAllocatedGain rest

gainAllocations : ∀ {parentThreshold} →
  List (AllocatedGain parentThreshold) → List Allocation.AllocationScale
gainAllocations [] = []
gainAllocations (entry ∷ rest) = allocation entry ∷ gainAllocations rest

allocatedGainBelowAllocatedParent :
  ∀ {parentThreshold} (entry : AllocatedGain parentThreshold) →
  allocatedGainValue entry
  ≤ L2.square (Allocation.scale (allocation entry)) * parentThreshold
allocatedGainBelowAllocatedParent {parentThreshold} entry =
  L2.nonnegativeProductMonotone
    (L2.squareNonnegative (Allocation.scale (allocation entry)))
    (rawGainNonnegative entry)
    (L2.squareNonnegative (Allocation.scale (allocation entry)))
    (ℚP.≤-trans (rawGainNonnegative entry) (rawGainBelowParent entry))
    ℚP.≤-refl
    (rawGainBelowParent entry)

sumAllocatedGainBelowParentTimesScaleMass :
  ∀ {parentThreshold} →
  0ℚ ≤ parentThreshold →
  (entries : List (AllocatedGain parentThreshold)) →
  sumAllocatedGain entries
  ≤ parentThreshold * Allocation.sumScaleSquares (gainAllocations entries)
sumAllocatedGainBelowParentTimesScaleMass parentNN [] =
  subst (0ℚ ≤_) (sym (ℚP.*-zeroʳ _)) ℚP.≤-refl
sumAllocatedGainBelowParentTimesScaleMass {parentThreshold} parentNN (entry ∷ rest) =
  let
    headBound = allocatedGainBelowAllocatedParent entry
    tailBound = sumAllocatedGainBelowParentTimesScaleMass parentNN rest
    sumBound :
      allocatedGainValue entry + sumAllocatedGain rest
      ≤
      L2.square (Allocation.scale (allocation entry)) * parentThreshold
      + parentThreshold * Allocation.sumScaleSquares (gainAllocations rest)
    sumBound = ℚP.+-mono-≤ headBound tailBound
    rearrange :
      L2.square (Allocation.scale (allocation entry)) * parentThreshold
      + parentThreshold * Allocation.sumScaleSquares (gainAllocations rest)
      ≡
      parentThreshold
      * (L2.square (Allocation.scale (allocation entry))
        + Allocation.sumScaleSquares (gainAllocations rest))
    rearrange =
      solve
        ( parentThreshold
        ∷ Allocation.scale (allocation entry)
        ∷ Allocation.sumScaleSquares (gainAllocations rest)
        ∷ [])
  in
  subst
    (sumAllocatedGain (entry ∷ rest) ≤_)
    rearrange
    sumBound

sharedChargeSubpartitionPreventsSupercriticality :
  ∀ {parentThreshold}
    (parentNN : 0ℚ ≤ parentThreshold)
    (entries : List (AllocatedGain parentThreshold)) →
  Allocation.PrimitiveChargeSubpartition (gainAllocations entries) →
  sumAllocatedGain entries ≤ parentThreshold
sharedChargeSubpartitionPreventsSupercriticality
    {parentThreshold} parentNN entries partition =
  let
    scaleMassNN = Allocation.sumScaleSquaresNonnegative (gainAllocations entries)
    first = sumAllocatedGainBelowParentTimesScaleMass parentNN entries
    scaled :
      parentThreshold * Allocation.sumScaleSquares (gainAllocations entries)
      ≤ parentThreshold * 1ℚ
    scaled =
      L2.nonnegativeProductMonotone
        parentNN scaleMassNN parentNN ℚP.0≤1
        ℚP.≤-refl (Allocation.scaleSquaresBelowOne partition)
    collapse : parentThreshold * 1ℚ ≡ parentThreshold
    collapse = ℚP.*-identityʳ parentThreshold
  in
  ℚP.≤-trans first
    (subst
      (parentThreshold * Allocation.sumScaleSquares (gainAllocations entries) ≤_)
      collapse
      scaled)

round77SharedChargeBranchingCanManufactureSupercriticality : Bool
round77SharedChargeBranchingCanManufactureSupercriticality = false

round77SharedChargeSubcriticalChildrenStaySubcritical : Bool
round77SharedChargeSubcriticalChildrenStaySubcritical = true

round77D2NeedsRawSupercriticalEfficiencyOrDistinctChargeSectors : Bool
round77D2NeedsRawSupercriticalEfficiencyOrDistinctChargeSectors = true

round77WaleffeClassMembershipAloneDischargesD2 : Bool
round77WaleffeClassMembershipAloneDischargesD2 = false

round77SharedChargeSubcriticalChildrenStaySubcriticalIsTrue :
  round77SharedChargeSubcriticalChildrenStaySubcritical ≡ true
round77SharedChargeSubcriticalChildrenStaySubcriticalIsTrue = refl
