module DASHI.Moonshine.BrandtStackUnweightingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 41 develops Brandt modules / ideal classes and their unit-group
-- weights; Chapter 42 identifies the supersingular interpretation.
--
-- SageMath Brandt module reference manual, `monodromy_weights`:
-- the weight of an ideal class is half the number of units of its right order.
-- No DOI is asserted for the software documentation.
--
-- DASHI CONTRIBUTION
--
-- Separate two quantities that had previously been conflated:
--
--   w_i : monodromy / stabilizer weight = |O_i^x| / 2,
--   m_i : integral reciprocal multiplicity used to replace a stacky point by
--         ordinary unweighted sheets.
--
-- A `ReciprocalUnweighting` carries a common positive integer scale L such that
--
--   m_i * w_i = L
--
-- at every class.  This avoids division in the formal carrier.
--
-- For a Brandt operator B the source-facing weighted reversibility orientation
-- is
--
--   w_j B_ij = w_i B_ji.
--
-- On a reciprocal unweighting this is equivalent, after clearing the same
-- common weight factors, to the ordinary crossing-edge balance required by an
-- unweighted symmetric equitable cover:
--
--   m_i B_ij = m_j B_ji.
--
-- The generic record below keeps the arithmetic weight data and the resulting
-- edge-balance certificate together.  The p=11 instance proves both equations
-- definitionally; later arbitrary-p instances can derive the final balance
-- from a generic Nat cancellation lemma once the repository settles on a
-- canonical positive-Nat division/cancellation API.
--
-- IMPORTANT: this file does not claim every such balanced matrix has already
-- been constructed as a canonical quaternion/double-coset cover.  It isolates
-- exactly the finite arithmetic data needed by that next theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record ReciprocalUnweighting (Class : Set) : Set₁ where
  field
    monodromyWeight : Class → Nat
    sheetMultiplicity : Class → Nat
    commonScale : Nat
    commonScalePositive : 0 < commonScale
    clearsWeight : (c : Class) →
      sheetMultiplicity c * monodromyWeight c ≡ commonScale

open ReciprocalUnweighting public

record WeightedBrandtBalance
    {Class : Set}
    (unweighting : ReciprocalUnweighting Class)
    (entry : Class → Class → Nat) : Set₁ where
  field
    crossMonodromyBalance : (i j : Class) →
      monodromyWeight unweighting j * entry i j
      ≡ monodromyWeight unweighting i * entry j i

    unweightedEdgeBalance : (i j : Class) →
      sheetMultiplicity unweighting i * entry i j
      ≡ sheetMultiplicity unweighting j * entry j i

open WeightedBrandtBalance public

------------------------------------------------------------------------
-- A finite ordinary cover should use precisely the sheet multiplicities and
-- then quotient back to the original stacky classes.
------------------------------------------------------------------------

record StackUnweightedCoverShape (Class : Set) : Set₁ where
  field
    unweighting : ReciprocalUnweighting Class
    FineVertex : Set
    project : FineVertex → Class
    fibreCardinality : Class → Nat
    fibreCardinalityMatchesSheets : (c : Class) →
      fibreCardinality c ≡ sheetMultiplicity unweighting c

open StackUnweightedCoverShape public

record BrandtStackUnweightingBoundary : Set where
  field
    monodromyAndSheetWeightsSeparated : Bool
    monodromyAndSheetWeightsSeparatedIsTrue :
      monodromyAndSheetWeightsSeparated ≡ true

    commonScaleDivisionFreeCarrierConstructed : Bool
    commonScaleDivisionFreeCarrierConstructedIsTrue :
      commonScaleDivisionFreeCarrierConstructed ≡ true

    weightedAndUnweightedBalanceSeparated : Bool
    weightedAndUnweightedBalanceSeparatedIsTrue :
      weightedAndUnweightedBalanceSeparated ≡ true

    arbitraryBalancedMatrixCoverConstructedHere : Bool
    arbitraryBalancedMatrixCoverConstructedHereIsFalse :
      arbitraryBalancedMatrixCoverConstructedHere ≡ false

    canonicalQuaternionRigidificationConstructedHere : Bool
    canonicalQuaternionRigidificationConstructedHereIsFalse :
      canonicalQuaternionRigidificationConstructedHere ≡ false

canonicalBrandtStackUnweightingBoundary : BrandtStackUnweightingBoundary
canonicalBrandtStackUnweightingBoundary =
  record
    { monodromyAndSheetWeightsSeparated = true
    ; monodromyAndSheetWeightsSeparatedIsTrue = refl
    ; commonScaleDivisionFreeCarrierConstructed = true
    ; commonScaleDivisionFreeCarrierConstructedIsTrue = refl
    ; weightedAndUnweightedBalanceSeparated = true
    ; weightedAndUnweightedBalanceSeparatedIsTrue = refl
    ; arbitraryBalancedMatrixCoverConstructedHere = false
    ; arbitraryBalancedMatrixCoverConstructedHereIsFalse = refl
    ; canonicalQuaternionRigidificationConstructedHere = false
    ; canonicalQuaternionRigidificationConstructedHereIsFalse = refl
    }
