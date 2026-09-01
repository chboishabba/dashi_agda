module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPairIncidenceRealizationRound343Exact where

------------------------------------------------------------------------
-- ROUND343 / BIDI: INSTANTIATE THE OLD PAIR-INCIDENCE INTERFACE, NOTHING MORE
--
-- R342 closes the only missing finite-list seam:
--
--   Pair  = R330.NestedIncidence
--   pairs = R342.globalNestedIncidences cutoff.
--
-- `NSPairIncidenceKernel` already owns the generic exact finite incidence fold.
-- Therefore, once the physical lane supplies the intended row/column lists,
-- heat-weighted nested contribution, scalar arithmetic and weights, there is
-- no further kernel ontology to invent.  This module is the thin constructor
-- which places those supplied physical semantics into the OLD
-- PairIncidenceData record on the literal global nested carrier.
--
-- In particular this does NOT prove a Schur bound and does NOT claim that an
-- arbitrary physical signed F_s response equals this nonnegative/majorant
-- kernel.  That representation/majorization receipt remains a separate BIDI
-- obligation, exactly as in the old compact-Gamma lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSTriadKNLiteralNestedRowEnumerationRound330Exact as R330
import DASHI.Physics.Closure.NSTriadKNGlobalNestedIncidenceEnumerationRound342Exact as R342

record NestedFsIncidenceSemantics
    (Row Col Scalar : Set) : Set₁ where
  field
    rows : List Row
    columns : List Col

    zero : Scalar
    add : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

    -- This is the ONLY carrier-specific coefficient requested by R341/R342.
    -- The physical producer may make it zero off the intended row/column
    -- selectors and equal to the heat-weighted nested majorant on support.
    heatWeightedPairContribution :
      R330.NestedIncidence → Row → Col → Scalar

    rowWeight : Row → Scalar
    colWeight : Col → Scalar

open NestedFsIncidenceSemantics public

nestedFsPairIncidenceData :
  ∀ {Row Col Scalar : Set} →
  Nat →
  NestedFsIncidenceSemantics Row Col Scalar →
  PairKernel.PairIncidenceData R330.NestedIncidence Row Col Scalar
nestedFsPairIncidenceData cutoff S = record
  { pairs = R342.globalNestedIncidences cutoff
  ; rows = rows S
  ; columns = columns S
  ; zero = zero S
  ; add = add S
  ; multiply = multiply S
  ; _≤_ = _≤_ S
  ; pairContribution = heatWeightedPairContribution S
  ; rowWeight = rowWeight S
  ; colWeight = colWeight S
  }

nestedFsPairsAreExactlyR342GlobalNestedIncidences :
  ∀ {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : NestedFsIncidenceSemantics Row Col Scalar) →
  PairKernel.pairs (nestedFsPairIncidenceData cutoff S)
  ≡ R342.globalNestedIncidences cutoff
nestedFsPairsAreExactlyR342GlobalNestedIncidences cutoff S = refl

nestedFsContributionIsExactlySuppliedPhysicalContribution :
  ∀ {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : NestedFsIncidenceSemantics Row Col Scalar)
    (pair : R330.NestedIncidence)
    (row : Row)
    (col : Col) →
  PairKernel.pairContribution (nestedFsPairIncidenceData cutoff S) pair row col
  ≡ heatWeightedPairContribution S pair row col
nestedFsContributionIsExactlySuppliedPhysicalContribution cutoff S pair row col = refl

round343OldPairIncidenceInterfaceReused : Bool
round343OldPairIncidenceInterfaceReused = true

round343GlobalNestedPairListReusedExactly : Bool
round343GlobalNestedPairListReusedExactly = true

round343NoSecondNestedKernelOntology : Bool
round343NoSecondNestedKernelOntology = true

-- Conditional closure: once the physical selector/coefficient semantics are
-- supplied, constructing the exact old PairIncidenceData is finished.
round343PairIncidenceRealizationConstructorClosed : Bool
round343PairIncidenceRealizationConstructorClosed = true

-- Still separate by design.
round343PhysicalResponseMajorizationClosed : Bool
round343PhysicalResponseMajorizationClosed = false

round343WeightedSchurCertificateClosed : Bool
round343WeightedSchurCertificateClosed = false

round343PackageAClosed : Bool
round343PackageAClosed = false

round343ClayPromotion : Bool
round343ClayPromotion = false

round343PairIncidenceRealizationConstructorClosedIsTrue :
  round343PairIncidenceRealizationConstructorClosed ≡ true
round343PairIncidenceRealizationConstructorClosedIsTrue = refl

round343PackageAClosedIsFalse : round343PackageAClosed ≡ false
round343PackageAClosedIsFalse = refl

round343ClayPromotionIsFalse : round343ClayPromotion ≡ false
round343ClayPromotionIsFalse = refl
