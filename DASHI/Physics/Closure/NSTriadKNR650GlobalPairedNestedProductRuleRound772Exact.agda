{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalPairedNestedProductRuleRound772Exact where

------------------------------------------------------------------------
-- ROUND772 / COMPLETE SWAP-PAIRED NESTED ORBIT IS THREE COPIES OF THE
--            PAIRED PRODUCT-RULE BASE ROW
--
-- R763 gives pointwise
--
--   N(beta) + N(swap beta)
--     = PairedBase(beta)
--       + 2 Row(pLeg beta)
--       + 2 Row(qLeg beta).
--
-- Pointwise, the two cyclic rows remain.  On the COMPLETE physical cutoff
-- enumeration, however, R38 proves pEnergyLeg and qEnergyLeg are exact
-- permutations.  Hence each cyclic row fold is exactly the base-row fold.
--
-- Also R763 gives
--
--   PairedBase(beta) = Row(beta) + Row(swap beta),
--
-- and swap is itself an exact enumeration permutation.  Therefore
--
--   sum PairedBase = 2 sum Row.
--
-- Combining these facts division-free:
--
--   sum [N(beta)+N(swap beta)]
--     = 3 * sum PairedBase(beta).
--
-- This removes R769's two cyclic leftovers GLOBALLY.  It does NOT assert a
-- classwise factor-three identity: pEnergyLeg/qEnergyLeg may change the R25
-- Bony class, so classwise reindexing requires additional structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedNestedOrbitNormalFormRound763Exact as R763

F : C3.RealField _
F = Rational.rationalRealField

three : ℚ
three = 3

module GlobalPairedNested
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module P =
    R763.PairedNestedOrbit
      physicalSystem S L H velocityTransverse

  cutoff : Nat
  cutoff = P.N.Nested.Base.cutoff

  items : List Physical.PhysicalTriadIncidence
  items = Physical.physicalTriadEnumeration cutoff

  baseRow : Physical.PhysicalTriadIncidence → ℚ
  baseRow = P.N.maskedNestedOuterRow

  pairedBaseRow : Physical.PhysicalTriadIncidence → ℚ
  pairedBaseRow = P.pairedMaskedBaseRow

  pairedOrbitCell : Physical.PhysicalTriadIncidence → ℚ
  pairedOrbitCell beta =
    P.N.nestedTriadOrbitResidue beta
      + P.N.nestedTriadOrbitResidue (Symmetry.swapTriad beta)

  foldCong :
    (left right : Physical.PhysicalTriadIncidence → ℚ) →
    ((beta : Physical.PhysicalTriadIncidence) → left beta ≡ right beta) →
    (xs : List Physical.PhysicalTriadIncidence) →
    R38.foldPower left xs ≡ R38.foldPower right xs
  foldCong left right pointwise [] = refl
  foldCong left right pointwise (beta ∷ rest) =
    cong₂ _+_
      (pointwise beta)
      (foldCong left right pointwise rest)

  foldAdd :
    (left right : Physical.PhysicalTriadIncidence → ℚ) →
    (xs : List Physical.PhysicalTriadIncidence) →
    R38.foldPower (λ beta → left beta + right beta) xs
    ≡ R38.foldPower left xs + R38.foldPower right xs
  foldAdd left right [] = solve []
  foldAdd left right (beta ∷ rest) =
    trans
      (cong
        (left beta + right beta +_)
        (foldAdd left right rest))
      (solve
        ( left beta
        ∷ right beta
        ∷ R38.foldPower left rest
        ∷ R38.foldPower right rest
        ∷ []))

  foldScaledAdd3 :
    (a b c : Physical.PhysicalTriadIncidence → ℚ) →
    (xs : List Physical.PhysicalTriadIncidence) →
    R38.foldPower
      (λ beta →
        a beta + R763.two * b beta + R763.two * c beta)
      xs
    ≡
    R38.foldPower a xs
      + R763.two * R38.foldPower b xs
      + R763.two * R38.foldPower c xs
  foldScaledAdd3 a b c [] = solve []
  foldScaledAdd3 a b c (beta ∷ rest) =
    trans
      (cong
        (a beta + R763.two * b beta + R763.two * c beta +_)
        (foldScaledAdd3 a b c rest))
      (solve
        ( a beta
        ∷ b beta
        ∷ c beta
        ∷ R38.foldPower a rest
        ∷ R38.foldPower b rest
        ∷ R38.foldPower c rest
        ∷ R763.two
        ∷ []))

  foldAfterReindex :
    (value : Physical.PhysicalTriadIncidence → ℚ) →
    (reindex :
      Physical.PhysicalTriadIncidence →
      Physical.PhysicalTriadIncidence) →
    (permutation :
      Agda.Builtin.List.map reindex items
        Data.List.Relation.Binary.Permutation.Propositional.↭ items) →
    R38.foldPower (λ beta → value (reindex beta)) items
    ≡ R38.foldPower value items
  foldAfterReindex value reindex permutation =
    trans
      (sym (R38.foldMap value reindex items))
      (R38.foldPermutationInvariant value permutation)

  pRowFoldIsBaseRowFold :
    R38.foldPower (λ beta → baseRow (Orbit.pEnergyLeg beta)) items
    ≡ R38.foldPower baseRow items
  pRowFoldIsBaseRowFold =
    foldAfterReindex
      baseRow Orbit.pEnergyLeg
      (R38.pEnergyLegEnumerationPermutation cutoff)

  qRowFoldIsBaseRowFold :
    R38.foldPower (λ beta → baseRow (Orbit.qEnergyLeg beta)) items
    ≡ R38.foldPower baseRow items
  qRowFoldIsBaseRowFold =
    foldAfterReindex
      baseRow Orbit.qEnergyLeg
      (R38.qEnergyLegEnumerationPermutation cutoff)

  swapRowFoldIsBaseRowFold :
    R38.foldPower (λ beta → baseRow (Symmetry.swapTriad beta)) items
    ≡ R38.foldPower baseRow items
  swapRowFoldIsBaseRowFold =
    foldAfterReindex
      baseRow Symmetry.swapTriad
      (R38.swapTriadEnumerationPermutation cutoff)

  pairedBaseFoldIsTwiceBaseRowFold :
    R38.foldPower pairedBaseRow items
    ≡ R763.two * R38.foldPower baseRow items
  pairedBaseFoldIsTwiceBaseRowFold =
    let
      base = R38.foldPower baseRow items
      swapped =
        R38.foldPower
          (λ beta → baseRow (Symmetry.swapTriad beta))
          items

      expose :
        R38.foldPower pairedBaseRow items
        ≡ base + swapped
      expose =
        trans
          (foldCong
            pairedBaseRow
            (λ beta →
              baseRow beta + baseRow (Symmetry.swapTriad beta))
            (λ beta → sym (P.maskedNestedOuterRowSwapPair beta))
            items)
          (foldAdd
            baseRow
            (λ beta → baseRow (Symmetry.swapTriad beta))
            items)
    in
    trans expose
      (trans
        (cong (base +_) swapRowFoldIsBaseRowFold)
        (solve (base ∷ R763.two ∷ [])))

  pairedOrbitFoldDecomposition :
    R38.foldPower pairedOrbitCell items
    ≡
    R38.foldPower pairedBaseRow items
      + R763.two *
          R38.foldPower
            (λ beta → baseRow (Orbit.pEnergyLeg beta)) items
      + R763.two *
          R38.foldPower
            (λ beta → baseRow (Orbit.qEnergyLeg beta)) items
  pairedOrbitFoldDecomposition =
    trans
      (foldCong
        pairedOrbitCell
        (λ beta →
          pairedBaseRow beta
            + R763.two * baseRow (Orbit.pEnergyLeg beta)
            + R763.two * baseRow (Orbit.qEnergyLeg beta))
        P.nestedOrbitSwapPairNormalForm
        items)
      (foldScaledAdd3
        pairedBaseRow
        (λ beta → baseRow (Orbit.pEnergyLeg beta))
        (λ beta → baseRow (Orbit.qEnergyLeg beta))
        items)

  completePairedNestedOrbitIsThreePairedBaseRows :
    R38.foldPower pairedOrbitCell items
    ≡ three * R38.foldPower pairedBaseRow items
  completePairedNestedOrbitIsThreePairedBaseRows =
    let
      paired = R38.foldPower pairedBaseRow items
      base = R38.foldPower baseRow items

      cyclicCollapsed :
        R38.foldPower pairedOrbitCell items
        ≡ paired + R763.two * base + R763.two * base
      cyclicCollapsed =
        trans
          pairedOrbitFoldDecomposition
          (trans
            (cong
              (λ selected →
                paired + R763.two * selected
                  + R763.two *
                      R38.foldPower
                        (λ beta → baseRow (Orbit.qEnergyLeg beta)) items)
              pRowFoldIsBaseRowFold)
            (cong
              (λ selected →
                paired + R763.two * base + R763.two * selected)
              qRowFoldIsBaseRowFold))
    in
    trans cyclicCollapsed
      (trans
        (cong
          (λ selected →
            selected + R763.two * base + R763.two * base)
          pairedBaseFoldIsTwiceBaseRowFold)
        (trans
          (solve (base ∷ R763.two ∷ three ∷ []))
          (cong
            (three *_)
            (sym pairedBaseFoldIsTwiceBaseRowFold))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round772CompletePairedNestedOrbitIsThreePairedBaseRows : Bool
round772CompletePairedNestedOrbitIsThreePairedBaseRows = true

round772CyclicNestedRowsRemainGloballyIndependent : Bool
round772CyclicNestedRowsRemainGloballyIndependent = false

round772UsesOnlyExactEnumerationPermutations : Bool
round772UsesOnlyExactEnumerationPermutations = true

round772ClasswiseFactorThreeClaimed : Bool
round772ClasswiseFactorThreeClaimed = false

round772IntroducesEstimate : Bool
round772IntroducesEstimate = false

round772ClayPromotion : Bool
round772ClayPromotion = false

round772CompletePairedNestedOrbitIsThreePairedBaseRowsIsTrue :
  round772CompletePairedNestedOrbitIsThreePairedBaseRows ≡ true
round772CompletePairedNestedOrbitIsThreePairedBaseRowsIsTrue = refl

round772CyclicNestedRowsRemainGloballyIndependentIsFalse :
  round772CyclicNestedRowsRemainGloballyIndependent ≡ false
round772CyclicNestedRowsRemainGloballyIndependentIsFalse = refl

round772UsesOnlyExactEnumerationPermutationsIsTrue :
  round772UsesOnlyExactEnumerationPermutations ≡ true
round772UsesOnlyExactEnumerationPermutationsIsTrue = refl

round772ClasswiseFactorThreeClaimedIsFalse :
  round772ClasswiseFactorThreeClaimed ≡ false
round772ClasswiseFactorThreeClaimedIsFalse = refl

round772IntroducesEstimateIsFalse :
  round772IntroducesEstimate ≡ false
round772IntroducesEstimateIsFalse = refl

round772ClayPromotionIsFalse :
  round772ClayPromotion ≡ false
round772ClayPromotionIsFalse = refl
