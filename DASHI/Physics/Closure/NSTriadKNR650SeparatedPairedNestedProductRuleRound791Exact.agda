{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedPairedNestedProductRuleRound791Exact where

------------------------------------------------------------------------
-- ROUND791 / LOCALIZE R772 TO THE FULLY-SEPARATED ORBIT FAMILY
--
-- R772 could collapse the paired nested orbit only on the complete physical
-- enumeration because pEnergyLeg/qEnergyLeg changed R25 classes.
--
-- R787 and R790 now prove something sharper for the modern orbit-profile mask:
--
--   ccTouched(q beta) = ccTouched(beta)
--   ccTouched(p beta) = ccTouched(beta),
--
-- while R781 already proves swap invariance.  Therefore the old R772
-- reindexing can be repeated inside the fully-separated family without
-- discarding the LH/HL/HH orbit structure.
--
-- Exactly:
--
--   sum_sep PairedNestedOrbit
--     = 3 * sum_sep PairedBaseProductRule.
--
-- This is a genuinely localized identity unavailable at R772.  It introduces
-- no estimate or absolute value.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
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
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650CCTouchedQInvariantRound787Exact as R787
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedPOrbitInvariantRound790Exact as R790
import DASHI.Physics.Closure.NSTriadKNR650GlobalPairedNestedProductRuleRound772Exact as R772

F : C3.RealField _
F = Rational.rationalRealField

module SeparatedGlobalPairedNested
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module G = R772.GlobalPairedNested
    physicalSystem S L H velocityTransverse

  cutoff : Nat
  cutoff = G.cutoff

  items : List Physical.PhysicalTriadIncidence
  items = G.items

  maskedBaseRow : Physical.PhysicalTriadIncidence → ℚ
  maskedBaseRow beta with R781.ccTouched beta
  ... | true = 0ℚ
  ... | false = G.baseRow beta

  maskedPairedBaseRow : Physical.PhysicalTriadIncidence → ℚ
  maskedPairedBaseRow beta with R781.ccTouched beta
  ... | true = 0ℚ
  ... | false = G.pairedBaseRow beta

  maskedPairedOrbitCell : Physical.PhysicalTriadIncidence → ℚ
  maskedPairedOrbitCell beta with R781.ccTouched beta
  ... | true = 0ℚ
  ... | false = G.pairedOrbitCell beta

  maskedPairedBasePointwise :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedPairedBaseRow beta
    ≡
    maskedBaseRow beta
      + maskedBaseRow (Symmetry.swapTriad beta)
  maskedPairedBasePointwise beta
    rewrite R781.ccTouchedSwapInvariant beta
    with R781.ccTouched beta
  ... | true = solve []
  ... | false =
    sym (G.P.maskedNestedOuterRowSwapPair beta)

  maskedOrbitPointwise :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedPairedOrbitCell beta
    ≡
    maskedPairedBaseRow beta
      + R763.two * maskedBaseRow (Orbit.pEnergyLeg beta)
      + R763.two * maskedBaseRow (Orbit.qEnergyLeg beta)
  maskedOrbitPointwise beta
    rewrite R790.ccTouchedPInvariant beta
          | R787.ccTouchedQInvariant beta
    with R781.ccTouched beta
  ... | true = solve (R763.two ∷ [])
  ... | false =
    G.P.nestedOrbitSwapPairNormalForm beta

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
      map reindex items Perm.↭ items) →
    R38.foldPower (λ beta → value (reindex beta)) items
    ≡ R38.foldPower value items
  foldAfterReindex value reindex permutation =
    trans
      (sym (R38.foldMap value reindex items))
      (R38.foldPermutationInvariant value permutation)

  maskedPRowFoldIsBase :
    R38.foldPower
      (λ beta → maskedBaseRow (Orbit.pEnergyLeg beta)) items
    ≡ R38.foldPower maskedBaseRow items
  maskedPRowFoldIsBase =
    foldAfterReindex maskedBaseRow Orbit.pEnergyLeg
      (R38.pEnergyLegEnumerationPermutation cutoff)

  maskedQRowFoldIsBase :
    R38.foldPower
      (λ beta → maskedBaseRow (Orbit.qEnergyLeg beta)) items
    ≡ R38.foldPower maskedBaseRow items
  maskedQRowFoldIsBase =
    foldAfterReindex maskedBaseRow Orbit.qEnergyLeg
      (R38.qEnergyLegEnumerationPermutation cutoff)

  maskedSwapRowFoldIsBase :
    R38.foldPower
      (λ beta → maskedBaseRow (Symmetry.swapTriad beta)) items
    ≡ R38.foldPower maskedBaseRow items
  maskedSwapRowFoldIsBase =
    foldAfterReindex maskedBaseRow Symmetry.swapTriad
      (R38.swapTriadEnumerationPermutation cutoff)

  maskedPairedBaseFoldIsTwiceBase :
    R38.foldPower maskedPairedBaseRow items
    ≡ R763.two * R38.foldPower maskedBaseRow items
  maskedPairedBaseFoldIsTwiceBase =
    let
      base = R38.foldPower maskedBaseRow items
      swapped =
        R38.foldPower
          (λ beta → maskedBaseRow (Symmetry.swapTriad beta)) items
      expose =
        trans
          (foldCong
            maskedPairedBaseRow
            (λ beta →
              maskedBaseRow beta
                + maskedBaseRow (Symmetry.swapTriad beta))
            maskedPairedBasePointwise items)
          (G.foldAdd
            maskedBaseRow
            (λ beta → maskedBaseRow (Symmetry.swapTriad beta))
            items)
    in
    trans expose
      (trans
        (cong (base +_) maskedSwapRowFoldIsBase)
        (solve (base ∷ R763.two ∷ [])))

  maskedOrbitFoldDecomposition :
    R38.foldPower maskedPairedOrbitCell items
    ≡
    R38.foldPower maskedPairedBaseRow items
      + R763.two *
          R38.foldPower
            (λ beta → maskedBaseRow (Orbit.pEnergyLeg beta)) items
      + R763.two *
          R38.foldPower
            (λ beta → maskedBaseRow (Orbit.qEnergyLeg beta)) items
  maskedOrbitFoldDecomposition =
    trans
      (foldCong
        maskedPairedOrbitCell
        (λ beta →
          maskedPairedBaseRow beta
            + R763.two * maskedBaseRow (Orbit.pEnergyLeg beta)
            + R763.two * maskedBaseRow (Orbit.qEnergyLeg beta))
        maskedOrbitPointwise items)
      (foldScaledAdd3
        maskedPairedBaseRow
        (λ beta → maskedBaseRow (Orbit.pEnergyLeg beta))
        (λ beta → maskedBaseRow (Orbit.qEnergyLeg beta))
        items)

  separatedPairedNestedIsThreePairedBase :
    R38.foldPower maskedPairedOrbitCell items
    ≡ R772.three * R38.foldPower maskedPairedBaseRow items
  separatedPairedNestedIsThreePairedBase =
    let
      paired = R38.foldPower maskedPairedBaseRow items
      base = R38.foldPower maskedBaseRow items
    in
    trans
      maskedOrbitFoldDecomposition
      (trans
        (cong
          (λ selected →
            paired + R763.two * selected
              + R763.two *
                  R38.foldPower
                    (λ beta → maskedBaseRow (Orbit.qEnergyLeg beta)) items)
          maskedPRowFoldIsBase)
        (trans
          (cong
            (λ selected →
              paired + R763.two * base + R763.two * selected)
            maskedQRowFoldIsBase)
          (trans
            (cong
              (λ selected →
                selected + R763.two * base + R763.two * base)
              maskedPairedBaseFoldIsTwiceBase)
            (trans
              (solve (base ∷ R763.two ∷ R772.three ∷ []))
              (cong
                (R772.three *_)
                (sym maskedPairedBaseFoldIsTwiceBase))))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round791R772LocalizedToFullySeparatedFamily : Bool
round791R772LocalizedToFullySeparatedFamily = true

round791SeparatedPairedNestedIsThreePairedBase : Bool
round791SeparatedPairedNestedIsThreePairedBase = true

round791UsesPAndQMaskEquivariance : Bool
round791UsesPAndQMaskEquivariance = true

round791IntroducesEstimate : Bool
round791IntroducesEstimate = false

round791W2Closed : Bool
round791W2Closed = false

round791ClayPromotion : Bool
round791ClayPromotion = false

round791R772LocalizedToFullySeparatedFamilyIsTrue :
  round791R772LocalizedToFullySeparatedFamily ≡ true
round791R772LocalizedToFullySeparatedFamilyIsTrue = refl

round791SeparatedPairedNestedIsThreePairedBaseIsTrue :
  round791SeparatedPairedNestedIsThreePairedBase ≡ true
round791SeparatedPairedNestedIsThreePairedBaseIsTrue = refl

round791UsesPAndQMaskEquivarianceIsTrue :
  round791UsesPAndQMaskEquivariance ≡ true
round791UsesPAndQMaskEquivarianceIsTrue = refl

round791IntroducesEstimateIsFalse :
  round791IntroducesEstimate ≡ false
round791IntroducesEstimateIsFalse = refl

round791W2ClosedIsFalse :
  round791W2ClosedIsFalse = refl

round791ClayPromotionIsFalse :
  round791ClayPromotion ≡ false
round791ClayPromotionIsFalse = refl
