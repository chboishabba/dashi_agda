{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ExternalZeroBranchEliminationRound673Exact where

------------------------------------------------------------------------
-- ROUND673 / THE R672 p=0 EXTERNAL DEFECT VANISHES ON THE PHYSICAL CARRIER
--
-- R672 deliberately retained the p=0 defect rather than deleting R630's
-- totalization branch by assumption.  The physical transversality already
-- supplied to that carrier is enough to prove the defect is actually zero.
--
-- For p_tau = 0:
--
--   * R436 gives projectedNonlinearity(0) = 0;
--   * R111 writes the selected self p-forcing as the two ordered terms on the
--     p-energy leg and its swap;
--   * both of those ordered terms have zero output and therefore vanish by the
--     same R436 zero-output theorem;
--   * hence externalForcingP = fullForcingP - selfForcingP = 0;
--   * the external forcing commutator is therefore zero before weighting.
--
-- Thus R672's explicit zero-branch defect fold vanishes exactly, and the R606
-- spectator-weighted external double-forcing fold lands on the R630 TOTAL
-- external nested commutator fold, including the p=0 branch.
--
-- This is still representation/algebra only.  The R637 signed spacetime
-- quantitative payment remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact as R437
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNR650ExternalTotalizationZeroBranchRound672Exact as R672

module ExternalZeroElimination673
    {r} {F : C3.RealField r}
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
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (W : R294.SwapInvariantCellWeight F) where

  system = Field30.finiteSystem physicalSystem
  module Base =
    R672.ExternalTotalization672
      physicalSystem S L H velocityTransverse W

  selfForcingPAtZero :
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.p tau ≡ Z3.zeroMode →
    R95.selfForcingP system tau ≡ C3.complex3Zero F
  selfForcingPAtZero tau pZero =
    let
      pLeg = Orbit.pEnergyLeg tau
      pLegZero :
        Physical.k pLeg ≡ Z3.zeroMode
      pLegZero =
        trans (Orbit.pEnergyLegOutput tau) pZero

      swapPLegZero :
        Physical.k (Symmetry.swapTriad pLeg) ≡ Z3.zeroMode
      swapPLegZero =
        trans (Symmetry.swapTriadK pLeg) pLegZero

      firstZero =
        R436.projectedOrderedTermAtZeroOutputIsZero
          system velocityTransverse pLeg pLegZero

      secondZero =
        R436.projectedOrderedTermAtZeroOutputIsZero
          system velocityTransverse
          (Symmetry.swapTriad pLeg) swapPLegZero
    in
    trans
      (R111.selfForcingKIsTwoSelectedOrderedTerms system pLeg)
      (trans
        (cong₂ C3.complex3Add firstZero secondZero)
        (Algebra.complex3AddZeroRight (C3.complex3Zero F)))

  fullForcingPAtZero :
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.p tau ≡ Z3.zeroMode →
    R95.fullForcingP system tau ≡ C3.complex3Zero F
  fullForcingPAtZero tau pZero =
    trans
      (cong (Audit.projectedNonlinearity system) pZero)
      (R436.projectedNonlinearityAtZeroIsZero
        system velocityTransverse)

  externalForcingPAtZero :
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.p tau ≡ Z3.zeroMode →
    R95.externalForcingP system tau ≡ C3.complex3Zero F
  externalForcingPAtZero tau pZero =
    trans
      (cong₂ C3.complex3Subtract
        (fullForcingPAtZero tau pZero)
        (selfForcingPAtZero tau pZero))
      (R106.complex3SubtractSelf (C3.complex3Zero F))

  externalCommutatorAtZero :
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.p tau ≡ Z3.zeroMode →
    Base.Weighted.Ext.externalCommutatorCell tau
    ≡ C3.complex3Zero F
  externalCommutatorAtZero tau pZero =
    R437.forcingCommutatorZeroFromForcingZero
      S
      (Audit.velocity system)
      (λ _ → R95.externalForcingP system tau)
      tau
      (externalForcingPAtZero tau pZero)

  weightedExternalCommutatorAtZero :
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.p tau ≡ Z3.zeroMode →
    Base.weightedCommutator tau ≡ C3.complex3Zero F
  weightedExternalCommutatorAtZero tau pZero =
    trans
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (externalCommutatorAtZero tau pZero))
      (R106.complex3ScaleZeroVector (R294.weight W tau))

  module AtOutput (output : Z3.FourierMode) where

    module At = Base.AtOutput output

    rawNestedAtZero :
      (tau : Physical.PhysicalTriadIncidence) →
      Physical.p tau ≡ Z3.zeroMode →
      Base.Weld.rawWeightedNestedExternalCommutator tau
      ≡ C3.complex3Zero F
    rawNestedAtZero tau pZero =
      let
        commZero = weightedExternalCommutatorAtZero tau pZero
      in
      trans
        (At.rawWeightedNestedIsFourCommutators tau)
        (trans
          (cong₂ C3.complex3Add
            (cong₂ C3.complex3Add commZero commZero)
            (cong₂ C3.complex3Add commZero commZero))
          (trans
            (cong₂ C3.complex3Add
              (Algebra.complex3AddZeroRight (C3.complex3Zero F))
              (Algebra.complex3AddZeroRight (C3.complex3Zero F)))
            (Algebra.complex3AddZeroRight (C3.complex3Zero F))))

    pZeroNestedDefectIsZero :
      (tau : Physical.PhysicalTriadIncidence) →
      At.pZeroNestedDefect tau ≡ C3.complex3Zero F
    pZeroNestedDefectIsZero tau
        with Output.modeEqual (Physical.p tau) Z3.zeroMode in decision
    ... | true =
      rawNestedAtZero tau (Output.modeEqualSound decision)
    ... | false = refl

    pZeroNestedDefectFoldIsZero :
      R224.foldVector At.pZeroNestedDefect At.fibre
      ≡ C3.complex3Zero F
    pZeroNestedDefectFoldIsZero =
      foldZero At.fibre
      where
      foldZero :
        (items : List Physical.PhysicalTriadIncidence) →
        R224.foldVector At.pZeroNestedDefect items
        ≡ C3.complex3Zero F
      foldZero [] = refl
      foldZero (tau ∷ rest) =
        trans
          (cong₂ C3.complex3Add
            (pZeroNestedDefectIsZero tau)
            (foldZero rest))
          (Algebra.complex3AddZeroRight (C3.complex3Zero F))

    fixedOutputR606ExternalFoldIsR630Total :
      R224.foldVector At.weightedExternalDoubleForcing At.fibre
      ≡
      R224.foldVector
        Base.Total.totalExternalNestedCommutator
        At.fibre
    fixedOutputR606ExternalFoldIsR630Total =
      let
        totalFold =
          R224.foldVector
            Base.Total.totalExternalNestedCommutator
            At.fibre
      in
      trans
        At.fixedOutputR606ExternalFoldIsTotalPlusPZeroDefect
        (trans
          (cong
            (C3.complex3Add totalFold)
            pZeroNestedDefectFoldIsZero)
          (Algebra.complex3AddZeroRight totalFold))

------------------------------------------------------------------------
-- Status / completed zero-branch splice.
------------------------------------------------------------------------

round673SelectedSelfPForcingAtZeroClosed : Bool
round673SelectedSelfPForcingAtZeroClosed = true

round673ExternalPForcingAtZeroClosed : Bool
round673ExternalPForcingAtZeroClosed = true

round673ExternalCommutatorAtZeroClosed : Bool
round673ExternalCommutatorAtZeroClosed = true

round673PZeroDefectEliminated : Bool
round673PZeroDefectEliminated = true

round673R606ExternalFoldEqualsR630TotalIncludingZeroBranch : Bool
round673R606ExternalFoldEqualsR630TotalIncludingZeroBranch = true

round673IntroducesEstimate : Bool
round673IntroducesEstimate = false

round673ExternalSignedPaymentClosed : Bool
round673ExternalSignedPaymentClosed = false

round673IntroducesNewClayLeaf : Bool
round673IntroducesNewClayLeaf = false

round673ClayPromotion : Bool
round673ClayPromotion = false

round673SelectedSelfPForcingAtZeroClosedIsTrue :
  round673SelectedSelfPForcingAtZeroClosed ≡ true
round673SelectedSelfPForcingAtZeroClosedIsTrue = refl

round673ExternalPForcingAtZeroClosedIsTrue :
  round673ExternalPForcingAtZeroClosed ≡ true
round673ExternalPForcingAtZeroClosedIsTrue = refl

round673ExternalCommutatorAtZeroClosedIsTrue :
  round673ExternalCommutatorAtZeroClosed ≡ true
round673ExternalCommutatorAtZeroClosedIsTrue = refl

round673PZeroDefectEliminatedIsTrue :
  round673PZeroDefectEliminated ≡ true
round673PZeroDefectEliminatedIsTrue = refl

round673R606ExternalFoldEqualsR630TotalIncludingZeroBranchIsTrue :
  round673R606ExternalFoldEqualsR630TotalIncludingZeroBranch ≡ true
round673R606ExternalFoldEqualsR630TotalIncludingZeroBranchIsTrue = refl

round673IntroducesEstimateIsFalse :
  round673IntroducesEstimate ≡ false
round673IntroducesEstimateIsFalse = refl

round673ExternalSignedPaymentClosedIsFalse :
  round673ExternalSignedPaymentClosed ≡ false
round673ExternalSignedPaymentClosedIsFalse = refl

round673IntroducesNewClayLeafIsFalse :
  round673IntroducesNewClayLeaf ≡ false
round673IntroducesNewClayLeafIsFalse = refl

round673ClayPromotionIsFalse :
  round673ClayPromotion ≡ false
round673ClayPromotionIsFalse = refl
