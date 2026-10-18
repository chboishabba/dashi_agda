{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelectedSelfFoldRealityRound719Exact where

------------------------------------------------------------------------
-- ROUND719 / CLOSE THE ZERO-SAFE SELECTED-SELF OUTPUT REALITY SEAM
--
-- R718 proved M_-k = conj(M_k) and showed simultaneous conjugation preserves
-- coherent work.  The only remaining same-object seam was
--
--   C^self_-k = conj(C^self_k)
--
-- for R714's literal ZERO-SAFE selected-self commutator fold.
--
-- This file closes that seam without weakening the p=0 branch:
--
--   canonical conjugation commutes with pEnergyLeg;
--   selected self forcing respects physical Fourier reality;
--   helical projectors and cross products respect conjugation;
--   the raw selected-self commutator respects conjugation;
--   modeEqual(-p,0) = modeEqual(p,0), so the R714 zero branch is preserved;
--   the canonical output-fibre conjugation permutation then gives the fold law.
--
-- Consequently R718's reality no-go is now unconditional on the literal
-- selected-self carrier.  No estimate or cancellation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Data.List.Base as ListBase
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as FibrePerm
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityLawsRound35Exact as RealityLaws
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3ScalarTripleOrbitRound93Exact as Triple
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNSummedProjectedNonlinearityRealityRound35Exact as SummedReality
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfOutputRealityRound718Exact as R718

canonicalConjugatePEnergyLeg :
  (tau : Physical.PhysicalTriadIncidence) →
  FibrePerm.canonicalConjugate (Orbit.pEnergyLeg tau)
  ≡ Orbit.pEnergyLeg (FibrePerm.canonicalConjugate tau)
canonicalConjugatePEnergyLeg tau =
  FibrePerm.physicalIncidenceExtPQ
    (FibrePerm.canonicalConjugate (Orbit.pEnergyLeg tau))
    (Orbit.pEnergyLeg (FibrePerm.canonicalConjugate tau))
    refl refl

canonicalConjugateSwap :
  (tau : Physical.PhysicalTriadIncidence) →
  FibrePerm.canonicalConjugate (Symmetry.swapTriad tau)
  ≡ Symmetry.swapTriad (FibrePerm.canonicalConjugate tau)
canonicalConjugateSwap tau =
  FibrePerm.physicalIncidenceExtPQ
    (FibrePerm.canonicalConjugate (Symmetry.swapTriad tau))
    (Symmetry.swapTriad (FibrePerm.canonicalConjugate tau))
    refl refl

modeEqualNegateZero :
  (mode : Z3.FourierMode) →
  Output.modeEqual (Z3.negateMode mode) Z3.zeroMode
  ≡ Output.modeEqual mode Z3.zeroMode
modeEqualNegateZero mode
  with Output.modeEqual mode Z3.zeroMode in base
     | Output.modeEqual (Z3.negateMode mode) Z3.zeroMode in neg
... | true | true = refl
... | true | false =
  let
    modeZero = Output.modeEqualSound base
    negZero : Z3.negateMode mode ≡ Z3.zeroMode
    negZero = trans (cong Z3.negateMode modeZero) refl
  in
  ⊥-elim
    (Output.falseNotTrue
      (trans (sym neg) (Output.modeEqualComplete negZero)))
... | false | true =
  let
    negZero = Output.modeEqualSound neg
    modeZero : mode ≡ Z3.zeroMode
    modeZero =
      trans
        (sym (Symmetry.negateModeInvolutive mode))
        (trans (cong Z3.negateMode negZero) refl)
  in
  ⊥-elim
    (Output.falseNotTrue
      (trans (sym base) (Output.modeEqualComplete modeZero)))
... | false | false = refl

module SelectedSelfReality
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R694.F)
    (S : Helical.HelicalModeScalars R694.F)
    (L : Helical.PeriodicHelicalProjectorLaws R694.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (velocityReality :
      Reality.RealityCondition
        (Audit.velocity (Field30.finiteSystem physicalSystem))) where

  module Prev =
    R718.OutputReality physicalSystem S L H velocityTransverse velocityReality

  module Out = Prev.Out
  module One = Out.One

  system = Field30.finiteSystem physicalSystem
  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  velocity = Audit.velocity system

  selfForcingKReality :
    (tau : Physical.PhysicalTriadIncidence) →
    R95.selfForcingK system (FibrePerm.canonicalConjugate tau)
    ≡ C3.complex3Conjugate (R95.selfForcingK system tau)
  selfForcingKReality tau =
    let
      first = Audit.projectedOrderedTerm system tau
      second = Audit.projectedOrderedTerm system (Symmetry.swapTriad tau)
    in
    trans
      (R111.selfForcingKIsTwoSelectedOrderedTerms
        system (FibrePerm.canonicalConjugate tau))
      (trans
        (cong₂ C3.complex3Add
          (SummedReality.canonicalConjugateTermReality
            system velocityReality tau)
          (trans
            (cong (Audit.projectedOrderedTerm system)
              (sym (canonicalConjugateSwap tau)))
            (SummedReality.canonicalConjugateTermReality
              system velocityReality (Symmetry.swapTriad tau))))
        (trans
          (sym (Additive.complex3ConjugateAdd first second))
          (cong C3.complex3Conjugate
            (sym (R111.selfForcingKIsTwoSelectedOrderedTerms system tau)))))

  selfForcingPReality :
    (tau : Physical.PhysicalTriadIncidence) →
    R95.selfForcingP system (FibrePerm.canonicalConjugate tau)
    ≡ C3.complex3Conjugate (R95.selfForcingP system tau)
  selfForcingPReality tau =
    trans
      (cong (R95.selfForcingForIncidence system)
        (sym (canonicalConjugatePEnergyLeg tau)))
      (selfForcingKReality (Orbit.pEnergyLeg tau))

  selfPlusForceMinusVelocityReality :
    (tau : Physical.PhysicalTriadIncidence) →
    One.Carrier.Normal.SelfSlot.Self.selfPlusForceMinusVelocity
      (FibrePerm.canonicalConjugate tau)
    ≡
    C3.complex3Conjugate
      (One.Carrier.Normal.SelfSlot.Self.selfPlusForceMinusVelocity tau)
  selfPlusForceMinusVelocityReality tau =
    let
      p = Physical.p tau
      q = Physical.q tau
      forceP = R95.selfForcingP system tau
      velQ = velocity q

      forcePlusReality :
        Helical.helicalProjectorPlus E I S
          (Z3.negateMode p)
          (R95.selfForcingP system (FibrePerm.canonicalConjugate tau))
        ≡
        C3.complex3Conjugate
          (Helical.helicalProjectorPlus E I S p forceP)
      forcePlusReality =
        trans
          (cong (Helical.helicalProjectorPlus E I S (Z3.negateMode p))
            (selfForcingPReality tau))
          (Helical.helicalProjectorRealityCompatible L Helical.plus p forceP)

      velocityMinusReality :
        Helical.helicalProjectorMinus E I S
          (Z3.negateMode q) (velocity (Z3.negateMode q))
        ≡
        C3.complex3Conjugate
          (Helical.helicalProjectorMinus E I S q velQ)
      velocityMinusReality =
        trans
          (cong (Helical.helicalProjectorMinus E I S (Z3.negateMode q))
            (velocityReality q))
          (Helical.helicalProjectorRealityCompatible L Helical.minus q velQ)
    in
    trans
      (cong₂ Cross.complex3Cross forcePlusReality velocityMinusReality)
      (Triple.crossConjugate
        (Helical.helicalProjectorPlus E I S p forceP)
        (Helical.helicalProjectorMinus E I S q velQ))

  selfMinusForcePlusVelocityReality :
    (tau : Physical.PhysicalTriadIncidence) →
    One.Carrier.Normal.SelfSlot.Self.selfMinusForcePlusVelocity
      (FibrePerm.canonicalConjugate tau)
    ≡
    C3.complex3Conjugate
      (One.Carrier.Normal.SelfSlot.Self.selfMinusForcePlusVelocity tau)
  selfMinusForcePlusVelocityReality tau =
    let
      p = Physical.p tau
      q = Physical.q tau
      forceP = R95.selfForcingP system tau
      velQ = velocity q

      forceMinusReality :
        Helical.helicalProjectorMinus E I S
          (Z3.negateMode p)
          (R95.selfForcingP system (FibrePerm.canonicalConjugate tau))
        ≡
        C3.complex3Conjugate
          (Helical.helicalProjectorMinus E I S p forceP)
      forceMinusReality =
        trans
          (cong (Helical.helicalProjectorMinus E I S (Z3.negateMode p))
            (selfForcingPReality tau))
          (Helical.helicalProjectorRealityCompatible L Helical.minus p forceP)

      velocityPlusReality :
        Helical.helicalProjectorPlus E I S
          (Z3.negateMode q) (velocity (Z3.negateMode q))
        ≡
        C3.complex3Conjugate
          (Helical.helicalProjectorPlus E I S q velQ)
      velocityPlusReality =
        trans
          (cong (Helical.helicalProjectorPlus E I S (Z3.negateMode q))
            (velocityReality q))
          (Helical.helicalProjectorRealityCompatible L Helical.plus q velQ)
    in
    trans
      (cong₂ Cross.complex3Cross forceMinusReality velocityPlusReality)
      (Triple.crossConjugate
        (Helical.helicalProjectorMinus E I S p forceP)
        (Helical.helicalProjectorPlus E I S q velQ))

  rawSelfCommutatorReality :
    (tau : Physical.PhysicalTriadIncidence) →
    One.Carrier.Normal.SelfSlot.Self.selfCommutatorCell
      (FibrePerm.canonicalConjugate tau)
    ≡
    C3.complex3Conjugate
      (One.Carrier.Normal.SelfSlot.Self.selfCommutatorCell tau)
  rawSelfCommutatorReality tau =
    trans
      (cong₂ C3.complex3Subtract
        (selfPlusForceMinusVelocityReality tau)
        (selfMinusForcePlusVelocityReality tau))
      (sym
        (RealityLaws.complex3ConjugateSubtract
          (One.Carrier.Normal.SelfSlot.Self.selfPlusForceMinusVelocity tau)
          (One.Carrier.Normal.SelfSlot.Self.selfMinusForcePlusVelocity tau)))

  zeroSafeSelfCellReality :
    (tau : Physical.PhysicalTriadIncidence) →
    Out.selfCell (FibrePerm.canonicalConjugate tau)
    ≡ C3.complex3Conjugate (Out.selfCell tau)
  zeroSafeSelfCellReality tau
    rewrite modeEqualNegateZero (Physical.p tau)
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = sym SummedReality.complex3ConjugateZero
  ... | false = rawSelfCommutatorReality tau

  selfFoldReality :
    (output : Z3.FourierMode) →
    Out.selfFold (Z3.negateMode output)
    ≡ C3.complex3Conjugate (Out.selfFold output)
  selfFoldReality output =
    let
      source = Out.fibre output
      permutation :
        ListBase.map FibrePerm.canonicalConjugate source
          Perm.↭ Out.fibre (Z3.negateMode output)
      permutation =
        FibrePerm.canonicalConjugateOutputFiberPermutation Out.cutoff output
    in
    trans
      (sym (R224.foldPermutationInvariant Out.selfCell permutation))
      (trans
        (R224.foldMap Out.selfCell FibrePerm.canonicalConjugate source)
        (Prev.foldConjugate Out.selfCell zeroSafeSelfCellReality source))

  fixedOutputSelfPairingRealityEven :
    (output : Z3.FourierMode) →
    Work.coherentWork
      (Out.mixedFold (Z3.negateMode output))
      (Out.selfFold (Z3.negateMode output))
    ≡
    Work.coherentWork
      (Out.mixedFold output)
      (Out.selfFold output)
  fixedOutputSelfPairingRealityEven output =
    Prev.realityPairingIsEven output (selfFoldReality output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round719CanonicalConjugationCommutesWithPEnergyLeg : Bool
round719CanonicalConjugationCommutesWithPEnergyLeg = true

round719SelectedSelfForcingRealityClosed : Bool
round719SelectedSelfForcingRealityClosed = true

round719ZeroSafeSelectedSelfCellRealityClosed : Bool
round719ZeroSafeSelectedSelfCellRealityClosed = true

round719SelectedSelfFoldRealityClosed : Bool
round719SelectedSelfFoldRealityClosed = true

round719RealityPairingIsEvenOnLiteralSelfCarrier : Bool
round719RealityPairingIsEvenOnLiteralSelfCarrier = true

round719RealityCancelsSelectedSelfPairing : Bool
round719RealityCancelsSelectedSelfPairing = false

round719IntroducesEstimate : Bool
round719IntroducesEstimate = false

round719ClayPromotion : Bool
round719ClayPromotion = false

round719SelectedSelfFoldRealityClosedIsTrue :
  round719SelectedSelfFoldRealityClosed ≡ true
round719SelectedSelfFoldRealityClosedIsTrue = refl

round719RealityPairingIsEvenOnLiteralSelfCarrierIsTrue :
  round719RealityPairingIsEvenOnLiteralSelfCarrier ≡ true
round719RealityPairingIsEvenOnLiteralSelfCarrierIsTrue = refl

round719RealityCancelsSelectedSelfPairingIsFalse :
  round719RealityCancelsSelectedSelfPairing ≡ false
round719RealityCancelsSelectedSelfPairingIsFalse = refl

round719IntroducesEstimateIsFalse :
  round719IntroducesEstimate ≡ false
round719IntroducesEstimateIsFalse = refl

round719ClayPromotionIsFalse :
  round719ClayPromotion ≡ false
round719ClayPromotionIsFalse = refl
