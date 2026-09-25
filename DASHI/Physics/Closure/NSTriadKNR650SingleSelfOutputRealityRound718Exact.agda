{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SingleSelfOutputRealityRound718Exact where

------------------------------------------------------------------------
-- ROUND718 / OUTPUT REALITY DOES NOT SUPPLY A MINUS SIGN
--
-- R717 reduces the complete selected-self question to
--
--   sum_{k != 0} W(M_k,C_k^self).
--
-- The mixed fold M_k has the ordinary Fourier reality law.  This file proves
-- that statement on the literal output fibres using the existing canonical
-- conjugation permutation.  It also records the decisive scalar algebra:
--
--   W(conj M, conj C) = W(M,C).
--
-- Hence if the selected-self fold C_k obeys the corresponding physical reality
-- law (the next same-object seam), then
--
--   W(M_-k,C_-k) = W(M_k,C_k),
--
-- not its negative.  The conjugate-output orbit therefore DUPLICATES the
-- scalar and cannot be the missing self cancellation mechanism.
--
-- No estimate or cancellation is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Data.List.Base as ListBase
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as FibrePerm
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNComplex3ScalarTripleOrbitRound93Exact as Triple
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfOutputPairingCollapseRound717Exact as R717

module OutputReality
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

  module Out =
    R717.OutputPairingCollapse physicalSystem S L H velocityTransverse

  system = Field30.finiteSystem physicalSystem
  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  velocity = Audit.velocity system

  mixedCellCanonicalConjugate :
    (tau : Physical.PhysicalTriadIncidence) →
    Out.mixedCell (FibrePerm.canonicalConjugate tau)
    ≡ C3.complex3Conjugate (Out.mixedCell tau)
  mixedCellCanonicalConjugate tau =
    let
      p = Physical.p tau
      q = Physical.q tau
      plusP = Helical.helicalProjectorPlus E I S p (velocity p)
      minusQ = Helical.helicalProjectorMinus E I S q (velocity q)

      plusReality :
        Helical.helicalProjectorPlus E I S
          (Z3.negateMode p) (velocity (Z3.negateMode p))
        ≡ C3.complex3Conjugate plusP
      plusReality =
        trans
          (cong
            (Helical.helicalProjectorPlus E I S (Z3.negateMode p))
            (velocityReality p))
          (Helical.helicalProjectorRealityCompatible
            L Helical.plus p (velocity p))

      minusReality :
        Helical.helicalProjectorMinus E I S
          (Z3.negateMode q) (velocity (Z3.negateMode q))
        ≡ C3.complex3Conjugate minusQ
      minusReality =
        trans
          (cong
            (Helical.helicalProjectorMinus E I S (Z3.negateMode q))
            (velocityReality q))
          (Helical.helicalProjectorRealityCompatible
            L Helical.minus q (velocity q))
    in
    trans
      (cong₂ Triple.Cross.complex3Cross plusReality minusReality)
      (Triple.crossConjugate plusP minusQ)

  foldConjugate :
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 R694.F) →
    ((tau : Physical.PhysicalTriadIncidence) →
      value (FibrePerm.canonicalConjugate tau)
      ≡ C3.complex3Conjugate (value tau)) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector
      (λ tau → value (FibrePerm.canonicalConjugate tau)) items
    ≡ C3.complex3Conjugate (R224.foldVector value items)
  foldConjugate value pointwise [] =
    sym
      (let open import DASHI.Physics.Closure.NSTriadKNSummedProjectedNonlinearityRealityRound35Exact
       in complex3ConjugateZero)
  foldConjugate value pointwise (tau ∷ rest) =
    trans
      (cong₂ C3.complex3Add
        (pointwise tau)
        (foldConjugate value pointwise rest))
      (sym
        (Additive.complex3ConjugateAdd
          (value tau) (R224.foldVector value rest)))

  mixedFoldReality :
    (output : Z3.FourierMode) →
    Out.mixedFold (Z3.negateMode output)
    ≡ C3.complex3Conjugate (Out.mixedFold output)
  mixedFoldReality output =
    let
      source = Out.fibre output
      target = Out.fibre (Z3.negateMode output)
      permutation :
        ListBase.map FibrePerm.canonicalConjugate source Perm.↭ target
      permutation =
        FibrePerm.canonicalConjugateOutputFiberPermutation Out.cutoff output
    in
    trans
      (sym
        (R224.foldPermutationInvariant Out.mixedCell permutation))
      (trans
        (R224.foldMap Out.mixedCell FibrePerm.canonicalConjugate source)
        (foldConjugate Out.mixedCell mixedCellCanonicalConjugate source))

  coherentWorkConjugateBoth :
    (left right : C3.Complex3 R694.F) →
    Out.One.Carrier.Split.Full.Nested.Base.Work.coherentWork
      (C3.complex3Conjugate left)
      (C3.complex3Conjugate right)
    ≡
    Out.One.Carrier.Split.Full.Nested.Base.Work.coherentWork left right
  coherentWorkConjugateBoth left right =
    cong
      (Out.One.Carrier.Split.Full.Nested.Base.Work.two *_)
      (R287.realHermitianCrossConjugateBoth left right)

  realityPairingIsEven :
    (output : Z3.FourierMode) →
    (selfReality :
      Out.selfFold (Z3.negateMode output)
      ≡ C3.complex3Conjugate (Out.selfFold output)) →
    Out.One.Carrier.Split.Full.Nested.Base.Work.coherentWork
      (Out.mixedFold (Z3.negateMode output))
      (Out.selfFold (Z3.negateMode output))
    ≡
    Out.One.Carrier.Split.Full.Nested.Base.Work.coherentWork
      (Out.mixedFold output)
      (Out.selfFold output)
  realityPairingIsEven output selfReality
    rewrite mixedFoldReality output
          | selfReality =
    coherentWorkConjugateBoth
      (Out.mixedFold output) (Out.selfFold output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round718MixedOutputFoldRealityClosed : Bool
round718MixedOutputFoldRealityClosed = true

round718SimultaneousConjugationChangesCoherentWorkSign : Bool
round718SimultaneousConjugationChangesCoherentWorkSign = false

round718RealityOrbitWouldCancelSelfPairing : Bool
round718RealityOrbitWouldCancelSelfPairing = false

round718SelectedSelfFoldRealityClosed : Bool
round718SelectedSelfFoldRealityClosed = false

round718IntroducesEstimate : Bool
round718IntroducesEstimate = false

round718ClayPromotion : Bool
round718ClayPromotion = false

round718MixedOutputFoldRealityClosedIsTrue :
  round718MixedOutputFoldRealityClosed ≡ true
round718MixedOutputFoldRealityClosedIsTrue = refl

round718SimultaneousConjugationChangesCoherentWorkSignIsFalse :
  round718SimultaneousConjugationChangesCoherentWorkSign ≡ false
round718SimultaneousConjugationChangesCoherentWorkSignIsFalse = refl

round718RealityOrbitWouldCancelSelfPairingIsFalse :
  round718RealityOrbitWouldCancelSelfPairing ≡ false
round718RealityOrbitWouldCancelSelfPairingIsFalse = refl

round718SelectedSelfFoldRealityClosedIsFalse :
  round718SelectedSelfFoldRealityClosed ≡ false
round718SelectedSelfFoldRealityClosedIsFalse = refl

round718IntroducesEstimateIsFalse :
  round718IntroducesEstimate ≡ false
round718IntroducesEstimateIsFalse = refl

round718ClayPromotionIsFalse :
  round718ClayPromotion ≡ false
round718ClayPromotionIsFalse = refl
