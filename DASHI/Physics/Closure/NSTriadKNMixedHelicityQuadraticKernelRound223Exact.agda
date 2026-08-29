module DASHI.Physics.Closure.NSTriadKNMixedHelicityQuadraticKernelRound223Exact where

------------------------------------------------------------------------
-- ROUND223 / QUADRATIC SLOT DIFFERENCE IS PURELY MIXED-HELICITY
--
-- Round142 identifies normalized curl with helicity-sign action
--
--   H u = u+ - u-.
--
-- Expanding the p/q slot difference before any absolute value gives
--
--   (H uP) x uQ - uP x (H uQ)
--
--     = 2 (uP+ x uQ- - uP- x uQ+).
--
-- Thus the same-helicity ++ and -- channels cancel EXACTLY at one physical
-- pair. Round167 identifies this slot difference with i times the authoritative
-- quadratic companion kernel, so the A-facing kernel is a mixed-helicity
-- object before any FL/HH/CC estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167

helicityTotal :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
helicityTotal = C3.complex3Add

helicityDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
helicityDifference = C3.complex3Subtract

mixedHelicityDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
mixedHelicityDifference pPlus pMinus qPlus qMinus =
  C3.complex3Subtract
    (Cross.complex3Cross pPlus qMinus)
    (Cross.complex3Cross pMinus qPlus)

doubleMixedHelicityDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
doubleMixedHelicityDifference pPlus pMinus qPlus qMinus =
  C3.complex3Add
    (mixedHelicityDifference pPlus pMinus qPlus qMinus)
    (mixedHelicityDifference pPlus pMinus qPlus qMinus)

helicitySlotDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
helicitySlotDifference pPlus pMinus qPlus qMinus =
  C3.complex3Subtract
    (Cross.complex3Cross
      (helicityDifference pPlus pMinus)
      (helicityTotal qPlus qMinus))
    (Cross.complex3Cross
      (helicityTotal pPlus pMinus)
      (helicityDifference qPlus qMinus))

helicitySlotDifferenceIsDoubleMixedHelicity :
  ∀ {r} {F : C3.RealField r}
    (pPlus pMinus qPlus qMinus : C3.Complex3 F) →
  helicitySlotDifference pPlus pMinus qPlus qMinus
  ≡ doubleMixedHelicityDifference pPlus pMinus qPlus qMinus
helicitySlotDifferenceIsDoubleMixedHelicity {F = F}
    pPlus pMinus qPlus qMinus =
  Field.complex3Ext
    (R.solve 8 goal refl
      (C3.y pPlus) (C3.z pPlus)
      (C3.y pMinus) (C3.z pMinus)
      (C3.y qPlus) (C3.z qPlus)
      (C3.y qMinus) (C3.z qMinus))
    (R.solve 8 goal refl
      (C3.z pPlus) (C3.x pPlus)
      (C3.z pMinus) (C3.x pMinus)
      (C3.z qPlus) (C3.x qPlus)
      (C3.z qMinus) (C3.x qMinus))
    (R.solve 8 goal refl
      (C3.x pPlus) (C3.y pPlus)
      (C3.x pMinus) (C3.y pMinus)
      (C3.x qPlus) (C3.y qPlus)
      (C3.x qMinus) (C3.y qMinus))
  where
  module R = Ring.Solver F
  goal = λ pa pb ma mb qa qb na nb →
    ( (((pa R.⊕ (R.⊝ ma)) R.⊗ (qb R.⊕ nb))
        R.⊕ (R.⊝ ((pb R.⊕ (R.⊝ mb)) R.⊗ (qa R.⊕ na))))
      R.⊕
      (R.⊝
        (((pa R.⊕ ma) R.⊗ (qb R.⊕ (R.⊝ nb)))
          R.⊕ (R.⊝ ((pb R.⊕ mb) R.⊗ (qa R.⊕ (R.⊝ na)))))) )
    R.⊜
    ( (((pa R.⊗ nb) R.⊕ (R.⊝ (pb R.⊗ na)))
        R.⊕ (R.⊝ ((ma R.⊗ qb) R.⊕ (R.⊝ (mb R.⊗ qa)))))
      R.⊕
      (((pa R.⊗ nb) R.⊕ (R.⊝ (pb R.⊗ na)))
        R.⊕ (R.⊝ ((ma R.⊗ qb) R.⊕ (R.⊝ (mb R.⊗ qa))))) )

record PhysicalHelicityPair
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) : Set r where
  constructor physical-helicity-pair
  field
    transverseP : Helical.Transverse E p uP
    transverseQ : Helical.Transverse E q uQ

open PhysicalHelicityPair public

physicalNormalizedCurlSlotDifferenceIsDoubleMixedHelicity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F)
    (P : PhysicalHelicityPair E I S L H p q uP uQ) →
  C3.complex3Subtract
    (Cross.complex3Cross (R142.normalizedCurl E S p uP) uQ)
    (Cross.complex3Cross uP (R142.normalizedCurl E S q uQ))
  ≡
  doubleMixedHelicityDifference
    (Helical.helicalProjectorPlus E I S p uP)
    (Helical.helicalProjectorMinus E I S p uP)
    (Helical.helicalProjectorPlus E I S q uQ)
    (Helical.helicalProjectorMinus E I S q uQ)
physicalNormalizedCurlSlotDifferenceIsDoubleMixedHelicity
    {E = E} {I = I} {S = S} {L = L} {H = H}
    p q uP uQ P
  rewrite sym (Helical.velocityHelicalDecomposition L p uP (transverseP P))
        | sym (Helical.velocityHelicalDecomposition L q uQ (transverseQ P))
        | sym (R142.helicitySignActionIsNormalizedCurl E I S H p uP)
        | sym (R142.helicitySignActionIsNormalizedCurl E I S H q uQ) =
  helicitySlotDifferenceIsDoubleMixedHelicity
    (Helical.helicalProjectorPlus E I S p uP)
    (Helical.helicalProjectorMinus E I S p uP)
    (Helical.helicalProjectorPlus E I S q uQ)
    (Helical.helicalProjectorMinus E I S q uQ)

iQuadraticKernelIsDoubleMixedHelicity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F)
    (P : PhysicalHelicityPair E I S L H p q uP uQ) →
  C3.complex3Scale (C3.complexI F)
    (R145.slotKernel
      (R167.normalizedDirection E S p)
      (R167.normalizedDirection E S q)
      uP uQ)
  ≡
  doubleMixedHelicityDifference
    (Helical.helicalProjectorPlus E I S p uP)
    (Helical.helicalProjectorMinus E I S p uP)
    (Helical.helicalProjectorPlus E I S q uQ)
    (Helical.helicalProjectorMinus E I S q uQ)
iQuadraticKernelIsDoubleMixedHelicity {E = E} {S = S}
    p q uP uQ P =
  trans
    (sym (R167.normalizedCurlSlotVectorDifferenceIsIQuadraticKernel
      E S p q uP uQ))
    (physicalNormalizedCurlSlotDifferenceIsDoubleMixedHelicity
      p q uP uQ P)

round223SameHelicityChannelsCancelPointwise : Bool
round223SameHelicityChannelsCancelPointwise = true

round223QuadraticKernelIsPureMixedHelicity : Bool
round223QuadraticKernelIsPureMixedHelicity = true

round223MixedHelicityIntegratedBudgetClosed : Bool
round223MixedHelicityIntegratedBudgetClosed = false

round223PackageAClosed : Bool
round223PackageAClosed = false

round223ClayPromotion : Bool
round223ClayPromotion = false

round223SameHelicityChannelsCancelPointwiseIsTrue :
  round223SameHelicityChannelsCancelPointwise ≡ true
round223SameHelicityChannelsCancelPointwiseIsTrue = refl

round223QuadraticKernelIsPureMixedHelicityIsTrue :
  round223QuadraticKernelIsPureMixedHelicity ≡ true
round223QuadraticKernelIsPureMixedHelicityIsTrue = refl

round223MixedHelicityIntegratedBudgetClosedIsFalse :
  round223MixedHelicityIntegratedBudgetClosed ≡ false
round223MixedHelicityIntegratedBudgetClosedIsFalse = refl

round223PackageAClosedIsFalse : round223PackageAClosed ≡ false
round223PackageAClosedIsFalse = refl

round223ClayPromotionIsFalse : round223ClayPromotion ≡ false
round223ClayPromotionIsFalse = refl
