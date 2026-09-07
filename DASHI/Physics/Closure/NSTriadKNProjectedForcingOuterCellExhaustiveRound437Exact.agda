module DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact where

------------------------------------------------------------------------
-- ROUND437 / EVERY PROJECTED-FORCING OUTER CELL IS SLOT-KERNEL OR EXACT ZERO
--
-- R307 identifies the actual projected NS forcing with the old R167/R145 slot
-- kernel whenever the forcing leg p is nonzero. R436 proves the complementary
-- fact that the actual projected nonlinearity at p=0 vanishes exactly under the
-- all-mode transversality already carried by the physical trajectory.
--
-- This file closes the resulting executable partition:
--
--   p != 0  -> doubled R230 cell = i * R145 slotKernel(N_p,u_q)
--   p  = 0  -> N_p = 0 -> doubled R230 cell = 0.
--
-- Thus the old R307 orientation exception is removed without ever evaluating
-- normalizedDirection at the zero mode. No estimate or absolute value is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNMixedHelicityQuadraticKernelRound223Exact as R223
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNForcingHelicityCommutatorRound306Exact as R306
import DASHI.Physics.Closure.NSTriadKNForcingSlotKernelRound307Exact as R307
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436

crossZeroRight :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  Helical.complex3Cross v (C3.complex3Zero F) ≡ C3.complex3Zero F
crossZeroRight {F = F} (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (trans
      (cong₂ C3.complexSubtract
        (Field.complexMultiplyZeroRight vy)
        (Field.complexMultiplyZeroRight vz))
      (Additive.complexSubtractSelf (C3.complexZero F)))
    (trans
      (cong₂ C3.complexSubtract
        (Field.complexMultiplyZeroRight vz)
        (Field.complexMultiplyZeroRight vx))
      (Additive.complexSubtractSelf (C3.complexZero F)))
    (trans
      (cong₂ C3.complexSubtract
        (Field.complexMultiplyZeroRight vx)
        (Field.complexMultiplyZeroRight vy))
      (Additive.complexSubtractSelf (C3.complexZero F)))

curlSymbolZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (mode : Z3.FourierMode) →
  Helical.curlSymbol E mode (C3.complex3Zero F) ≡ C3.complex3Zero F
curlSymbolZero {F = F} E mode =
  trans
    (cong (C3.complex3Scale (C3.complexI F))
      (crossZeroRight (C3.modeVector E mode)))
    (R106.complex3ScaleZeroVector (C3.complexI F))

helicalProjectorPlusZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (mode : Z3.FourierMode) →
  Helical.helicalProjectorPlus E I S mode (C3.complex3Zero F)
  ≡ C3.complex3Zero F
helicalProjectorPlusZero {F = F} E I S mode =
  trans
    (cong
      (C3.complex3Scale (C3.realEmbed F (Helical.half S)))
      (cong₂ C3.complex3Add
        (R436.lerayZeroVector E I mode)
        (trans
          (cong
            (C3.complex3Scale
              (C3.realEmbed F (Helical.inverseModeNorm S mode)))
            (curlSymbolZero E mode))
          (R106.complex3ScaleZeroVector
            (C3.realEmbed F (Helical.inverseModeNorm S mode))))))
    (trans
      (cong
        (C3.complex3Scale (C3.realEmbed F (Helical.half S)))
        (R230.complex3AddZeroLeft (C3.complex3Zero F)))
      (R106.complex3ScaleZeroVector
        (C3.realEmbed F (Helical.half S))))

helicalProjectorMinusZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (mode : Z3.FourierMode) →
  Helical.helicalProjectorMinus E I S mode (C3.complex3Zero F)
  ≡ C3.complex3Zero F
helicalProjectorMinusZero {F = F} E I S mode =
  trans
    (cong
      (C3.complex3Scale (C3.realEmbed F (Helical.half S)))
      (cong₂ C3.complex3Subtract
        (R436.lerayZeroVector E I mode)
        (trans
          (cong
            (C3.complex3Scale
              (C3.realEmbed F (Helical.inverseModeNorm S mode)))
            (curlSymbolZero E mode))
          (R106.complex3ScaleZeroVector
            (C3.realEmbed F (Helical.inverseModeNorm S mode))))))
    (trans
      (cong
        (C3.complex3Scale (C3.realEmbed F (Helical.half S)))
        (R106.complex3SubtractSelf (C3.complex3Zero F)))
      (R106.complex3ScaleZeroVector
        (C3.realEmbed F (Helical.half S))))

forcingCommutatorZeroFromForcingZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  forcing (Physical.p tau) ≡ C3.complex3Zero F →
  R230.forcingCommutatorCell S velocity forcing tau
  ≡ C3.complex3Zero F
forcingCommutatorZeroFromForcingZero {F = F} {E = E} {I = I}
    S velocity forcing tau forcingZero =
  let
    p = Physical.p tau
    q = Physical.q tau
    uQ = velocity q
    pPlusZero =
      trans
        (cong (Helical.helicalProjectorPlus E I S p) forcingZero)
        (helicalProjectorPlusZero E I S p)
    pMinusZero =
      trans
        (cong (Helical.helicalProjectorMinus E I S p) forcingZero)
        (helicalProjectorMinusZero E I S p)
  in
  trans
    (cong₂ C3.complex3Subtract
      (cong₂ Helical.complex3Cross pPlusZero refl)
      (cong₂ Helical.complex3Cross pMinusZero refl))
    (zeroCrossDifference
      (Helical.helicalProjectorMinus E I S q uQ)
      (Helical.helicalProjectorPlus E I S q uQ))
  where
  crossZeroLeft :
    ∀ (v : C3.Complex3 F) →
    Helical.complex3Cross (C3.complex3Zero F) v ≡ C3.complex3Zero F
  crossZeroLeft (C3.complex3 vx vy vz) =
    Algebra.complex3Ext
      (trans
        (cong₂ C3.complexSubtract
          (Field.complexMultiplyZeroLeft vz)
          (Field.complexMultiplyZeroLeft vy))
        (Additive.complexSubtractSelf (C3.complexZero F)))
      (trans
        (cong₂ C3.complexSubtract
          (Field.complexMultiplyZeroLeft vx)
          (Field.complexMultiplyZeroLeft vz))
        (Additive.complexSubtractSelf (C3.complexZero F)))
      (trans
        (cong₂ C3.complexSubtract
          (Field.complexMultiplyZeroLeft vy)
          (Field.complexMultiplyZeroLeft vx))
        (Additive.complexSubtractSelf (C3.complexZero F)))

  zeroCrossDifference :
    (left right : C3.Complex3 F) →
    C3.complex3Subtract
      (Helical.complex3Cross (C3.complex3Zero F) left)
      (Helical.complex3Cross (C3.complex3Zero F) right)
    ≡ C3.complex3Zero F
  zeroCrossDifference left right =
    trans
      (cong₂ C3.complex3Subtract
        (crossZeroLeft left) (crossZeroLeft right))
      (R106.complex3SubtractSelf (C3.complex3Zero F))

doubleR230ZeroFromForcingZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  forcing (Physical.p tau) ≡ C3.complex3Zero F →
  R306.doubleR230Cell S velocity forcing tau ≡ C3.complex3Zero F
doubleR230ZeroFromForcingZero {F = F} S velocity forcing tau forcingZero =
  trans
    (cong₂ C3.complex3Add
      (forcingCommutatorZeroFromForcingZero S velocity forcing tau forcingZero)
      (forcingCommutatorZeroFromForcingZero S velocity forcing tau forcingZero))
    (R230.complex3AddZeroLeft (C3.complex3Zero F))

data ProjectedForcingOuterCellCase
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  slot-kernel-cell :
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    R306.doubleR230Cell S
      (Audit.velocity system)
      (Audit.projectedNonlinearity system)
      tau
    ≡
    C3.complex3Scale (C3.complexI F)
      (R145.slotKernel
        (R167.normalizedDirection E S (Physical.p tau))
        (R167.normalizedDirection E S (Physical.q tau))
        (Audit.projectedNonlinearity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau))) →
    ProjectedForcingOuterCellCase S system tau

  zero-forcing-cell :
    Physical.p tau ≡ Z3.zeroMode →
    Audit.projectedNonlinearity system (Physical.p tau)
      ≡ C3.complex3Zero F →
    R306.doubleR230Cell S
      (Audit.velocity system)
      (Audit.projectedNonlinearity system)
      tau
      ≡ C3.complex3Zero F →
    ProjectedForcingOuterCellCase S system tau

classifyProjectedForcingOuterCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (tau : Physical.PhysicalTriadIncidence) →
  ProjectedForcingOuterCellCase S system tau
classifyProjectedForcingOuterCell {E = E} {S = S}
    system velocityTransverse tau
  with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
... | true =
  let
    pZero = Output.modeEqualSound pDecision
    forcingZero :
      Audit.projectedNonlinearity system (Physical.p tau)
      ≡ C3.complex3Zero _
    forcingZero =
      trans
        (cong (Audit.projectedNonlinearity system) pZero)
        (R436.projectedNonlinearityAtZeroIsZero system velocityTransverse)
  in
  zero-forcing-cell
    pZero forcingZero
    (doubleR230ZeroFromForcingZero
      S (Audit.velocity system) (Audit.projectedNonlinearity system)
      tau forcingZero)
... | false =
  let
    pNonzero : Z3.NonZeroMode (Physical.p tau)
    pNonzero = record
      { Z3.notZero = λ pZero →
          Output.falseNotTrue
            (trans (sym pDecision) (Output.modeEqualComplete pZero))
      }
  in
  slot-kernel-cell
    pNonzero
    (R307.doubledProjectedNSForcingCellIsIOuterSlotKernel
      system tau pNonzero (velocityTransverse (Physical.q tau)))

round437EveryOuterCellClassifiedSlotOrZero : Bool
round437EveryOuterCellClassifiedSlotOrZero = true

round437ZeroForcingLegDiscardedBeforeNorm : Bool
round437ZeroForcingLegDiscardedBeforeNorm = true

round437NormalizedDirectionAtZeroRequired : Bool
round437NormalizedDirectionAtZeroRequired = false

round437UsesAnyAnalyticEstimate : Bool
round437UsesAnyAnalyticEstimate = false

round437R294WeightedSameObjectFoldClosed : Bool
round437R294WeightedSameObjectFoldClosed = false

round437R423SignedCompanionBudgetClosed : Bool
round437R423SignedCompanionBudgetClosed = false

round437PackageAClosed : Bool
round437PackageAClosed = false

round437ClayPromotion : Bool
round437ClayPromotion = false

round437EveryOuterCellClassifiedSlotOrZeroIsTrue :
  round437EveryOuterCellClassifiedSlotOrZero ≡ true
round437EveryOuterCellClassifiedSlotOrZeroIsTrue = refl

round437NormalizedDirectionAtZeroRequiredIsFalse :
  round437NormalizedDirectionAtZeroRequired ≡ false
round437NormalizedDirectionAtZeroRequiredIsFalse = refl
