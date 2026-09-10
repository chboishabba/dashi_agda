module DASHI.Physics.Closure.NSTriadKNLiveOuterSignedCrossDecompositionRound589Exact where

-- Repository-native DASHI extension, based on R581's exact zero-masked
-- partition, R291's Hermitian additivity, and R438/R440's physical forcing.
-- Recoverable baseline: dashi_agda commit 6cd63dcd7cda24cddb641ee7326143cf33ed01dd.
-- No external analytic theorem is imported here. The full amplitude is held
-- fixed while partitioning ONLY the outer forcing incidence. In particular,
-- cross-class interference survives. No deep/shoulder payment is asserted.
-- Draft: Agda execution deferred by user instruction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool.Base using (not)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact as R434
import DASHI.Physics.Closure.NSTriadKNModernHistoricalCriticalConeSignedCrossBidiRound588Exact as R588

F : C3.RealField _
F = R440.F

-- Repo-native decidable shell tests calibrated to the scalar thresholds in
-- R234/R235. Using min for HH is conservative; an analytic comparison with
-- their common high-shell convention is still required. Shell zero follows
-- Shell's ceil-log convention, including zero modes, without a positivity claim.
shellLE589 : Nat → Nat → Bool
shellLE589 zero n = true
shellLE589 (suc m) zero = false
shellLE589 (suc m) (suc n) = shellLE589 m n

shellLETrue589 : ∀ m n → shellLE589 m n ≡ true → m Nat.≤ n
shellLETrue589 zero n proof = Nat.z≤n
shellLETrue589 (suc m) zero ()
shellLETrue589 (suc m) (suc n) proof =
  Nat.s≤s (shellLETrue589 m n proof)

shellLEFalse589 : ∀ m n → shellLE589 m n ≡ false → n Nat.< m
shellLEFalse589 zero n ()
shellLEFalse589 (suc m) zero proof = Nat.s≤s Nat.z≤n
shellLEFalse589 (suc m) (suc n) proof =
  Nat.s≤s (shellLEFalse589 m n proof)

deepFarLow589 deepHighHigh589 : Physical.PhysicalTriadIncidence → Bool
deepFarLow589 tau = shellLE589
  (3 Nat.* (Shell.shellIndex (Physical.p tau) Nat.⊓ Shell.shellIndex (Physical.q tau)))
  (2 Nat.* (Shell.shellIndex (Physical.p tau) Nat.⊔ Shell.shellIndex (Physical.q tau)))
deepHighHigh589 tau = shellLE589
  (5 Nat.* Shell.shellIndex (Physical.k tau))
  (4 Nat.* (Shell.shellIndex (Physical.p tau) Nat.⊓ Shell.shellIndex (Physical.q tau)))

select589 : Bool → C3.Complex3 F → C3.Complex3 F
select589 true v = v
select589 false v = C3.complex3Zero F

complementary589 : (b : Bool) (v : C3.Complex3 F) →
  v ≡ C3.complex3Add (select589 b v) (select589 (not b) v)
complementary589 true v = sym (Field.complex3AddZeroRight v)
complementary589 false v = sym (R581.zeroLeft v)

masked589 :
  (Physical.PhysicalTriadIncidence → Bool) →
  (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
masked589 test value tau = select589 (test tau) (value tau)

splitFold589 :
  (test : Physical.PhysicalTriadIncidence → Bool)
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F)
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector value items ≡ C3.complex3Add
    (R224.foldVector (masked589 test value) items)
    (R224.foldVector (masked589 (λ tau → not (test tau)) value) items)
splitFold589 test value items = trans
  (R581.foldPointwiseEqual581 value
    (λ tau → C3.complex3Add
      (masked589 test value tau)
      (masked589 (λ t → not (test t)) value tau))
    (λ tau → complementary589 (test tau) (value tau)) items)
  (R225.foldPointwiseAdd (masked589 test value)
    (masked589 (λ tau → not (test tau)) value) items)

module LiteralOuterSplit
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) where

  fibre = Output.physicalOutputFiber (Audit.cutoff system) output
  forcing = R438.doubleWeightedProjectedForcingCell W S system
  amplitude = R440.weightedAmplitudeAggregate W S system fibre

  lowHigh = R224.foldVector (R581.lowHighCell581 forcing) fibre
  highLow = R224.foldVector (R581.highLowCell581 forcing) fibre
  highHigh = R224.foldVector (R581.highHighToLowCell581 forcing) fibre
  comparable = R224.foldVector (R581.comparableCell581 forcing) fibre

  farLowCell tau = C3.complex3Add
    (R581.lowHighCell581 forcing tau) (R581.highLowCell581 forcing tau)
  highHighCell = R581.highHighToLowCell581 forcing

  deepFL = R224.foldVector (masked589 deepFarLow589 farLowCell) fibre
  shoulderFL = R224.foldVector
    (masked589 (λ tau → not (deepFarLow589 tau)) farLowCell) fibre
  deepHH = R224.foldVector (masked589 deepHighHigh589 highHighCell) fibre
  shoulderHH = R224.foldVector
    (masked589 (λ tau → not (deepHighHigh589 tau)) highHighCell) fibre

  farLowDeepShoulder589 :
    R179.realHermitianCross amplitude (C3.complex3Add lowHigh highLow)
    ≡ R179.realHermitianCross amplitude deepFL
      + R179.realHermitianCross amplitude shoulderFL
  farLowDeepShoulder589 = trans
    (cong (R179.realHermitianCross amplitude)
      (trans
        (sym (R225.foldPointwiseAdd
          (R581.lowHighCell581 forcing) (R581.highLowCell581 forcing) fibre))
        (splitFold589 deepFarLow589 farLowCell fibre)))
    (R291.realCrossAddRight amplitude deepFL shoulderFL)

  highHighDeepShoulder589 :
    R179.realHermitianCross amplitude highHigh
    ≡ R179.realHermitianCross amplitude deepHH
      + R179.realHermitianCross amplitude shoulderHH
  highHighDeepShoulder589 = trans
    (cong (R179.realHermitianCross amplitude)
      (splitFold589 deepHighHigh589 highHighCell fibre))
    (R291.realCrossAddRight amplitude deepHH shoulderHH)

  farLowSignedCross589 : ℚ
  farLowSignedCross589 =
    R179.realHermitianCross amplitude (C3.complex3Add lowHigh highLow)

  highHighSignedCross589 : ℚ
  highHighSignedCross589 = R179.realHermitianCross amplitude highHigh

  comparableSignedCross589 : ℚ
  comparableSignedCross589 = R179.realHermitianCross amplitude comparable

  -- The LH/HL merge is addition, not the inner-slot symmetry theorem of R587.
  literalCommonCrossSplits589 :
    R440.fixedOutputPhysicalCommonCross W S system output
    ≡ (farLowSignedCross589 + highHighSignedCross589)
      + comparableSignedCross589
  literalCommonCrossSplits589 =
    trans
      (cong (R179.realHermitianCross amplitude)
        (R581.literalFoldToFourClassFolds581 forcing fibre))
      (trans
        (R291.realCrossAddRight amplitude
          (C3.complex3Add lowHigh highLow)
          (C3.complex3Add highHigh comparable))
        (trans
          (cong (λ x → farLowSignedCross589 + x)
            (R291.realCrossAddRight amplitude highHigh comparable))
          (sym (ℚP.+-assoc farLowSignedCross589
            highHighSignedCross589 comparableSignedCross589))))

  deepFarLowSigned589 = R179.realHermitianCross amplitude deepFL
  deepHighHighSigned589 = R179.realHermitianCross amplitude deepHH
  farLowShoulderSigned589 = R179.realHermitianCross amplitude shoulderFL
  highHighShoulderSigned589 = R179.realHermitianCross amplitude shoulderHH

  criticalCoreSigned589 : ℚ
  criticalCoreSigned589 =
    (farLowShoulderSigned589 + highHighShoulderSigned589)
      + comparableSignedCross589

  -- Payment-independent, literal version of R434.fixedOutputCrossMeaning.
  -- The core is the TWO shoulders plus CC, with their signs intact.
  literalCriticalConeDecomposition589 :
    R440.fixedOutputPhysicalCommonCross W S system output
    ≡ (deepFarLowSigned589 + deepHighHighSigned589) + criticalCoreSigned589
  literalCriticalConeDecomposition589 = trans literalCommonCrossSplits589
    (trans
      (cong (λ x → x + comparableSignedCross589)
        (cong₂ _+_ farLowDeepShoulder589 highHighDeepShoulder589))
      (solve (deepFarLowSigned589 ∷ farLowShoulderSigned589
        ∷ deepHighHighSigned589 ∷ highHighShoulderSigned589
        ∷ comparableSignedCross589 ∷ [])))

  -- This producer fixes the three signed masses to the literal finite fibre.
  -- It does not request an abstract decomposition or a same-cross equality.
  -- ED and Q still need physical meaning, and the constants still need a
  -- cutoff-uniform producer. In particular W currently has only swap symmetry.
  historicalWeldFromLiteralPayments589 :
    (ED Q cFL cHH cCore theta : ℚ) →
    0ℚ ≤ ED → 0ℚ ≤ theta → theta < 1 →
    deepFarLowSigned589 ≤ cFL * ED →
    deepHighHighSigned589 ≤ cHH * ED →
    criticalCoreSigned589 ≤ theta * Q + cCore * ED →
    R588.LiveHistoricalSignedCrossWeld588 W S system output
  historicalWeldFromLiteralPayments589
      ED Q cFL cHH cCore theta edNN thetaNN thetaLT flPaid hhPaid corePaid =
    record
      { historicalDecomposition588 = record
          { payment = record
              { energyDissipation = ED
              ; deepFarLowMass = deepFarLowSigned589
              ; deepHHMass = deepHighHighSigned589
              ; coreCompanionMass = Q
              ; coreGramDebt = criticalCoreSigned589
              ; deepFarLowCoefficient = cFL
              ; deepHHCoefficient = cHH
              ; coreEDCoefficient = cCore
              ; theta = theta
              ; energyDissipationNN = edNN
              ; thetaNN = thetaNN
              ; thetaStrictlyBelowOne = thetaLT
              ; deepFarLowPayment = flPaid
              ; deepHHPayment = hhPaid
              ; criticalCoreRelativeCovariance = corePaid
              }
          ; fixedOutputCross = R440.fixedOutputPhysicalCommonCross W S system output
          ; fixedOutputCrossMeaning = literalCriticalConeDecomposition589
          }
      ; sameSignedCross588 = refl
      }

  literalPaymentsBoundCommonCross589 :
    (ED Q cFL cHH cCore theta : ℚ) →
    0ℚ ≤ ED → 0ℚ ≤ theta → theta < 1 →
    deepFarLowSigned589 ≤ cFL * ED →
    deepHighHighSigned589 ≤ cHH * ED →
    criticalCoreSigned589 ≤ theta * Q + cCore * ED →
    R440.fixedOutputPhysicalCommonCross W S system output
      ≤ theta * Q + ((cFL + cHH) + cCore) * ED
  literalPaymentsBoundCommonCross589
      ED Q cFL cHH cCore theta edNN thetaNN thetaLT flPaid hhPaid corePaid =
    R588.liveCommonCrossBelowHistoricalCriticalConeBudget588
      (historicalWeldFromLiteralPayments589
        ED Q cFL cHH cCore theta edNN thetaNN thetaLT flPaid hhPaid corePaid)
