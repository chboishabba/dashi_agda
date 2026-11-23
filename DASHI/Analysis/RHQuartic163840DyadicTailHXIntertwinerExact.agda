module DASHI.Analysis.RHQuartic163840DyadicTailHXIntertwinerExact where

------------------------------------------------------------------------
-- RH / GRH P0: ACTUAL 163840 q-TAIL MEASURE -> DYADIC-15 CHART;
-- SOURCE H_X -> H_T CHAR INTERTWINER, NO MISATTRIBUTED MONSTER ACTION.
--
-- ORIGINAL SOURCE OWNERS:
--   Lean quarticFour signed FourierMass & NMu: physical r=t/16.
--   Lean FourthOrderQuotient: original combined even cosine transform.
--   Zeta23 GammaFacts.mu: real even monotone; GammaFactsChiProof: Stirling.
--   RiemannG2CanonicalHXToHTCompilerExact: exp(i(b-t)u) identity,
--       CONDITIONAL on an inhabited RiemannComplexCharacterExtension.
--   RiemannCanonicalComplexCharacterAttachmentExact: carrier attachment.
--   NonArchimedeanMonster3BActionSeparationExact: actual dyadic 2^15
--       action order at n=17, STRICTLY NOT a Monster 3B element.
--   DASHIQuantumLikeEntropyOscillatorExact: actual 15-bit capacity.
--
-- NEW analytic calculation (independent local SymPy, not Agda-real):
--   q>8, v=(8/q)^5, q^-6 dq=-dv/(5*8^5).
--   v=(k+theta)/32768; k in 0..32767, theta in [0,1).
--   q=16 <-> v=1/32 <-> boundary k=1024,theta=0.
--   Integral mass ratio q>16 / q>8 = 1/32.
--
-- This module pins existing typed source number and action owners;
-- it does NOT promote a 2^15 capacity to an RH group action.  The
-- real positive chart, its Jacobian, measured density and actual zeros
-- remain in the external analytic/local-SymPy proof ledger.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.NonArchimedeanMonster3BActionSeparationExact as Dyadic
import DASHI.Biology.DASHIQuantumLikeEntropyOscillatorExact as Capacity
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as HX
import DASHI.Analysis.RiemannAristotlePoleNearTranslationModulationIntertwinerExact as HT
import DASHI.Analysis.RiemannG2CanonicalHXToHTCompilerExact as HXCompiler
import DASHI.Analysis.RHQuartic128Monster3BSSPSignedC2IntertwinerExact as Finite128
import DASHI.Analysis.RHQuartic128SevenBitFaceCechGluingExact as RH128

sourceDyadicBits : Nat
sourceDyadicBits = 15

sourceDyadicCapacity : Nat
sourceDyadicCapacity = Capacity.binaryCapacityFifteen

sourceDyadicCapacityIs32768 : sourceDyadicCapacity ≡ 32768
sourceDyadicCapacityIs32768 = Capacity.binaryCapacityFifteenIs32768

tailCutoff : Nat
tailCutoff = 8

tailWeightExponent : Nat
tailWeightExponent = 5

tailCutoffFifthPower : Nat
tailCutoffFifthPower = 8 * 8 * 8 * 8 * 8

tailCutoffFifthPowerIsSourceDyadicCapacity :
  tailCutoffFifthPower ≡ sourceDyadicCapacity
tailCutoffFifthPowerIsSourceDyadicCapacity = refl

tailDenominator : Nat
tailDenominator = tailWeightExponent * tailCutoffFifthPower

tailDenominatorIs163840 : tailDenominator ≡ 163840
tailDenominatorIs163840 = refl

sameIntegerAsExistingOrder17 :
  Dyadic.sourceOddTimesThreeOrderAt17 ≡ sourceDyadicCapacity
sameIntegerAsExistingOrder17 = refl

fiveTimesExistingOrder17IsTailDenominator :
  5 * Dyadic.sourceOddTimesThreeOrderAt17 ≡ tailDenominator
fiveTimesExistingOrder17IsTailDenominator = refl

crossingAtSixteenCellIndex : Nat
crossingAtSixteenCellIndex = 1024

crossingToTotalFactor : Nat
crossingToTotalFactor = 32

crossingScaledBackToDyadicCapacity :
  crossingAtSixteenCellIndex * crossingToTotalFactor
    ≡ sourceDyadicCapacity
crossingScaledBackToDyadicCapacity = refl

otherTailCellCount : Nat
otherTailCellCount = 31744

partitionDyadicCellsAtOriginalZeroOrdinateCrossing :
  crossingAtSixteenCellIndex + otherTailCellCount
    ≡ sourceDyadicCapacity
partitionDyadicCellsAtOriginalZeroOrdinateCrossing = refl

-- The exact q=16 ordinate crossing is a distinguished boundary,
-- not a cell interior and not a deleted neutral value.
data TailCrossingStratum : Set where
  beyondSixteen : TailCrossingStratum
  exactSixteenBoundary : TailCrossingStratum
  betweenEightAndSixteen : TailCrossingStratum

-- Import-only reuse: character-product proof terms do not become
-- new Monster phase/physical-group action proofs.
reuseOriginalConditionalAnalyticHT :
  {analytic : Analytic.AnalyticSubstrate} →
  HX.RiemannComplexCharacterExtension analytic →
  HT.TargetTranslationModulationIntertwiner
reuseOriginalConditionalAnalyticHT = HXCompiler.canonicalHXToHT

finiteSevenAxesActualDonor :
  (mask state : RH128.BinarySeven) →
  Finite128.encode (Finite128.maskAct mask state)
    ≡ Finite128.actOnNativeSignedX6 mask (Finite128.encode state)
finiteSevenAxesActualDonor = Finite128.encodeIntertwinesAllSeven

record AnalyticActionAndTailBoundary : Set where
  constructor analytic-action-and-tail-boundary
  field
    actualSourceDyadicOrderIsReused : Bool
    fullPositiveTailJacobianProvedInLocalSymPy : Bool
    boundaryAtSixteenIsRetained : Bool
    continuousResidualRequiredForExactRecovery : Bool
    canonicalHXToHTRequiresHXSourceAttachment : Bool
    originalQuarticSevenPhysicalInvolutionsConstructed : Bool
    sourceDyadicOrderIsMonsterThreeBAction : Bool
    strictSignedRHZeroMarginEstablishedHere : Bool

canonicalAnalyticActionAndTailBoundary : AnalyticActionAndTailBoundary
canonicalAnalyticActionAndTailBoundary =
  analytic-action-and-tail-boundary
    true true true true true false false false
