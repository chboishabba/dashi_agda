module DASHI.Arithmetic.TwinPrimeFractranResidualHyperfabricExact where

------------------------------------------------------------------------
-- CT15: FRACTRAN PRIME VALUATIONS + CONSUMER-INDEXED RETAINED FIBRE.
--
-- PRIOR OWNERS (IMPORT AND REUSE, DO NOT DUPLICATE):
--  * Conway 1987 FRACTRAN: ordered fraction-register transitions.
--  * SignedSSPFRACTRANWeaveExact: the actual fifteen Ogg prime lanes;
--    in particular SSP 7, 47, 59, and signed multiplicity values.
--  * FractranCOL: a DIFFERENT concrete five-lane evaluator (2,3,5,7,11).
--  * VerifiedFractranCrankPipeline: full prime-exponent machine contract.
--  * SSP15FractranCompression: label-only, lossless residual and
--    transition-congruence are distinct obligations.
--  * TwinPrimeNat270PeriodResidualBidiExact: exact Nat <-> (q,r).
--  * TwinPrimeTernary270IbrahimSurvivorCollisionExact: source-owned
--    59 vs 329 certified twin-consumer collision.
--  * ConsumerIndexedResidualRefinementExact / CoarseFineRelativeFibreExact
--    and PickoverConsumerResidualFibreBridgeExact (sin-9999):
--    consumer-indexed necessity, strict refinement and exact reopening.
--
-- This module closes the concrete consumer-refinement and SSP-valuation
-- *witness* obligations. It does NOT claim the five-lane executor can
-- process 47/59, that an SSP geometric label is a full FRACTRAN trace,
-- that a FRACTRAN test proves cofinal twin primes, or a Monster 3B
-- representation. Source-written; kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Nat.DivMod using (_%_; _/_)
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Correlation
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Mangoldt
open import Data.Product using (_×_)
open import Agda.Builtin.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeTernary270IbrahimSurvivorCollisionExact as Witness
import DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact as Twin
import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Repair
import DASHI.Analysis.PickoverConsumerResidualFibreBridgeExact as Pickover
import DASHI.Interop.VerifiedFractranCrankPipeline as Machine
import DASHI.Combinatorics.SSP15FractranCompression as Compression
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeWeilActualCorrelationPartitionExact as Fold
import DASHI.Arithmetic.TwinPrimeMangoldtPrimeErrorFiniteSplitExact as Split
import DASHI.Programmes.FRACDASHNumericInterpreterTargetExact as Interpreter

------------------------------------------------------------------------
-- 59 = 59, versus 329 = 7 * 47: both SSP primes really exist in
-- the original fifteen-lane atlas. These are explicit, local
-- factorisation certificates, NOT an invented global valuation oracle.
------------------------------------------------------------------------

fiftyNineSSPValuation : Signed.SSPValuation
fiftyNineSSPValuation Signed.ssp59 = Signed.positiveMultiplicity 1
fiftyNineSSPValuation _ = Signed.zeroMultiplicity

threeTwentyNineSSPValuation : Signed.SSPValuation
threeTwentyNineSSPValuation Signed.ssp7 =
  Signed.positiveMultiplicity 1
threeTwentyNineSSPValuation Signed.ssp47 =
  Signed.positiveMultiplicity 1
threeTwentyNineSSPValuation _ = Signed.zeroMultiplicity

fiftyNinePrimeLane :
  Signed.primeValue Signed.ssp59 ≡ 59
fiftyNinePrimeLane = refl

sevenFortySevenFactorisation :
  Signed.primeValue Signed.ssp7 *
    Signed.primeValue Signed.ssp47 ≡ 329
sevenFortySevenFactorisation = refl

fiftyNineValuationAtFiftyNine :
  fiftyNineSSPValuation Signed.ssp59
    ≡ Signed.positiveMultiplicity 1
fiftyNineValuationAtFiftyNine = refl

threeTwentyNineValuationAtSeven :
  threeTwentyNineSSPValuation Signed.ssp7
    ≡ Signed.positiveMultiplicity 1
threeTwentyNineValuationAtSeven = refl

threeTwentyNineValuationAtFortySeven :
  threeTwentyNineSSPValuation Signed.ssp47
    ≡ Signed.positiveMultiplicity 1
threeTwentyNineValuationAtFortySeven = refl

valAtSevenSeparatesInputs :
  fiftyNineSSPValuation Signed.ssp7
    ≡ threeTwentyNineSSPValuation Signed.ssp7 → ⊥
valAtSevenSeparatesInputs ()

valAtFiftyNineSeparatesInputs :
  fiftyNineSSPValuation Signed.ssp59
    ≡ threeTwentyNineSSPValuation Signed.ssp59 → ⊥
valAtFiftyNineSeparatesInputs ()

-- The certificate pairs a concrete input numeral with its genuinely
-- factored SSP valuation. It is evidence for precisely these two
-- inputs. It does not pretend all numbers factor within SSP15.
data LocalSSPFactorReceipt : Nat → Signed.SSPValuation → Set where
  genuine59Receipt :
    LocalSSPFactorReceipt 59 fiftyNineSSPValuation
  composite329Receipt :
    LocalSSPFactorReceipt 329 threeTwentyNineSSPValuation

------------------------------------------------------------------------
-- Reuse exact original PERIOD CODEC as the coarse/fine fibre.
-- The period index is unbounded and cannot be erased by 270 wheel.
------------------------------------------------------------------------

arithmeticCoarseFineFibre : Fibre.CoarseFineReopening Nat
arithmeticCoarseFineFibre = record
  { Coarse = Fin 270
  ; RelativeFine = Nat
  ; coarse = Period.finiteResidue270
  ; relativeFine = λ n →
      Period.periodIndex (Period.encodeNatPeriod270 n)
  ; reopen = λ residue period → toℕ residue + period * 270
  ; reopenExact = Period.decodeEncodeNatPeriod270
  }

fullArithmeticObserver : Nat → Fin 270 × Nat
fullArithmeticObserver =
  Fibre.coarseFineObserver arithmeticCoarseFineFibre

fullArithmeticReopening :
  (n : Nat) →
  Fibre.reopen arithmeticCoarseFineFibre
    (Fibre.coarse arithmeticCoarseFineFibre n)
    (Fibre.relativeFine arithmeticCoarseFineFibre n)
    ≡ n
fullArithmeticReopening =
  Fibre.reopenExact arithmeticCoarseFineFibre

-- This is consumer-indexed sufficient for ACTUAL twin-primality, not
-- merely a reconstruction of one abstract status or residue label.
actualTwinResidualRepair :
  Repair.ResidualRepair
    (Fibre.coarse arithmeticCoarseFineFibre)
    (Fibre.relativeFine arithmeticCoarseFineFibre)
    Twin.twinStartBool
actualTwinResidualRepair = record
  { jointSufficient =
      Repair.separatingObserverIsSufficientForEveryConsumer
        (Fibre.coarseFineObserverSeparating arithmeticCoarseFineFibre)
        Twin.twinStartBool
  }

-- Reuse the ORIGINAL 59/329 primality collision, now through the
-- precise consumer-relevant collision owner from sin-9999.
actualTwinCoarseCollision :
  Repair.ConsumerRelevantCollision
    (Fibre.coarse arithmeticCoarseFineFibre)
    Twin.twinStartBool
actualTwinCoarseCollision = record
  { left = 59
  ; right = 329
  ; sameSurface = refl
  ; differentOutcome = Witness.natTwinConsumerDistinguishes59And329
  }

-- A correct residual repair MUST distinguish these two inputs.
-- This is the nontrivial necessity statement independent of the
-- particular period representation chosen by this module.
anyActualTwinResidualMustSeparate :
  {Residual : Set} →
  (residual : Nat → Residual) →
  Repair.ResidualRepair
    (Fibre.coarse arithmeticCoarseFineFibre)
    residual Twin.twinStartBool →
  residual 59 ≡ residual 329 → ⊥
anyActualTwinResidualMustSeparate residual correct same =
  Repair.residualMustSeparateRelevantCollision
    actualTwinCoarseCollision correct same

-- Concrete certified strict refinement: original Pickover
-- consumer-indexed theorem, specialising to prime pairs.
twinResidualStrictRefinement :
  Repair.ConsumerSufficient
    (Fibre.coarse arithmeticCoarseFineFibre)
    Twin.twinStartBool → ⊥
twinResidualStrictRefinement supposedlySufficient =
  Repair.coarseCollisionBlocksSufficiency
    actualTwinCoarseCollision supposedlySufficient

-- An exact full arithmetic residual is sufficient and necessarily
-- finer than the bare finite wheel for the twin consumer. This is
-- an inhabited STRICT refinement theorem, not an analytic estimate.
twinFibreReallyRefinesWheel :
  Repair.ResidualRepair
    (Fibre.coarse arithmeticCoarseFineFibre)
    (Fibre.relativeFine arithmeticCoarseFineFibre)
    Twin.twinStartBool
twinFibreReallyRefinesWheel = actualTwinResidualRepair

------------------------------------------------------------------------
-- FRACTRAN COMPILER BOUNDARY: prime-register machines preserve their
-- exact arithmetic meaning only with a concrete faithful readout.
--
-- Existing VerifiedFractranCrankPipeline.FractranMachine supplies
-- per-lane exponent laws; SSP15FractranCompression.SSP15ResidualCodec
-- supplies a lossless EV5 label+residual codec. NEITHER alone is a
-- full Nat -> unrestricted all-prime valuation compiler.
--
-- A machine may have a twin evaluator after a certified state-to-Nat
-- readout; correctness comes from the actual source TwinPrimeAt.
------------------------------------------------------------------------

record SoundFractranTwinReadout
    (F : Machine.FractranMachine)
    (encodeNat : Nat → Machine.State F) : Set₁ where
  field
    decodeNat : Machine.State F → Nat
    decodeEncode : (n : Nat) → decodeNat (encodeNat n) ≡ n
    machineTwin : Machine.State F → Bool
    machineTwinCorrect :
      (state : Machine.State F) →
      machineTwin state ≡ Twin.twinStartBool (decodeNat state)

open SoundFractranTwinReadout public

certifiedFractranTwinOutput :
  (F : Machine.FractranMachine)
  (encodeNat : Nat → Machine.State F)
  (sound : SoundFractranTwinReadout F encodeNat) →
  (n : Nat) →
  machineTwin sound (encodeNat n) ≡ Twin.twinStartBool n
certifiedFractranTwinOutput F encodeNat sound n
  rewrite decodeEncode sound n =
    machineTwinCorrect sound (encodeNat n)

-- A finite SSP phase or a bare five-prime EV5 projection can be
-- treated as the above machine ONLY after somebody constructs the
-- required sound instance. No such instance is fabricated here.

------------------------------------------------------------------------
-- CONCRETE ACTUAL FRACTRAN DENOMINATOR GUARDS.
--
-- A rule with denominator 7 can fire on 329 because 7 | 329,
-- but not on 59. The same holds for denominator 47. This is
-- direct integer divisibility (the arithmetic FRACTRAN guard),
-- not an inference from Ogg labels or from a prime-output sequence.
--
-- FIRST-APPLICABLE priority, 14-fraction PRIMEGAME runtime and
-- machine registration are separate verified-program obligations.
------------------------------------------------------------------------

sevenDenominatorEnabledOn329 : 329 % 7 ≡ 0
sevenDenominatorEnabledOn329 = refl

sevenDenominatorRemainderOn59 : 59 % 7 ≡ 3
sevenDenominatorRemainderOn59 = refl

fortySevenDenominatorEnabledOn329 : 329 % 47 ≡ 0
fortySevenDenominatorEnabledOn329 = refl

fortySevenDenominatorRemainderOn59 : 59 % 47 ≡ 12
fortySevenDenominatorRemainderOn59 = refl

sevenDenominatorCannotFireOn59 : 59 % 7 ≡ 0 → ⊥
sevenDenominatorCannotFireOn59 ()

fortySevenDenominatorCannotFireOn59 : 59 % 47 ≡ 0 → ⊥
fortySevenDenominatorCannotFireOn59 ()

------------------------------------------------------------------------
-- Direct PICKOVER source theorem specialization. Not only generic
-- analogy: inhabit its existing SignedPhaseFibre using the
-- proof-bearing actual prime consumer and exact period residual.
------------------------------------------------------------------------

pickoverPatternForActualTwinConsumer :
  Pickover.SignedPhaseFibre Nat (Fin 270) Nat Bool
    (Fibre.coarse arithmeticCoarseFineFibre)
    (Fibre.relativeFine arithmeticCoarseFineFibre)
    Twin.twinStartBool
pickoverPatternForActualTwinConsumer = record
  { signedRepair = actualTwinResidualRepair }

pickoverNecessityOfTwinPeriod :
  Fibre.relativeFine arithmeticCoarseFineFibre 59
    ≡ Fibre.relativeFine arithmeticCoarseFineFibre 329 →
  ⊥
pickoverNecessityOfTwinPeriod =
  Pickover.residualNeededForSignedCollision
    actualTwinCoarseCollision
    pickoverPatternForActualTwinConsumer

-- The concrete original Weil/Mangoldt producer can be transported
-- through this SAME exact arithmetic fibre. This is a genuine
-- pointwise consumer theorem, not a symbol-label comparison.
actualMangoldtPairConsumer :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Nat → Weil.WeilTestSpace.Scalar space
actualMangoldtPairConsumer space arithmetic mangoldt =
  Correlation.pairCorrelationAtNat
    (Mangoldt.actualMangoldtPair space arithmetic mangoldt)

actualMangoldtConsumerResidualRepair :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Repair.ResidualRepair
    (Fibre.coarse arithmeticCoarseFineFibre)
    (Fibre.relativeFine arithmeticCoarseFineFibre)
    (actualMangoldtPairConsumer space arithmetic mangoldt)
actualMangoldtConsumerResidualRepair space arithmetic mangoldt =
  record
    { jointSufficient =
        Repair.separatingObserverIsSufficientForEveryConsumer
          (Fibre.coarseFineObserverSeparating arithmeticCoarseFineFibre)
          (actualMangoldtPairConsumer space arithmetic mangoldt)
    }

actualMangoldtConsumerReopens :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (n : Nat) →
  actualMangoldtPairConsumer space arithmetic mangoldt
    (Fibre.reopen arithmeticCoarseFineFibre
      (Fibre.coarse arithmeticCoarseFineFibre n)
      (Fibre.relativeFine arithmeticCoarseFineFibre n))
    ≡
  actualMangoldtPairConsumer space arithmetic mangoldt n
actualMangoldtConsumerReopens space arithmetic mangoldt n =
  cong (actualMangoldtPairConsumer space arithmetic mangoldt)
    (fullArithmeticReopening n)

-- Opening a finite wheel cell plus keeping the period reconstructs
-- every pointwise Mangoldt weight, but it does NOT deliver a uniform
-- positive estimate of a sum over unbounded scales. In particular
-- it does not prove cofinalObservedSeparationImpliesTwinInfinitude's
-- premise. No numeric/SSP/Monster identity promotion.

------------------------------------------------------------------------
-- FINITE WINDOW/REFINEMENT AXIS: genuinely original Mangoldt
-- correlation over all Nat positions, read by exact q,r fibres.
-- This is the existing ordered finite-sum BIDI, specialised rather
-- than duplicated. It works on ANY finite window and keeps the
-- original scalar/term order. The prime-only / proper-power split
-- stays the already-owned original M15 theorem.
------------------------------------------------------------------------

actualMangoldtWindowFibreForward :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (start count : Nat) →
  Sum.sumDecodedInterval (Fold.weilAdditive space)
    (Correlation.pairCorrelationAtPeriod
      (Mangoldt.actualMangoldtPair space arithmetic mangoldt))
    start count
  ≡
  Sum.sumInterval (Fold.weilAdditive space)
    (actualMangoldtPairConsumer space arithmetic mangoldt)
    start count
actualMangoldtWindowFibreForward space arithmetic mangoldt start count =
  Sum.pairFiniteSumBidiForward
    (Fold.weilAdditive space)
    (Mangoldt.actualMangoldtPair space arithmetic mangoldt)
    start count

actualMangoldtWindowFibreBackward :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (start count : Nat) →
  Sum.sumInterval (Fold.weilAdditive space)
    (actualMangoldtPairConsumer space arithmetic mangoldt)
    start count
  ≡
  Sum.sumDecodedInterval (Fold.weilAdditive space)
    (Correlation.pairCorrelationAtPeriod
      (Mangoldt.actualMangoldtPair space arithmetic mangoldt))
    start count
actualMangoldtWindowFibreBackward space arithmetic mangoldt start count =
  Sum.pairFiniteSumBidiBackward
    (Fold.weilAdditive space)
    (Mangoldt.actualMangoldtPair space arithmetic mangoldt)
    start count

-- This source-term correspondence holds FOR ALL finite window sizes.
-- Its quantified length is unbounded, but it does not assert any
-- prime-pair count grows or any correlation stays positive.
actualMangoldtFibreWindowPrimeErrorSplit :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (laws : Split.AdditiveInterchangeLaws space)
  (start count : Nat) →
  Sum.sumDecodedInterval (Fold.weilAdditive space)
    (Correlation.pairCorrelationAtPeriod
      (Mangoldt.actualMangoldtPair space arithmetic mangoldt))
    start count
  ≡
  Weil.WeilTestSpace._+S_ space
    (Sum.sumInterval (Fold.weilAdditive space)
      (Split.primeOnlyAtNat space arithmetic mangoldt) start count)
    (Sum.sumInterval (Fold.weilAdditive space)
      (Split.nonPrimeErrorAtNat space arithmetic mangoldt) start count)
actualMangoldtFibreWindowPrimeErrorSplit
    space arithmetic mangoldt laws start count =
  trans
    (actualMangoldtWindowFibreForward space arithmetic mangoldt
      start count)
    (Split.finiteMangoldtPrimeErrorSplit
      space arithmetic mangoldt laws start count)

------------------------------------------------------------------------
-- ACTUAL TWO-RULE NUMERIC FRACTRAN EXECUTION, importing the original
-- "first applicable" operational semantics. This is intentionally a
-- concrete, BOUNDED subprogram [1/7,1/47]. It is NOT the fourteen-
-- fraction Conway PRIMEGAME, and does not decide all primes.
------------------------------------------------------------------------

data LocalDivisionRule : Set where
  divideSeven : LocalDivisionRule
  divideFortySeven : LocalDivisionRule

localFractionEnabled : Nat → LocalDivisionRule → Set
localFractionEnabled n divideSeven = n % 7 ≡ 0
localFractionEnabled n divideFortySeven = n % 47 ≡ 0

localFractionStep : Nat → LocalDivisionRule → Nat
localFractionStep n divideSeven = n / 7
localFractionStep n divideFortySeven = n / 47

localFractranProgram : List LocalDivisionRule
localFractranProgram =
  divideSeven ∷ divideFortySeven ∷ []

-- The source interpreter chooses 1/7 FIRST, yielding 47 on 329.
-- This is a real step witness, not a Boolean metadata receipt.
threeTwentyNineFractranChoosesSeven :
  Interpreter.FirstApplicableStep
    localFractionEnabled localFractionStep
    localFractranProgram 329 47
threeTwentyNineFractranChoosesSeven =
  Interpreter.choose-head sevenDenominatorEnabledOn329

-- 59 has neither 7 nor 47 denominator enabled, so this PARTICULAR
-- two-rule program cannot make an integer step on input 59.
fiftyNineHasNoLocalFractranStep :
  {next : Nat} →
  Interpreter.FirstApplicableStep
    localFractionEnabled localFractionStep
    localFractranProgram 59 next →
  ⊥
fiftyNineHasNoLocalFractranStep
  (Interpreter.choose-head sevenEnabled) =
  sevenDenominatorCannotFireOn59 sevenEnabled
fiftyNineHasNoLocalFractranStep
  (Interpreter.skip-head skipped
    (Interpreter.choose-head fortySevenEnabled)) =
  fortySevenDenominatorCannotFireOn59 fortySevenEnabled
fiftyNineHasNoLocalFractranStep
  (Interpreter.skip-head _ (Interpreter.skip-head _ ()))
