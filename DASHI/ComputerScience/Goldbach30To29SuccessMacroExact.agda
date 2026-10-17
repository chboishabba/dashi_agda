module DASHI.ComputerScience.Goldbach30To29SuccessMacroExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.Goldbach29Signed369VendorBridgeExact as Bridge

------------------------------------------------------------------------
-- GOLDBACH30 -> GOLDBACH29 SUCCESS MACRO
--
-- External construction authority:
--   Mike Dupont / meta-introspector, meta-introspector/aok
--   commit c168223e96f7acc6179044f2a365a92db2e350c3
--   Cryptids/Goldbach30/Program.lean
--   Cryptids/Goldbach29/Program.lean
--
-- Both source files prove their own FRACTRAN-step/abstract-step theorem
-- `fstep_enc`.  This module does NOT copy those AGPL source files and does not
-- claim their Lean theorem as an Agda theorem.  DASHI independently reconstructs
-- only the success-tail register semantics needed to compare the two published
-- rule sequences.
--
-- EXACT SUCCESS-BRANCH CONTRACT
-- -----------------------------
-- In the published `NT_B` case, the success branch is selected only after the
-- earlier restoration branches have failed.  On the source-reachable success
-- boundary this gives
--
--   a = suc aTail,  f = 1,  s = 0,  g = 0.
--
-- `c` may be zero: the first real Goldbach success is `(a,b,c)=(2,2,0)`.
-- Positive `a` guarantees that the transfer loop increments c before the final
-- c-consuming rule.  `d/e/h/m` are not inspected by the success-tail rules and
-- are therefore retained parametrically.
--
-- Two tempting broader contracts are intentionally rejected:
--   * requiring c>0 would exclude the real first success;
--   * allowing f>1 is not source-faithful for Goldbach29, because a positive
--     verdict remains after staging and the machine re-enters its success loop.
------------------------------------------------------------------------

record SuccessEntry : Set where
  constructor successEntry
  field
    aTail : Nat
    b : Nat
    c : Nat
    d : Nat
    e : Nat
    h : Nat
    m : Nat

open SuccessEntry public

/-- The actual tested `a` register at a success entry. -/
a : SuccessEntry → Nat
a x = suc (aTail x)

record SuccessRegisters : Set where
  constructor successRegisters
  field
    regA : Nat
    regB : Nat
    regC : Nat
    regD : Nat
    regE : Nat
    regF : Nat
    regS : Nat
    regG : Nat
    regH : Nat
    regM : Nat

open SuccessRegisters public

successEntryRegisters : SuccessEntry → SuccessRegisters
successEntryRegisters x =
  successRegisters
    (a x)
    (b x)
    (c x)
    (d x)
    (e x)
    1
    0
    0
    (h x)
    (m x)

------------------------------------------------------------------------
-- Old Goldbach30 macro.
--
-- NT_B*f -> SA consumes the unique verdict f=1.  Each unit of positive a is
-- transferred by the SA*a -> SB*b*c ; SB -> SA pair.  Because at least one a
-- unit is transferred, c is positive by the time the terminal SA*c rule is
-- reached even when entry c=0.  That rule consumes one c, creates a=2,d+=2,
-- and restores f=1.  s and g remain zero; d/e/h/m are carried as published.
--
-- The first argument is `aTail`; actual entry a is `suc aTail`.  The zero case
-- therefore still performs one a-transfer before the terminal rule.
------------------------------------------------------------------------

oldSuccessTerminalFrom :
  Nat → Nat → Nat → Nat → Nat → Nat → Nat →
  SuccessRegisters
oldSuccessTerminalFrom zero b c d e h m =
  successRegisters 2 (suc b) c (d + 2) e 1 0 0 h m
oldSuccessTerminalFrom (suc aTail) b c d e h m =
  oldSuccessTerminalFrom aTail (suc b) (suc c) d e h m

oldSuccessTerminal : SuccessEntry → SuccessRegisters
oldSuccessTerminal x =
  oldSuccessTerminalFrom
    (aTail x) (b x) (c x) (d x) (e x) (h x) (m x)

------------------------------------------------------------------------
-- New Goldbach29 macro.
--
-- Each positive a-unit is transferred by
--
--   NT_B*f*a -> SB*b*c ; SB -> NT_B*f
--
-- with the unique verdict f=1 consumed and restored on every pair.  At a=0,
-- NT_B*f -> NT2_B*a*b and NT2_B -> NT_B consume that verdict; the existing
-- NT_B*b*c -> RA_A transition can then fire because the positive-a transfer
-- has made c positive, and it restores f=1.  The macro-boundary registers are
-- exactly the Goldbach30 registers.
------------------------------------------------------------------------

newSuccessTerminalFrom :
  Nat → Nat → Nat → Nat → Nat → Nat → Nat →
  SuccessRegisters
newSuccessTerminalFrom zero b c d e h m =
  successRegisters 2 (suc b) c (d + 2) e 1 0 0 h m
newSuccessTerminalFrom (suc aTail) b c d e h m =
  newSuccessTerminalFrom aTail (suc b) (suc c) d e h m

newSuccessTerminal : SuccessEntry → SuccessRegisters
newSuccessTerminal x =
  newSuccessTerminalFrom
    (aTail x) (b x) (c x) (d x) (e x) (h x) (m x)

successTerminalFromAgree :
  (aTail b c d e h m : Nat) →
  oldSuccessTerminalFrom aTail b c d e h m
  ≡
  newSuccessTerminalFrom aTail b c d e h m
successTerminalFromAgree zero b c d e h m = refl
successTerminalFromAgree (suc aTail) b c d e h m =
  successTerminalFromAgree aTail (suc b) (suc c) d e h m

successTerminalRegistersAgree :
  (x : SuccessEntry) →
  oldSuccessTerminal x ≡ newSuccessTerminal x
successTerminalRegistersAgree x =
  successTerminalFromAgree
    (aTail x) (b x) (c x) (d x) (e x) (h x) (m x)

------------------------------------------------------------------------
-- Source-reachable guard receipts.
------------------------------------------------------------------------

successEntryAIsPositiveByConstruction :
  (x : SuccessEntry) →
  a x ≡ suc (aTail x)
successEntryAIsPositiveByConstruction x = refl

successEntryVerdictIsExactlyOne :
  (x : SuccessEntry) →
  regF (successEntryRegisters x) ≡ 1
successEntryVerdictIsExactlyOne x = refl

successEntryRestoreRegistersAreZero :
  (x : SuccessEntry) →
  (regS (successEntryRegisters x) ≡ 0)
  ×
  (regG (successEntryRegisters x) ≡ 0)
successEntryRestoreRegistersAreZero x = refl , refl

successTerminalVerdictIsExactlyOne :
  (x : SuccessEntry) →
  regF (oldSuccessTerminal x) ≡ 1
successTerminalVerdictIsExactlyOne (successEntry zero b c d e h m) = refl
successTerminalVerdictIsExactlyOne (successEntry (suc aTail) b c d e h m) =
  successTerminalVerdictIsExactlyOne
    (successEntry aTail (suc b) (suc c) d e h m)

/-- Regression for the real first success: entry c=0 is intentionally admitted. -/
firstGoldbachSuccessEntry : SuccessEntry
firstGoldbachSuccessEntry =
  successEntry 1 2 0 0 0 0 0

firstGoldbachSuccessOldTerminal :
  oldSuccessTerminal firstGoldbachSuccessEntry
  ≡ successRegisters 2 4 1 2 0 1 0 0 0 0
firstGoldbachSuccessOldTerminal = refl

firstGoldbachSuccessNewTerminal :
  newSuccessTerminal firstGoldbachSuccessEntry
  ≡ successRegisters 2 4 1 2 0 1 0 0 0 0
firstGoldbachSuccessNewTerminal = refl

------------------------------------------------------------------------
-- Declared consumers.
------------------------------------------------------------------------

NextEvenBoundary : Set
NextEvenBoundary = Nat × (Nat × Nat)

nextEvenBoundaryConsumer : SuccessRegisters → NextEvenBoundary
nextEvenBoundaryConsumer r = regA r , (regB r , regC r)

verdictGuardConsumer : SuccessRegisters → Nat
verdictGuardConsumer = regF

successNextEvenConsumerPreserved :
  (x : SuccessEntry) →
  nextEvenBoundaryConsumer (oldSuccessTerminal x)
  ≡
  nextEvenBoundaryConsumer (newSuccessTerminal x)
successNextEvenConsumerPreserved x =
  cong nextEvenBoundaryConsumer (successTerminalRegistersAgree x)

successGoldbachVerdictConsumerPreserved :
  (x : SuccessEntry) →
  verdictGuardConsumer (oldSuccessTerminal x)
  ≡
  verdictGuardConsumer (newSuccessTerminal x)
successGoldbachVerdictConsumerPreserved x =
  cong verdictGuardConsumer (successTerminalRegistersAgree x)

------------------------------------------------------------------------
-- Static/dynamic Pareto consequence.
------------------------------------------------------------------------

oldSuccessExecutionLength : Nat → Nat
oldSuccessExecutionLength = Bridge.oldSuccessExecutionLength

newSuccessExecutionLength : Nat → Nat
newSuccessExecutionLength = Bridge.newSuccessExecutionLength

newSuccessExecutionLengthIsOneMore :
  (actualA : Nat) →
  newSuccessExecutionLength actualA ≡ suc (oldSuccessExecutionLength actualA)
newSuccessExecutionLengthIsOneMore = Bridge.newSuccessExecutionLengthIsOneMore

reachableSuccessExecutionLengthIsOneMore :
  (x : SuccessEntry) →
  newSuccessExecutionLength (a x)
  ≡ suc (oldSuccessExecutionLength (a x))
reachableSuccessExecutionLengthIsOneMore x =
  newSuccessExecutionLengthIsOneMore (a x)

record GoldbachSuccessMacroBoundary : Set where
  constructor goldbachSuccessMacroBoundary
  field
    terminalRegistersPreserved : Bool
    nextEvenBoundaryPreserved : Bool
    verdictGuardPreserved : Bool
    entryVerdictExactlyOne : Bool
    restoreRegistersZeroAtSuccess : Bool
    zeroCReachableSuccessCovered : Bool
    arbitraryPositiveVerdictClaimed : Bool
    arbitraryRestoreRegisterClaimed : Bool
    fractionCountReduced : Bool
    successMicrostepsReduced : Bool
    successMicrostepsIncreaseByOne : Bool
    wholeMachineBisimulationFollowsFromThisMacroAlone : Bool

canonicalGoldbachSuccessMacroBoundary : GoldbachSuccessMacroBoundary
canonicalGoldbachSuccessMacroBoundary =
  goldbachSuccessMacroBoundary
    true true true true true true false false true false true false
