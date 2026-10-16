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
-- We encode the success-entry guards structurally:
--   c = suc cTail   and   f = suc fTail.
-- Thus the final c-consuming and verdict-consuming rules are total on every
-- inhabitant of SuccessEntry.  All other registers are carried explicitly.
------------------------------------------------------------------------

record SuccessEntry : Set where
  constructor successEntry
  field
    a : Nat
    b : Nat
    cTail : Nat
    d : Nat
    e : Nat
    fTail : Nat
    s : Nat
    g : Nat
    h : Nat
    m : Nat

open SuccessEntry public

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
    (suc (cTail x))
    (d x)
    (e x)
    (suc (fTail x))
    (s x)
    (g x)
    (h x)
    (m x)

------------------------------------------------------------------------
-- Old Goldbach30 macro.
--
-- NT_B*f -> SA consumes one f.  Each unit of a is transferred by the
-- SA*a -> SB*b*c ; SB -> SA pair.  The terminal SA*c rule consumes one c,
-- creates a=2,d+=2 and restores f.  f therefore has its entry value again at
-- the macro boundary.
------------------------------------------------------------------------

oldSuccessTerminalFrom :
  Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
  SuccessRegisters
oldSuccessTerminalFrom zero b cTail d e fTail s g h m =
  successRegisters 2 b cTail (d + 2) e (suc fTail) s g h m
oldSuccessTerminalFrom (suc a) b cTail d e fTail s g h m =
  oldSuccessTerminalFrom a (suc b) (suc cTail) d e fTail s g h m

oldSuccessTerminal : SuccessEntry → SuccessRegisters
oldSuccessTerminal x =
  oldSuccessTerminalFrom
    (a x) (b x) (cTail x) (d x) (e x) (fTail x)
    (s x) (g x) (h x) (m x)

------------------------------------------------------------------------
-- New Goldbach29 macro.
--
-- Each a-unit is transferred by NT_B*f*a -> SB*b*c ; SB -> NT_B*f, so f is
-- restored after every pair.  At a=0, NT_B*f -> NT2_B*a*b and NT2_B -> NT_B
-- stage one a and one b while consuming f; the existing NT_B*b*c -> RA_A rule
-- then consumes that staged b and one c, adds one further a and restores f.
-- The macro-boundary register result is therefore the same as Goldbach30.
------------------------------------------------------------------------

newSuccessTerminalFrom :
  Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
  SuccessRegisters
newSuccessTerminalFrom zero b cTail d e fTail s g h m =
  successRegisters 2 b cTail (d + 2) e (suc fTail) s g h m
newSuccessTerminalFrom (suc a) b cTail d e fTail s g h m =
  newSuccessTerminalFrom a (suc b) (suc cTail) d e fTail s g h m

newSuccessTerminal : SuccessEntry → SuccessRegisters
newSuccessTerminal x =
  newSuccessTerminalFrom
    (a x) (b x) (cTail x) (d x) (e x) (fTail x)
    (s x) (g x) (h x) (m x)

successTerminalFromAgree :
  (a b cTail d e fTail s g h m : Nat) →
  oldSuccessTerminalFrom a b cTail d e fTail s g h m
  ≡
  newSuccessTerminalFrom a b cTail d e fTail s g h m
successTerminalFromAgree zero b cTail d e fTail s g h m = refl
successTerminalFromAgree (suc a) b cTail d e fTail s g h m =
  successTerminalFromAgree a (suc b) (suc cTail) d e fTail s g h m

successTerminalRegistersAgree :
  (x : SuccessEntry) →
  oldSuccessTerminal x ≡ newSuccessTerminal x
successTerminalRegistersAgree x =
  successTerminalFromAgree
    (a x) (b x) (cTail x) (d x) (e x) (fTail x)
    (s x) (g x) (h x) (m x)

------------------------------------------------------------------------
-- Declared consumers.
--
-- `nextEvenBoundaryConsumer` is the (a,b,c) boundary state identified by the
-- upstream Goldbach29 source comment as the start of the next even-number
-- search.  `verdictGuardConsumer` retains the f register, whose success guard
-- is consumed and restored by both macros.
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
  (a : Nat) →
  newSuccessExecutionLength a ≡ suc (oldSuccessExecutionLength a)
newSuccessExecutionLengthIsOneMore = Bridge.newSuccessExecutionLengthIsOneMore

record GoldbachSuccessMacroBoundary : Set where
  constructor goldbachSuccessMacroBoundary
  field
    terminalRegistersPreserved : Bool
    nextEvenBoundaryPreserved : Bool
    verdictGuardPreserved : Bool
    fractionCountReduced : Bool
    successMicrostepsReduced : Bool
    successMicrostepsIncreaseByOne : Bool
    wholeMachineBisimulationFollowsFromThisMacroAlone : Bool

canonicalGoldbachSuccessMacroBoundary : GoldbachSuccessMacroBoundary
canonicalGoldbachSuccessMacroBoundary =
  goldbachSuccessMacroBoundary true true true true false true false
