module DASHI.Physics.Closure.NSPreReleaseTerminalConeChronologyExact where

------------------------------------------------------------------------
-- PRE-RELEASE NS TERMINAL-CONE CHRONOLOGY
--
-- The 2026-09-09 tranche intake date is not the theorem-construction date.
-- Git history shows that the narrowing from the resolved Gram/Cauchy route to
-- the literal direct R406 off-diagonal consumer was already committed before
-- the public 2026-09-08 OpenAI Navier--Stokes release.
--
-- These are provenance receipts only.  They do not convert a conditional
-- compiler into an inhabited analytic leaf and do not claim Clay priority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

data ChronologyRole : Set where
  gramCauchyRoute
  directR423Producer
  directResolventCarrier
  directR415Consumer
  terminalCutset : ChronologyRole

record DatedNSCommit : Set where
  constructor dated-ns-commit
  field
    localTimestamp : String
    commitSHA : String
    description : String
    role : ChronologyRole

open DatedNSCommit public

preReleaseTerminalChronology : List DatedNSCommit
preReleaseTerminalChronology =
  dated-ns-commit
    "2026-09-07T21:49:39+10:00"
    "02f892c5013e28692f15f6ad0a6d5d984b31577b"
    "R471-R477 Gram operator route wired into closure rollup"
    gramCauchyRoute
  ∷ dated-ns-commit
    "2026-09-08T03:28:12+10:00"
    "cd40a97f63d14d934407125d0eb73dddbcde299a"
    "R483 ordered Cauchy sum closed to the R446 Hermitian form"
    gramCauchyRoute
  ∷ dated-ns-commit
    "2026-09-08T03:30:10+10:00"
    "d7d5b14a6eeb4ecb79cbef6f00b61af5f253e59d"
    "R484 separates full Cauchy form from signed flux consumer"
    gramCauchyRoute
  ∷ dated-ns-commit
    "2026-09-08T03:31:05+10:00"
    "928e6f0d2cff83f5b56130a79c61bdeb2745f4ae"
    "R485 corrects first-missing search to positive signed flux"
    gramCauchyRoute
  ∷ dated-ns-commit
    "2026-09-08T03:50:09+10:00"
    "1bf7d4190420bfe57d96c4089af89bfb2357c7e6"
    "R487 compiles fixed-output payments directly to R423"
    directR423Producer
  ∷ dated-ns-commit
    "2026-09-08T04:19:25+10:00"
    "e5530a268041c6b7b99a1ad858ffb71f95bdecb2"
    "R489 makes direct signed payment the first physical leaf"
    directR423Producer
  ∷ dated-ns-commit
    "2026-09-08T04:21:10+10:00"
    "5a16bbcc593aa9fdd0610a9b8beba2e4446bea8b"
    "R492 restores strict same-object companion firewall before R423"
    directR423Producer
  ∷ dated-ns-commit
    "2026-09-08T04:46:02+10:00"
    "71318a44a8ece6086d40ec052d759afa3912517e"
    "R493 keeps integration transport optional on the direct strict route"
    directR423Producer
  ∷ dated-ns-commit
    "2026-09-08T04:53:49+10:00"
    "9be2933f265e95ccc9f2dca5204b21bc528fc393"
    "R496 defines the direct nonseparable resolvent pair companion"
    directResolventCarrier
  ∷ dated-ns-commit
    "2026-09-08T04:56:50+10:00"
    "6bccd775be7fafe5aaaf62c49d049bafc10a80be"
    "R500 lifts the literal direct companion through integration transport"
    directResolventCarrier
  ∷ dated-ns-commit
    "2026-09-08T04:57:19+10:00"
    "c7e45e4f07d2000318a9d78f1d14a1dc787e747f"
    "R501 compiles the direct resolvent companion budget to R423"
    directR423Producer
  ∷ dated-ns-commit
    "2026-09-08T05:00:53+10:00"
    "a74a9bbac96690ff83165ff81073f43fbd23cfea"
    "R502 separates the direct off-diagonal signed cross from full companion"
    directR415Consumer
  ∷ dated-ns-commit
    "2026-09-08T05:02:43+10:00"
    "984eaa83d988b0292ead61cfef8e9db463cbb425"
    "R503 compiles the direct off-diagonal resolvent budget directly to R415"
    directR415Consumer
  ∷ dated-ns-commit
    "2026-09-08T05:05:02+10:00"
    "67831b2b1ada78f08c5ad092637afeb9e2a80180"
    "R504 exposes the literal R406 two-leaf Clay terminal cutset"
    terminalCutset
  ∷ []

trancheIntakeDateIsConstructionDate : Bool
trancheIntakeDateIsConstructionDate = false

terminalConeSubstantiallyPredatesTrancheIntake : Bool
terminalConeSubstantiallyPredatesTrancheIntake = true

chronologyAloneProvesAnalyticInhabitation : Bool
chronologyAloneProvesAnalyticInhabitation = false

chronologyAloneProvesClayPriority : Bool
chronologyAloneProvesClayPriority = false

terminalConeSubstantiallyPredatesTrancheIntakeIsTrue :
  terminalConeSubstantiallyPredatesTrancheIntake ≡ true
terminalConeSubstantiallyPredatesTrancheIntakeIsTrue = refl

chronologyAloneProvesClayPriorityIsFalse :
  chronologyAloneProvesClayPriority ≡ false
chronologyAloneProvesClayPriorityIsFalse = refl
