module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCookLevinSameObjectWeldExact where

------------------------------------------------------------------------
-- SAME-OBJECT WELD:
-- finite static program syntax + exact Cook--Levin certificate
--
-- For ONE literal ConcreteTapeMachine, combine:
--
--   * exact finite static-program encoding/decoding;
--   * the SAME state/symbol coverage witnesses;
--   * the SAME literal transition-rule table;
--   * exact-budget Cook--Levin satisfiability iff accepting run;
--   * exact tableau variable count and closed polynomial clause bound.
--
-- This closes a representation seam: the machine whose finite code is
-- serialized is definitionally the machine whose run is reduced to SAT.
--
-- It does NOT establish equivalence with every standard deterministic
-- polynomial-time machine model, and it does NOT prove SAT is hard for
-- this machine class. Those are separate universal theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Program
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinPrizeFacingExact as Cook

------------------------------------------------------------------------
-- One certificate, one machine object.
------------------------------------------------------------------------

record SameMachineProgramCookLevinCertificate
    (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  field
    finiteProgram :
      Program.ConcreteTapeProgramDescription machine

    programCodeRoundTrip :
      Program.decodeStaticProgramView
        machine stateCoverage symbolCoverage
        (Program.code finiteProgram)
      ≡
      Program.canonicalStaticProgramView machine

    cookLevin :
      Cook.PrizeFacingCookLevinCertificate
        stateCoverage symbolCoverage nonempty input steps

open SameMachineProgramCookLevinCertificate public

------------------------------------------------------------------------
-- Canonical inhabitant from the repository's two positive constructions.
------------------------------------------------------------------------

sameMachineProgramCookLevinCertificate :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  SameMachineProgramCookLevinCertificate
    machine stateCoverage symbolCoverage nonempty input steps
sameMachineProgramCookLevinCertificate
    machine stateCoverage symbolCoverage nonempty input steps = record
  { finiteProgram =
      Program.canonicalConcreteTapeProgramDescription
        machine stateCoverage symbolCoverage
  ; programCodeRoundTrip =
      Program.decodeEncodeStaticProgramView
        machine stateCoverage symbolCoverage
  ; cookLevin =
      Cook.prizeFacingCookLevinCertificate
        stateCoverage symbolCoverage nonempty input steps
  }

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
--   finite program code on the literal machine
--   exact decode-after-encode
--   exact-budget Cook--Levin semantics on the literal machine
--   exact variable count
--   closed polynomial clause bound
--
-- OPEN:
--   standard deterministic TM -> ConcreteTapeMachine polynomial simulation
--   ConcreteTapeMachine -> standard TM polynomial simulation
--   universal SAT lower-bound invariant preserved by such simulations
------------------------------------------------------------------------
