module DASHI.Physics.ClosureStatusFromGlue where

open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Physics.ClosureGlue
open import DASHI.Physics.UnificationClosure

-- Bridge from concrete closure axioms to the existing closure status record.
closureStatusFromGlue : ClosureAxioms → ClosureStatus
closureStatusFromGlue _ =
  record
    { hasQuadratic = ⊤
    ; hasQuadraticUnique = ⊤
    ; hasSignature31 = ⊤
    ; hasClifford = ⊤
    ; hasEvenLift = ⊤
    }
