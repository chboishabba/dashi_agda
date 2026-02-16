module Verification.BinaryPatching where

open import Verification.Prelude

postulate Binary : Set
postulate Input  : Set
postulate Output : Set

-- Semantics of a binary as a function (idealization).
postulate run : Binary → Input → Output

-- Vulnerability predicate (e.g., triggers UAF, OOB, etc.)
postulate Vuln : Binary → Set

-- Patch procedure
postulate patch : Binary → Binary

-- Correctness obligations
record PatchCorrect : Set₁ where
  field
    B : Binary
    -- vulnerability removed
    fixed : ¬ Vuln (patch B)
    -- behavior preserved on some agreed safe domain
    postulate SafeInput : Input → Set
    preserved : ∀ i → SafeInput i → run (patch B) i ≡ run B i
