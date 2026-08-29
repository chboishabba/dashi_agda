module DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact where

------------------------------------------------------------------------
-- VENDORED CONSTRUCTIVE-ANALYSIS SUBSTRATE
--
-- DASHI does not vendor-copy Bishop real definitions into local theorem
-- owners.  The repository carries viktorcsimma/bishop as a git submodule:
--
--   path   = vendor/bishop
--   url    = https://github.com/viktorcsimma/bishop.git
--   branch = main
--
-- On the Hardy--Ramanujan / Erdos partition branch the gitlink is pinned to
--
--   240e38c7f6938f20f865b1f956c5f084da48bd54
--
-- This module is therefore provenance only.  Analytic consumers should import
-- the ordinary Bishop modules (`Real`, `RealProperties`, `Inverse`, `Sequence`,
-- ...) supplied by that vendored submodule and build DASHI adapters/theorems on
-- top of them.  It introduces no replacement real carrier and no analytic
-- axiom.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)

bishopSubmodulePath : String
bishopSubmodulePath = "vendor/bishop"

bishopSubmoduleRepository : String
bishopSubmoduleRepository = "https://github.com/viktorcsimma/bishop.git"

bishopSubmoduleDeclaredBranch : String
bishopSubmoduleDeclaredBranch = "main"

bishopSubmodulePinnedCommit : String
bishopSubmodulePinnedCommit =
  "240e38c7f6938f20f865b1f956c5f084da48bd54"

------------------------------------------------------------------------
-- Source strings are audit metadata, not theorem authority.  The actual
-- constructive-real claims remain whatever the imported vendored Agda modules
-- prove at the pinned gitlink.
------------------------------------------------------------------------
