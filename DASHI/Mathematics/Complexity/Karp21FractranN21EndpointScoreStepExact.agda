module DASHI.Mathematics.Complexity.Karp21FractranN21EndpointScoreStepExact where

------------------------------------------------------------------------
-- Karp-21 / FRACDASH: a REAL N21 guarded endpoint/score microstep.
--
-- The original verifier owns endpointConsistent, boolEqual, and the
-- 2m certificate convention. The binary-native ledger owns the actual
-- signed token operation. Here the source N21 endpoint checks and the
-- two-lane operation are used in the compiled first-enabled machine.
--
-- The frame fixes ONE actual raw edge's endpoints, certificate labels,
-- previous endpoint history and parsed binary signed weight. Changing
-- the score ledger cannot change these endpoint guards. A change in
-- live/rejected status may change enabledness and is invalidated.
--
-- This does NOT claim a complete graph parser, token-to-raw signed
-- integer equality, recursive rawSparseScore weld, original PR.InNP,
-- or a bit-machine polynomial clock. The old original owners remain
-- authoritative. No postulates, no fabricated prime-power integers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21FractranPriorityFrontierExact as Frontier

module N21Edge
  (u v : Nat)
  (a b : Bool)
  (history : List (Nat × Bool))
  (weight : Signed.SignedMagnitudeBits)
  where

  data Rule : Set where
    advance reject : Rule

  -- The concrete original N21 history checks (not an oracle).
  endpointGuard : Bool
  endpointGuard =
    Boolean.andBool
      (Original.endpointConsistent u a history)
      (Original.endpointConsistent v b history)

  record State : Set where
    constructor state
    field
      live : Bool
      ledger : Ledger.SignedLedger
  open State public

  data Status : Set where
    advanced rejected : Status

  -- Incremental cache dependency: the rule's guard depends on the
  -- status, but NOT the large binary score payload.
  statusChanged : Bool → Bool → Bool
  statusChanged false false = false
  statusChanged false true = true
  statusChanged true false = true
  statusChanged true true = false

  guard : Rule → State → Bool
  guard advance (state current score) =
    Boolean.andBool current endpointGuard
  guard reject s = true

  affected : Rule → State → State → Bool
  affected advance (state before _) (state after _) =
    statusChanged before after
  affected reject before after = false

  unaffectedStable :
    ∀ rule before after →
    affected rule before after ≡ false →
    guard rule before ≡ guard rule after
  unaffectedStable advance (state false _) (state false _) eq = refl
  unaffectedStable advance (state false _) (state true _) ()
  unaffectedStable advance (state true _) (state false _) ()
  unaffectedStable advance (state true _) (state true _) eq = refl
  unaffectedStable reject before after eq = refl

  -- Signed contribution is inserted exactly when the original
  -- certificate endpoint labels disagree.
  scoreAdvance : Ledger.SignedLedger → Ledger.SignedLedger
  scoreAdvance score with Boolean.boolEqual a b
  ... | true = score
  ... | false = Ledger.insertSigned weight score

  apply : Rule → State → State
  apply advance (state current score) =
    state true (scoreAdvance score)
  apply reject (state current score) =
    state false score

  open Frontier.Machine State Rule guard apply affected unaffectedStable
    public renaming
      ( directStep to fractranStep
      ; cachedStep to fractranCachedStep
      ; cachedStepCorrect to karpN21CachedStepCorrect
      )

  -- The direct source edge step uses the ACTUAL N21 endpoint guards.
  -- This is one-edge score-phase semantics, NOT recursive rawSparseScore.
  originalN21EdgeStep : State → State
  originalN21EdgeStep s with guard advance s
  ... | true = apply advance s
  ... | false = apply reject s

  -- Priority order is essential: the fallback rejects exactly when
  -- the source guard fails, rather than shadowing a valid advance.
  karpFractranFirstEnabledSameN21EdgeStep :
    ∀ s → fractranStep (advance ∷ reject ∷ []) s
      ≡ just (originalN21EdgeStep s)
  karpFractranFirstEnabledSameN21EdgeStep s with guard advance s
  ... | true = refl
  ... | false = refl

  -- On an already checked and live edge, binary score updates leave
  -- the input endpoint guard cache unchanged, avoiding recomputation.
  scoreOnly : State → Ledger.SignedLedger → State
  scoreOnly (state status _) score = state status score

  scoreOnlyUnaffected :
    ∀ rule before score →
    affected rule before (scoreOnly before score) ≡ false
  scoreOnlyUnaffected advance (state false _) score = refl
  scoreOnlyUnaffected advance (state true _) score = refl
  scoreOnlyUnaffected reject before score = refl

  scoreOnlyGuardStable :
    ∀ rule before score →
    guard rule before ≡ guard rule (scoreOnly before score)
  scoreOnlyGuardStable rule before score =
    unaffectedStable rule before (scoreOnly before score)
      (scoreOnlyUnaffected rule before score)

  -- Concrete Karp instance of the generic selective frontier proof,
  -- for the original source guard and actual native binary ledger.
  karpN21CachedScoreUpdateSameStep :
    ∀ before score →
    fractranCachedStep
      (refreshCache (populate (advance ∷ reject ∷ []) before)
        before (scoreOnly before score))
      (scoreOnly before score)
    ≡ just (originalN21EdgeStep (scoreOnly before score))
  karpN21CachedScoreUpdateSameStep before score =
    let after = scoreOnly before score
        eq = karpN21CachedStepCorrect
          (advance ∷ reject ∷ [])
          (populate (advance ∷ reject ∷ []) before)
          before after refl
    in
    -- `eq` identifies cached and direct execution; the latter is
    -- the selected original N21 one-edge guarded operation.
    trans eq (karpFractranFirstEnabledSameN21EdgeStep after)
