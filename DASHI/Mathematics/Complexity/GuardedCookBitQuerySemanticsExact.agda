module DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact where

------------------------------------------------------------------------
-- EXACT SEMANTICS OF THE CANONICAL ANSWER-BLIND GUARDED COOK BIT QUERY
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Canonical
import DASHI.Mathematics.Complexity.CanonicalGuardedCookVirtualSourceExact as Guarded
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual

queryAnswer : Query.GuardedCookBitQuery → Maybe Bool
queryAnswer query =
  Canonical.lookupBit
    (Query.index query)
    (Binary.encodeFormulaBits (Query.queryFormula query))

queryAnswerSound :
  ∀ {query bit} →
  queryAnswer query ≡ Agda.Builtin.Maybe.just bit →
  Virtual.BitAt
    (Query.index query)
    (Binary.encodeFormulaBits (Query.queryFormula query))
    bit
queryAnswerSound = Canonical.lookupBitSound

queryAnswerComplete :
  ∀ {query bit} →
  Virtual.BitAt
    (Query.index query)
    (Binary.encodeFormulaBits (Query.queryFormula query))
    bit →
  queryAnswer query ≡ Agda.Builtin.Maybe.just bit
queryAnswerComplete = Canonical.lookupBitComplete

queryAnswerMatchesCanonicalSource :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  queryAnswer (Description.atIndex description index)
  ≡
  Virtual.readBit (Guarded.canonicalGuardedSource description) index
queryAnswerMatchesCanonicalSource description index =
  Agda.Builtin.Equality.refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The canonical serialized query has one exact extensional answer function.
-- A future finite generator must realize `queryAnswer`; there is no remaining
-- freedom to choose a different semantic oracle or query-dependent formula.
------------------------------------------------------------------------
