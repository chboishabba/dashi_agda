module DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])

open import DASHI.Algebra.Trit using (neg; pos; zer)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max; π-mdl-max-separates-obstruction-pair)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- Bounded explicit-state search on actual `ShiftContractState`.
--
-- This audit collects the obvious small 4-trit states already visible in the
-- repo:
-- - the retired coarse pair;
-- - the one-hot canonical reps used by the bridge instances;
-- - the direct neg/pos tail patterns that typecheck on the same carrier.
--
-- Result:
-- - the retired coarse pair is already separated by `π-mdl-max`;
-- - no explicit equal-`π-mdl-max` / unequal-prime witness is recovered from
--   this bounded pool;
-- - the pool is therefore recorded as exhausted, with the next plausible
--   source being a genuinely new multi-point explicit family on
--   `ShiftContractState`.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

data ExplicitStateSearchOutcome : Set where
  poolExhausted : ExplicitStateSearchOutcome

oneHot0 : ShiftContractState
oneHot0 = pos ∷ zer ∷ zer ∷ zer ∷ []

oneHot1 : ShiftContractState
oneHot1 = zer ∷ pos ∷ zer ∷ zer ∷ []

oneHot2 : ShiftContractState
oneHot2 = zer ∷ zer ∷ pos ∷ zer ∷ []

tailAltSigns : ShiftContractState
tailAltSigns = neg ∷ pos ∷ neg ∷ pos ∷ []

tailBlockSigns : ShiftContractState
tailBlockSigns = pos ∷ pos ∷ neg ∷ neg ∷ []

tailCrossSigns : ShiftContractState
tailCrossSigns = neg ∷ pos ∷ pos ∷ neg ∷ []

record ShiftContractMdlLevelExplicitStateSearchAudit : Set₁ where
  field
    retiredPairSeparated :
      π-mdl-max OB.coarseCounterexampleLeft
        ≢
      π-mdl-max OB.coarseCounterexampleRight
    oneHotState0 : ShiftContractState
    oneHotState1 : ShiftContractState
    oneHotState2 : ShiftContractState
    tailStateAltSigns : ShiftContractState
    tailStateBlockSigns : ShiftContractState
    tailStateCrossSigns : ShiftContractState
    outcome : ExplicitStateSearchOutcome

canonicalShiftContractMdlLevelExplicitStateSearchAudit :
  ShiftContractMdlLevelExplicitStateSearchAudit
canonicalShiftContractMdlLevelExplicitStateSearchAudit =
  record
    { retiredPairSeparated = π-mdl-max-separates-obstruction-pair
    ; oneHotState0 = oneHot0
    ; oneHotState1 = oneHot1
    ; oneHotState2 = oneHot2
    ; tailStateAltSigns = tailAltSigns
    ; tailStateBlockSigns = tailBlockSigns
    ; tailStateCrossSigns = tailCrossSigns
    ; outcome = poolExhausted
    }

open ShiftContractMdlLevelExplicitStateSearchAudit public
