module DASHI.Mathematics.Complexity.Karp21EncodedFixedGraphWordsExact where

-- Integration owner: not --safe until the imported weighted-graph
-- theorem chain is independently checked and transitively --safe.

------------------------------------------------------------------------
-- E20: THE TWO LITERAL FIXED GRAPH EXCEPTIONS, FULLY SOURCED.
--
-- For total PARTITION -> weighted MAX CUT:
-- * zero signed total has an ORIGINAL actual two-vertex +1 unit edge,
--   required W=1, hence this wire word is YES;
-- * malformed source words get the SAME edge but required W=2,
--   hence no cut can accept the target wire word.
--
-- Both target words come from the ACTUAL gamma/zigzag encoder and
-- are decoded by the ACTUAL strict target graph-word parser.
-- There are no abstract true/false status flags or assumed graph
-- truth predicates here; all four NO labels are explicitly rejected.
--
-- Karp 1972; DASHI fixed E20 graph owners and gamma/zigzag codec.
-- Still source-written until independent Agda kernel acceptance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)
import Data.Vec.Base as Vec
import Data.Unit
import Data.Integer.Properties as IntP
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Actual
import DASHI.Mathematics.Complexity.Karp21WeightedMaxCutFixedNoGraphExact as FixedNo
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as GraphWord
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode

encodedFixedUnitWordAccepts :
  PR.accepts GraphWord.concreteGraphWordLanguage
    (Encode.encodeGraphWord (2 , Actual.fixedUnitGraph))
encodedFixedUnitWordAccepts =
  (true Vec.∷ false Vec.∷ Vec.[]) ,
  IntP.≤ᵇ⇒≤ Data.Unit.tt

encodedFixedNoWordRejects :
  PR.accepts GraphWord.concreteGraphWordLanguage
    (Encode.encodeGraphWord FixedNo.fixedNoGraphInstance) → ⊥
encodedFixedNoWordRejects
  ((false Vec.∷ false Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)
encodedFixedNoWordRejects
  ((false Vec.∷ true Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)
encodedFixedNoWordRejects
  ((true Vec.∷ false Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)
encodedFixedNoWordRejects
  ((true Vec.∷ true Vec.∷ Vec.[]) , valid) =
  ⊥-elim (IntP.≤⇒≤ᵇ valid)

fixedUnitWordFaithful :
  PR.Iff
    (Cut.WeightedMaxCutYES Actual.fixedUnitGraph)
    (PR.accepts GraphWord.concreteGraphWordLanguage
      (Encode.encodeGraphWord (2 , Actual.fixedUnitGraph)))
fixedUnitWordFaithful =
  PR.iff
    (λ _ → encodedFixedUnitWordAccepts)
    (λ _ → Actual.fixedUnitGraphAccepts)
