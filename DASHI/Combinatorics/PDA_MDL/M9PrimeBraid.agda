module DASHI.Combinatorics.PDA_MDL.M9PrimeBraid where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Combinatorics.PDA_MDL.Prelude
import DASHI.Combinatorics.PDA_MDL.PDA as Existing
open import DASHI.Arithmetic.M9BraidPDA
open import DASHI.Arithmetic.M9MDLBraidEvaluation

------------------------------------------------------------------------
-- Recursive hypothesis source.
--
-- No list of primes is built into this generator.  It enumerates ordinary
-- factor hypotheses by recursion; an MDL policy may retain, reorder, or turn
-- them into identity events after earlier braid evaluations subsume them.

nextFactor : FactorCandidate → FactorCandidate
nextFactor (factor n) = factor (suc n)

recursiveFactorGenerator : CandidateGenerator
recursiveFactorGenerator =
  record
    { seed = factor (suc (suc zero))
    ; next = nextFactor
    ; candidates = []
    }

------------------------------------------------------------------------
-- Crossing programs.

pushThenCross : FactorCandidate → FactorCandidate → BraidWord
pushThenCross m w = push m ∷ cross m w ∷ []

identityIfSubsumed : Bool → Event → Event
identityIfSubsumed true e = identity
identityIfSubsumed false e = e

------------------------------------------------------------------------
-- Existing PDA/MDL compatibility.
--
-- The older PDA surface observes worlds through a priced admissibility lens.
-- M9 supplies the richer world state; this bridge deliberately leaves the
-- arithmetic admissibility witness parameterised rather than promoting a
-- primality decision from the structural braid alone.

record M9PrimeWorld : Set where
  constructor m9PrimeWorld
  field
    endpoint : Endpoint
    kernel   : KernelState
    program  : BraidWord
open M9PrimeWorld public

record M9PrimeObservation : Set where
  constructor m9PrimeObservation
  field
    verdict : Verdict
    survival : Nat
open M9PrimeObservation public

record M9PrimePDAWitness : Set₁ where
  field
    pda : Existing.PDA M9PrimeWorld M9PrimeObservation
    generator : CandidateGenerator
    generatorIsRecursive : generator ≡ recursiveFactorGenerator
    deadlineWidthThree : Nat
    deadlineWidthThreeIsDelta3 : deadlineWidthThree ≡ delta3
    nonSeparable : Bool
    noPrimeListProgrammed : Bool
    noPrimalityPromotionFromStructureAlone : Bool
    reading : String
open M9PrimePDAWitness public

------------------------------------------------------------------------
-- Structural laws used by downstream executable/certified instances.

subsumedEventIsIdentity :
  ∀ (e : Event) → identityIfSubsumed true e ≡ identity
subsumedEventIsIdentity e = refl

freshEventRemainsTwist :
  ∀ (e : Event) → identityIfSubsumed false e ≡ e
freshEventRemainsTwist e = refl

crossingProgramHasPush :
  ∀ (m w : FactorCandidate) →
  pushThenCross m w ≡ push m ∷ cross m w ∷ []
crossingProgramHasPush m w = refl
