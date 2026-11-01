module DASHI.Physics.Closure.NSTriadKNFullShellIncidenceFunctionalityNoGoRound63Exact where

------------------------------------------------------------------------
-- ROUND 63 / D-F INCIDENCE AUDIT
--
-- The official full-shell API currently provides:
--
--   * for an occurring Pair, existence of some target/source incidence;
--   * uniqueness of the Incidence PROOF after pair/target/source are fixed.
--
-- Those facts do not imply that target/source themselves are unique.  This
-- file gives the minimal exact countermodel: the incidence proposition is the
-- singleton Unit for every pair of Boolean modes.  Incidence proofs are unique,
-- but one pair is incident to both `true` and `false` targets.
--
-- Therefore the desired D/F theorem
--
--   officialPairEnumerationIsFourierComplete
--
-- cannot be obtained from `incidenceProofUnique`.  The physical full-shell
-- producer must additionally prove MODE FUNCTIONALITY (unique target/source)
-- or directly provide target/source extraction preserving the enumeration.
-- This is precisely the missing prerequisite for a coefficient-preserving
-- bijection to the mature literal two-mode Fourier-pair system.
--
-- This logical countermodel is repository-original and uses no external
-- mathematical authority.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation.Core using (¬_)

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

CounterPair : Set
CounterPair = ⊤

CounterMode : Set
CounterMode = Bool

CounterIncidence : CounterPair → CounterMode → CounterMode → Set
CounterIncidence pair target source = ⊤

counterIncidenceProofUnique :
  ∀ pair target source →
  (left right : CounterIncidence pair target source) →
  left ≡ right
counterIncidenceProofUnique pair target source tt tt = refl

counterPairHasTrueTarget : CounterIncidence tt true true
counterPairHasTrueTarget = tt

counterPairHasFalseTarget : CounterIncidence tt false true
counterPairHasFalseTarget = tt

proofUniquenessDoesNotForceTargetUniqueness :
  (∀ target source →
    (left right : CounterIncidence tt target source) → left ≡ right) →
  ¬ ((∀ target₁ target₂ source →
      CounterIncidence tt target₁ source →
      CounterIncidence tt target₂ source →
      target₁ ≡ target₂))
proofUniquenessDoesNotForceTargetUniqueness proofUnique endpointUnique =
  trueNotFalse
    (endpointUnique true false true
      counterPairHasTrueTarget counterPairHasFalseTarget)

record FunctionalPairIncidence
    {p m i : Level}
    (Pair : Set p)
    (Mode : Set m)
    (Incidence : Pair → Mode → Mode → Set i) :
    Set (lsuc (p ⊔ m ⊔ i)) where
  field
    targetOf : Pair → Mode
    sourceOf : Pair → Mode

    selectedIncidence : ∀ pair →
      Incidence pair (targetOf pair) (sourceOf pair)

    targetFunctional : ∀ pair target source →
      Incidence pair target source → target ≡ targetOf pair

    sourceFunctional : ∀ pair target source →
      Incidence pair target source → source ≡ sourceOf pair

open FunctionalPairIncidence public

round63IncidenceProofUniquenessInsufficientForModeBijection : Bool
round63IncidenceProofUniquenessInsufficientForModeBijection = true

round63DFRequiresFunctionalPairEndpoints : Bool
round63DFRequiresFunctionalPairEndpoints = true

round63IncidenceProofUniquenessInsufficientForModeBijectionIsTrue :
  round63IncidenceProofUniquenessInsufficientForModeBijection ≡ true
round63IncidenceProofUniquenessInsufficientForModeBijectionIsTrue = refl

round63DFRequiresFunctionalPairEndpointsIsTrue :
  round63DFRequiresFunctionalPairEndpoints ≡ true
round63DFRequiresFunctionalPairEndpointsIsTrue = refl
