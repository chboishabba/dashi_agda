module DASHI.Physics.YangMills.YMClayParametricVocabularyNoClayPromotionExact where

------------------------------------------------------------------------
-- CRITICAL ENDPOINT SEMANTIC ANCHORING: the chosen Clay problem record
-- is PARAMETRIC in an arbitrary ClayProblemVocabulary. One can choose
-- every obligation predicate to be the trivial one-element type.
-- This formally inhabits ClayYangMillsSolution for THAT VOCABULARY,
-- with no quantum gauge fields, Hamiltonian, nontriviality, or gap.
--
-- Therefore inhabiting ClayYangMillsSolution SOME-VOCABULARY is NOT
-- evidence of the externally specified Jaffe--Witten Clay theorem.
-- The Round78 literal compiler is valid as a relative implication
-- for its chosen LiteralYangMillsSemantics C, but C and S themselves
-- must first be SAME-OBJECT pinned to actual mathematical QFT objects
-- and authoritative physical meanings. This is not automatic merely
-- because the vocabulary is definitionally induced from a supplied Y.
--
-- This module also supplies the correct bidirectional TRANSPORT on
-- three fixed families of physically selected requirements. Those
-- equalities, plus the chosen parametric solution proof, are the
-- required *semantic endpoint anchoring*. No reverse implication
-- from arbitrary official Clay solutions to the specific RG route.
--
-- The trivial witness below is a deliberate negative control,
-- NEVER an actual 4D Yang--Mills or Clay solution.
-- SOURCE WRITTEN, no kernel acceptance, no postulates/holes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁)
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

data Trivial : Set where
  trivial : Trivial

data NoProof : Set where

-- Exact inhabitant of the original *PARAMETRIC* ClayProblemVocabulary.
trivialChosenVocabulary : Clay.ClayProblemVocabulary
trivialChosenVocabulary = record
  { Clay.ClayProblemVocabulary.PreconditionWitness = λ _ → Trivial
  ; Clay.ClayProblemVocabulary.PostconditionWitness = λ _ → Trivial
  ; Clay.ClayProblemVocabulary.InvariantWitness = λ _ → Trivial
  }

-- The existence of this record is a precise NONPROMOTION countermodel.
-- It proves no physical statement; it only exhibits why the generic
-- vocabulary parameter is a semantic trust obligation.
trivialVocabularyHasParametricRecord :
  Clay.ClayYangMillsSolution trivialChosenVocabulary
trivialVocabularyHasParametricRecord = record
  { Clay.ClayYangMillsSolution.preconditions = λ _ → trivial
  ; Clay.ClayYangMillsSolution.postconditions = λ _ → trivial
  ; Clay.ClayYangMillsSolution.invariants = λ _ → trivial
  }

-- A physically fixed, external interpretation is an additional input.
-- It is NOT free to be chosen after proving a parametric record.
record PhysicallyAnchoredClayEndpoint
    (vocabulary : Clay.ClayProblemVocabulary)
    (selectedPrecondition : Clay.ClayPrecondition → Set)
    (selectedPostcondition : Clay.ClayPostcondition → Set)
    (selectedInvariant : Clay.ClayInvariant → Set)
    : Set₁ where
  constructor physicallyAnchoredClayEndpoint
  field
    sourceParametricProof : Clay.ClayYangMillsSolution vocabulary
    preconditionSameMeaning :
      ∀ req →
      Clay.PreconditionWitness vocabulary req
      ≡ selectedPrecondition req
    postconditionSameMeaning :
      ∀ req →
      Clay.PostconditionWitness vocabulary req
      ≡ selectedPostcondition req
    invariantSameMeaning :
      ∀ req →
      Clay.InvariantWitness vocabulary req
      ≡ selectedInvariant req

open PhysicallyAnchoredClayEndpoint public

fromParametricToSelected :
  ∀ {V : Clay.ClayProblemVocabulary}
    {P : Clay.ClayPrecondition → Set}
    {Q : Clay.ClayPostcondition → Set}
    {R : Clay.ClayInvariant → Set} →
    PhysicallyAnchoredClayEndpoint V P Q R →
    (∀ req → P req) × (∀ req → Q req) × (∀ req → R req)
fromParametricToSelected anchored =
  (λ pre →
    transport
      (preconditionSameMeaning anchored pre)
      (Clay.ClayYangMillsSolution.preconditions (sourceParametricProof anchored) pre)) ,
  (λ post →
    transport
      (postconditionSameMeaning anchored post)
      (Clay.ClayYangMillsSolution.postconditions (sourceParametricProof anchored) post)) ,
  (λ inv →
    transport
      (invariantSameMeaning anchored inv)
      (Clay.ClayYangMillsSolution.invariants (sourceParametricProof anchored) inv))
  where
    transport : ∀ {A B : Set} → A ≡ B → A → B
    transport refl proof = proof

-- The converse is ONLY for fixed literal predicate-family equalities,
-- not the claim that arbitrary Clay solutions imply this preferred RG
-- proof strategy. This is logical type transport, not physical discovery.
fromSelectedToParametric :
  ∀ {V : Clay.ClayProblemVocabulary}
    {P : Clay.ClayPrecondition → Set}
    {Q : Clay.ClayPostcondition → Set}
    {R : Clay.ClayInvariant → Set} →
    (∀ req → Clay.PreconditionWitness V req ≡ P req) →
    (∀ req → Clay.PostconditionWitness V req ≡ Q req) →
    (∀ req → Clay.InvariantWitness V req ≡ R req) →
    (∀ req → P req) →
    (∀ req → Q req) →
    (∀ req → R req) →
    PhysicallyAnchoredClayEndpoint V P Q R
fromSelectedToParametric preEq postEq invEq pre post inv =
  physicallyAnchoredClayEndpoint
    (record
      { Clay.ClayYangMillsSolution.preconditions =
          λ req → backwards (preEq req) (pre req)
      ; Clay.ClayYangMillsSolution.postconditions =
          λ req → backwards (postEq req) (post req)
      ; Clay.ClayYangMillsSolution.invariants =
          λ req → backwards (invEq req) (inv req)
      })
    preEq postEq invEq
  where
    backwards : ∀ {A B : Set} → A ≡ B → B → A
    backwards refl witness = witness

-- If the externally selected precondition at some requirement is
-- uninhabited, no anchored solution of that meaning can exist. This
-- is the real difference between a chosen Trivial vocabulary and a
-- selected physical assertion with meaningful falsifiability.
selectedFalsePreconditionRejectsAnchoring :
  ∀ {V : Clay.ClayProblemVocabulary}
    {P : Clay.ClayPrecondition → Set}
    {Q : Clay.ClayPostcondition → Set}
    {R : Clay.ClayInvariant → Set}
    (requirement : Clay.ClayPrecondition) →
    (P requirement → NoProof) →
    PhysicallyAnchoredClayEndpoint V P Q R →
    NoProof
selectedFalsePreconditionRejectsAnchoring requirement refute anchored =
  refute
    (proj₁ (fromParametricToSelected anchored) requirement)
