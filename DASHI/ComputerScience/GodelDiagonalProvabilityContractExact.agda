module DASHI.ComputerScience.GodelDiagonalProvabilityContractExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ABSTRACT GÖDEL DIAGONAL / PROVABILITY CONTRACT
--
-- This module does not prove Gödel, Löb, or Tarski.  It types the exact
-- interfaces required to state those theorems over a concrete arithmetised
-- formal system.  Existing Gödel-numbering/scalarisation modules may supply
-- code coordinates later, but do not by themselves inhabit these contracts.
------------------------------------------------------------------------

record ArithmetisedFormalSystem : Set₁ where
  field
    Formula : Set
    Sentence : Set
    Proof : Set

    codeFormula : Formula → Nat
    codeSentence : Sentence → Nat
    codeProof : Proof → Nat

    numeral : Nat → Formula
    instantiate : Formula → Nat → Sentence

    Provable : Sentence → Set
    proves : Proof → Sentence → Set

    Equivalent : Sentence → Sentence → Set
    Negation : Sentence → Sentence
    Implication : Sentence → Sentence → Sentence
    ConsistencySentence : Sentence

open ArithmetisedFormalSystem public

------------------------------------------------------------------------
-- Arithmetised substitution / representability.
------------------------------------------------------------------------

record ArithmetisedSubstitution
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    substituteCode : Nat → Nat → Nat
    substitutionExact :
      (formula : Formula F) →
      (n : Nat) →
      substituteCode (codeFormula F formula) n
      ≡ codeSentence F (instantiate F formula n)

open ArithmetisedSubstitution public

record ProofRelationRepresentation
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    proofPredicate : Formula F
    proofPredicateRepresents :
      (proof : Proof F) →
      (sentence : Sentence F) →
      proves F proof sentence →
      Provable F (instantiate F proofPredicate (codeSentence F sentence))

open ProofRelationRepresentation public

------------------------------------------------------------------------
-- Diagonal/fixed-point lemma authority.
------------------------------------------------------------------------

record DiagonalLemmaAuthority
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    fixedPoint : Formula F → Sentence F
    fixedPointEquivalence :
      (predicate : Formula F) →
      Provable F
        (fixedPoint F predicate)
      → Set
    fixedPointLaw :
      (predicate : Formula F) →
      Equivalent F
        (fixedPoint predicate)
        (instantiate F predicate (codeSentence F (fixedPoint predicate)))

open DiagonalLemmaAuthority public

------------------------------------------------------------------------
-- Provability predicate and Hilbert–Bernays/Löb derivability coordinates.
------------------------------------------------------------------------

record ProvabilityStructure
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    box : Sentence F → Sentence F

open ProvabilityStructure public

record DerivabilityConditions
    (F : ArithmetisedFormalSystem)
    (P : ProvabilityStructure F) : Set₁ where
  field
    derivability1 :
      (A : Sentence F) →
      Provable F A →
      Provable F (box P A)

    derivability2 :
      (A B : Sentence F) →
      Provable F
        (Implication F
          (box P (Implication F A B))
          (Implication F (box P A) (box P B)))

    derivability3 :
      (A : Sentence F) →
      Provable F
        (Implication F (box P A) (box P (box P A)))

open DerivabilityConditions public

------------------------------------------------------------------------
-- Named theorem-result contracts.
--
-- These are theorem interfaces, not inhabitants.  A source-aligned theorem,
-- Lean proof, Agda proof, or other accepted authority may later inhabit them.
------------------------------------------------------------------------

record GodelFirstIncompletenessResult
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    godelSentence : Sentence F
    unprovable : Provable F godelSentence → ⊥
    unrefutable : Provable F (Negation F godelSentence) → ⊥

open GodelFirstIncompletenessResult public

record GodelSecondIncompletenessResult
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    systemCannotProveItsConsistency :
      Provable F (ConsistencySentence F) → ⊥

open GodelSecondIncompletenessResult public

record LobTheoremResult
    (F : ArithmetisedFormalSystem)
    (P : ProvabilityStructure F) : Set₁ where
  field
    lob :
      (A : Sentence F) →
      Provable F (Implication F (box P A) A) →
      Provable F A

open LobTheoremResult public

record TarskiUndefinabilityResult
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    TruthPredicate : Set
    noInternalTruthPredicate : TruthPredicate → ⊥

open TarskiUndefinabilityResult public

------------------------------------------------------------------------
-- Dependency bundles.
------------------------------------------------------------------------

record GodelFirstPrerequisites
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    substitution : ArithmetisedSubstitution F
    proofRepresentation : ProofRelationRepresentation F
    diagonal : DiagonalLemmaAuthority F
    Consistent : Set
    consistent : Consistent

open GodelFirstPrerequisites public

record GodelSecondPrerequisites
    (F : ArithmetisedFormalSystem)
    (P : ProvabilityStructure F) : Set₁ where
  field
    diagonal : DiagonalLemmaAuthority F
    derivability : DerivabilityConditions F P
    Consistent : Set
    consistent : Consistent

open GodelSecondPrerequisites public

record LobPrerequisites
    (F : ArithmetisedFormalSystem)
    (P : ProvabilityStructure F) : Set₁ where
  field
    diagonal : DiagonalLemmaAuthority F
    derivability : DerivabilityConditions F P

open LobPrerequisites public

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data NaturalNumberEncodingAloneImpliesDiagonalLemma : Set where
data DiagonalLemmaAloneImpliesGodelII : Set where
data SearchExhaustionImpliesUnprovability : Set where
data GodelIncompletenessImpliesTuringHalting : Set where

encodingAloneDoesNotSupplyDiagonalLemma :
  NaturalNumberEncodingAloneImpliesDiagonalLemma → ⊥
encodingAloneDoesNotSupplyDiagonalLemma ()

diagonalLemmaAloneDoesNotSupplyGodelII :
  DiagonalLemmaAloneImpliesGodelII → ⊥
diagonalLemmaAloneDoesNotSupplyGodelII ()

finiteSearchExhaustionDoesNotSupplyUnprovability :
  SearchExhaustionImpliesUnprovability → ⊥
finiteSearchExhaustionDoesNotSupplyUnprovability ()

godelDoesNotDefinitionallySupplyHalting :
  GodelIncompletenessImpliesTuringHalting → ⊥
godelDoesNotDefinitionallySupplyHalting ()

record GodelDiagonalProvabilityBoundary : Set where
  constructor godelDiagonalProvabilityBoundary
  field
    naturalNumberCodingSeparatedFromSubstitution : Bool
    substitutionSeparatedFromDiagonalLemma : Bool
    diagonalSeparatedFromIncompleteness : Bool
    godelISeparatedFromGodelII : Bool
    derivabilityConditionsRequiredForGodelIIAndLob : Bool
    finiteProofSearchExhaustionIsUnprovability : Bool
    haltingIdentifiedWithGodelIncompleteness : Bool

canonicalGodelDiagonalProvabilityBoundary : GodelDiagonalProvabilityBoundary
canonicalGodelDiagonalProvabilityBoundary =
  godelDiagonalProvabilityBoundary
    true true true true true false false
