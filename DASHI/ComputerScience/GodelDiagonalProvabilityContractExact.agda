module DASHI.ComputerScience.GodelDiagonalProvabilityContractExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ABSTRACT GÖDEL DIAGONAL / PROVABILITY CONTRACT
--
-- A natural-number code is only one coordinate.  Diagonalisation also needs
-- terms/numerals, substitution on codes, representability inside the object
-- theory, and an object-language biconditional which the theory proves.
------------------------------------------------------------------------

record ArithmetisedFormalSystem : Set₁ where
  field
    Term : Set
    Formula : Set          -- one distinguished free variable
    BinaryFormula : Set    -- two distinguished free variables
    Sentence : Set
    Proof : Set

    codeTerm : Term → Nat
    codeFormula : Formula → Nat
    codeBinaryFormula : BinaryFormula → Nat
    codeSentence : Sentence → Nat
    codeProof : Proof → Nat

    numeral : Nat → Term
    instantiate : Formula → Term → Sentence
    instantiate2 : BinaryFormula → Term → Term → Sentence

    Provable : Sentence → Set
    proves : Proof → Sentence → Set

    Negation : Sentence → Sentence
    Implication : Sentence → Sentence → Sentence
    Biconditional : Sentence → Sentence → Sentence
    ConsistencySentence : Sentence

open ArithmetisedFormalSystem public

------------------------------------------------------------------------
-- Arithmetised substitution / proof-relation representation.
------------------------------------------------------------------------

record ArithmetisedSubstitution
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    substituteCode : Nat → Nat → Nat
    substitutionExact :
      (formula : Formula F) →
      (n : Nat) →
      substituteCode (codeFormula F formula) n
      ≡ codeSentence F (instantiate F formula (numeral F n))

open ArithmetisedSubstitution public

record ProofRelationRepresentation
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    proofRelationPredicate : BinaryFormula F
    proofRelationRepresentsPositiveInstances :
      (proof : Proof F) →
      (sentence : Sentence F) →
      proves F proof sentence →
      Provable F
        (instantiate2 F proofRelationPredicate
          (numeral F (codeProof F proof))
          (numeral F (codeSentence F sentence)))

open ProofRelationRepresentation public

------------------------------------------------------------------------
-- Diagonal/fixed-point lemma.
--
-- Standard theorem shape:
--
--   F ⊢ D ↔ A(⌜D⌝)
--
-- This is provability of an OBJECT-LANGUAGE biconditional, not a meta-level
-- identification of the two sentences or their meanings.
------------------------------------------------------------------------

record DiagonalLemmaAuthority
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    fixedPoint : Formula F → Sentence F
    fixedPointLaw :
      (predicate : Formula F) →
      Provable F
        (Biconditional F
          (fixedPoint predicate)
          (instantiate F predicate
            (numeral F (codeSentence F (fixedPoint predicate)))))

open DiagonalLemmaAuthority public

------------------------------------------------------------------------
-- GENERIC DIAGONAL CONSTRUCTION
--
-- A concrete arithmetic formalisation still has to represent the unary map
-- x ↦ A(sub(x,x)).  Once it supplies that representation, the fixed-point
-- lemma itself follows from the exact substitution-code law below.
------------------------------------------------------------------------

record DiagonalFormulaConstruction
    (F : ArithmetisedFormalSystem)
    (S : ArithmetisedSubstitution F) : Set₁ where
  field
    diagonalise : Formula F → Formula F
    diagonaliseRepresentsSelfSubstitution :
      (predicate : Formula F) →
      Provable F
        (Biconditional F
          (instantiate F
            (diagonalise predicate)
            (numeral F (codeFormula F (diagonalise predicate))))
          (instantiate F predicate
            (numeral F
              (substituteCode S
                (codeFormula F (diagonalise predicate))
                (codeFormula F (diagonalise predicate))))))

open DiagonalFormulaConstruction public

fixedPointFromConstruction :
  (F : ArithmetisedFormalSystem) →
  (S : ArithmetisedSubstitution F) →
  DiagonalFormulaConstruction F S →
  Formula F →
  Sentence F
fixedPointFromConstruction F S D predicate =
  instantiate F
    (diagonalise D predicate)
    (numeral F (codeFormula F (diagonalise D predicate)))

fixedPointFromConstructionLaw :
  (F : ArithmetisedFormalSystem) →
  (S : ArithmetisedSubstitution F) →
  (D : DiagonalFormulaConstruction F S) →
  (predicate : Formula F) →
  Provable F
    (Biconditional F
      (fixedPointFromConstruction F S D predicate)
      (instantiate F predicate
        (numeral F
          (codeSentence F (fixedPointFromConstruction F S D predicate)))))
fixedPointFromConstructionLaw F S D predicate
  rewrite substitutionExact S
    (diagonalise D predicate)
    (codeFormula F (diagonalise D predicate))
  = diagonaliseRepresentsSelfSubstitution D predicate

diagonalLemmaFromConstruction :
  (F : ArithmetisedFormalSystem) →
  (S : ArithmetisedSubstitution F) →
  DiagonalFormulaConstruction F S →
  DiagonalLemmaAuthority F
diagonalLemmaFromConstruction F S D =
  record
    { fixedPoint = fixedPointFromConstruction F S D
    ; fixedPointLaw = fixedPointFromConstructionLaw F S D
    }

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
------------------------------------------------------------------------

-- Ordinary Gödel sentence: consistency suffices for the unprovability half;
-- the classical two-sided result needs the stronger 1-/omega-consistency
-- coordinate represented in GodelFirstPrerequisites below.
record GodelFirstIncompletenessResult
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    godelSentence : Sentence F
    unprovable : Provable F godelSentence → ⊥
    unrefutable : Provable F (Negation F godelSentence) → ⊥

open GodelFirstIncompletenessResult public

-- Rosser's modified sentence is deliberately distinct: under the appropriate
-- effective arithmetic hypotheses it obtains both sides from simple
-- consistency rather than silently strengthening the ordinary Gödel sentence.
record RosserFirstIncompletenessResult
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    rosserSentence : Sentence F
    rosserUnprovable : Provable F rosserSentence → ⊥
    rosserUnrefutable : Provable F (Negation F rosserSentence) → ⊥

open RosserFirstIncompletenessResult public

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

record GodelFirstUnprovabilityPrerequisites
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    substitution : ArithmetisedSubstitution F
    proofRepresentation : ProofRelationRepresentation F
    diagonal : DiagonalLemmaAuthority F
    Consistent : Set
    consistent : Consistent

open GodelFirstUnprovabilityPrerequisites public

record GodelFirstPrerequisites
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    substitution : ArithmetisedSubstitution F
    proofRepresentation : ProofRelationRepresentation F
    diagonal : DiagonalLemmaAuthority F
    Consistent : Set
    consistent : Consistent
    OneOrOmegaConsistent : Set
    oneOrOmegaConsistent : OneOrOmegaConsistent

open GodelFirstPrerequisites public

record RosserFirstPrerequisites
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    substitution : ArithmetisedSubstitution F
    proofRepresentation : ProofRelationRepresentation F
    diagonal : DiagonalLemmaAuthority F
    Consistent : Set
    consistent : Consistent

open RosserFirstPrerequisites public

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
data PlainConsistencyGivesOrdinaryGodelUnrefutability : Set where
data GodelSentenceEqualsRosserSentence : Set where
data TermsAreFormulas : Set where
data UnaryProofPredicateIsBinaryProofRelation : Set where

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

plainConsistencyDoesNotGiveOrdinaryGodelUnrefutabilityHere :
  PlainConsistencyGivesOrdinaryGodelUnrefutability → ⊥
plainConsistencyDoesNotGiveOrdinaryGodelUnrefutabilityHere ()

godelSentenceIsNotDefinitionallyRosserSentence :
  GodelSentenceEqualsRosserSentence → ⊥
godelSentenceIsNotDefinitionallyRosserSentence ()

termsAreNotDefinitionallyFormulas : TermsAreFormulas → ⊥
termsAreNotDefinitionallyFormulas ()

unaryPredicateDoesNotReplaceBinaryProofRelation :
  UnaryProofPredicateIsBinaryProofRelation → ⊥
unaryPredicateDoesNotReplaceBinaryProofRelation ()

record GodelDiagonalProvabilityBoundary : Set where
  constructor godelDiagonalProvabilityBoundary
  field
    termsSeparatedFromFormulas : Bool
    unaryAndBinaryFormulaAritiesSeparated : Bool
    naturalNumberCodingSeparatedFromSubstitution : Bool
    substitutionSeparatedFromDiagonalLemma : Bool
    diagonalLawIsObjectLanguageProvableBiconditional : Bool
    diagonalLemmaDerivedFromConstructionInterface : Bool
    diagonalSeparatedFromIncompleteness : Bool
    originalGodelTwoSidedNeedsStrongerConsistencyCoordinate : Bool
    rosserStrengtheningKeptDistinct : Bool
    godelISeparatedFromGodelII : Bool
    derivabilityConditionsRequiredForGodelIIAndLob : Bool
    finiteProofSearchExhaustionIsUnprovability : Bool
    haltingIdentifiedWithGodelIncompleteness : Bool

canonicalGodelDiagonalProvabilityBoundary : GodelDiagonalProvabilityBoundary
canonicalGodelDiagonalProvabilityBoundary =
  godelDiagonalProvabilityBoundary
    true true true true true true true true true true true false false
