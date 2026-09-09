module DASHI.ComputerScience.GodelDiagonalProvabilityContractExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ABSTRACT GÖDEL DIAGONAL / PROVABILITY CONTRACT
--
-- This module separates the arithmetic coding substrate from the operations
-- that make diagonalisation possible.  In particular, a Nat code alone does
-- not provide numeral quotation, substitution, representability, or a proof
-- of an object-language biconditional.
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

    Negation : Sentence → Sentence
    Implication : Sentence → Sentence → Sentence
    Biconditional : Sentence → Sentence → Sentence
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
-- Diagonal/fixed-point lemma.
--
-- Standard theorem shape:
--
--   F ⊢ D ↔ A(⌜D⌝)
--
-- The biconditional is an OBJECT-LANGUAGE sentence whose provability is the
-- theorem.  It is not merely a meta-level equivalence relation.
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
          (instantiate F predicate (codeSentence F (fixedPoint predicate))))

open DiagonalLemmaAuthority public

------------------------------------------------------------------------
-- GENERIC DIAGONAL CONSTRUCTION
--
-- This is the first actual theorem seam.  A construction supplies a unary
-- formula which represents the map x ↦ A(sub(x,x)).  ArithmetisedSubstitution
-- then identifies the self-substitution code with the code of the resulting
-- sentence.  From those two coordinates we DERIVE DiagonalLemmaAuthority.
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
            (codeFormula F (diagonalise predicate)))
          (instantiate F predicate
            (substituteCode S
              (codeFormula F (diagonalise predicate))
              (codeFormula F (diagonalise predicate)))))

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
    (codeFormula F (diagonalise D predicate))

fixedPointFromConstructionLaw :
  (F : ArithmetisedFormalSystem) →
  (S : ArithmetisedSubstitution F) →
  (D : DiagonalFormulaConstruction F S) →
  (predicate : Formula F) →
  Provable F
    (Biconditional F
      (fixedPointFromConstruction F S D predicate)
      (instantiate F predicate
        (codeSentence F (fixedPointFromConstruction F S D predicate))))
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

-- This two-sided result is the ORIGINAL Gödel-sentence outcome and is paired
-- below with a 1-/omega-consistency coordinate.  Mere consistency is enough
-- for the unprovability half, but not for the ordinary Gödel sentence's
-- unrefutability half.
record GodelFirstIncompletenessResult
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    godelSentence : Sentence F
    unprovable : Provable F godelSentence → ⊥
    unrefutable : Provable F (Negation F godelSentence) → ⊥

open GodelFirstIncompletenessResult public

-- Rosser's modified sentence obtains both directions from simple consistency
-- under the appropriate effective/arithmetical hypotheses; keep it a distinct
-- theorem/result rather than silently strengthening Gödel's original sentence.
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

-- Consistency-only prerequisites for the first (unprovability) half of the
-- ordinary Gödel sentence.
record GodelFirstUnprovabilityPrerequisites
    (F : ArithmetisedFormalSystem) : Set₁ where
  field
    substitution : ArithmetisedSubstitution F
    proofRepresentation : ProofRelationRepresentation F
    diagonal : DiagonalLemmaAuthority F
    Consistent : Set
    consistent : Consistent

open GodelFirstUnprovabilityPrerequisites public

-- The two-sided original Gödel result requires a stronger 1-/omega-consistency
-- coordinate for the refutation half.  We leave the exact chosen formulation
-- abstract until the concrete arithmetic system is source-aligned.
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
\data GodelSentenceEqualsRosserSentence : Set where

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

record GodelDiagonalProvabilityBoundary : Set where
  constructor godelDiagonalProvabilityBoundary
  field
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
    true true true true true true true true true false false
