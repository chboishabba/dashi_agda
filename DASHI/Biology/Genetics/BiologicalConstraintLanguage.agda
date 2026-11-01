module DASHI.Biology.Genetics.BiologicalConstraintLanguage where

-- Biology can be viewed as a constrained symbolic/control language whose
-- symbols are physically realised by chemistry.  The language and its chemical
-- implementation are kept separate.
record BiologicalPushdownSystem : Set₁ where
  field
    Symbol       : Set
    StackSymbol  : Set
    ControlState : Set
    Input        : Set
    Stack        : Set

    initialControl : ControlState
    initialStack   : Stack

    transition :
      ControlState → Symbol → Stack → ControlState → Stack → Set

    Parses    : Input → Set
    Accepted  : Input → Set
    WellTyped : Input → Set

record ChemicalLanguageRealisation
  (L : BiologicalPushdownSystem) : Set₁ where
  open BiologicalPushdownSystem L
  field
    ChemicalState : Set
    Reaction      : Set
    Environment   : Set

    encodeInput   : Input → ChemicalState
    realiseSymbol : Environment → Symbol → Reaction
    execute       : Environment → Reaction → ChemicalState → ChemicalState

    ChemicallyAdmissible : Environment → ChemicalState → Set

    acceptedHasAdmissibleRealisation :
      (environment : Environment) (input : Input) →
      Accepted input →
      ChemicallyAdmissible environment (encodeInput input)

-- Syntax alone is not biological execution, and chemistry alone does not supply
-- semantic or control interpretation.  The bridge carries both directions.
record LanguageChemistryBoundary
  (L : BiologicalPushdownSystem) : Set₁ where
  field
    SyntaxToChemistry : Set
    ChemistryToControlMeaning : Set

    syntaxRealisationWitness : SyntaxToChemistry
    controlMeaningWitness    : ChemistryToControlMeaning

    grammarIsNotGenomeBlueprint : Set
    chemicalOccurrenceIsNotSemanticInstruction : Set
