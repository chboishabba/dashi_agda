module DASHI.Foundations.Wette1969HistoricalSignatureExact where

------------------------------------------------------------------------
-- WETTE 1969 HISTORICAL SIGNATURE
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Source loci:
--   pp. 142--143  generic word / word-term / formula grammar and signature;
--   pp. 147--148  intended meanings of constants, functors and relators;
--   pp. 193--194  addendum replacing A by _A in the crucial rule surface.
--
-- Kreisel--Zucker explicitly review the modified p.193 version:
-- JSL 37(1), 1972, pp. 203--204, DOI: 10.2307/2272630.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

------------------------------------------------------------------------
-- Seven constants and eight functors from the source signature.
-- Constructor names encode Wette's stated intended reading, not a claim that
-- the pure symbol already possesses that semantics before interpretation.
------------------------------------------------------------------------

data HistoricalConstant : Set where
  emptyConstant : HistoricalConstant
  zeroConstant : HistoricalConstant
  variableKernel : HistoricalConstant
  predicateMarkKernel : HistoricalConstant
  orderPredicateConstant : HistoricalConstant
  verumConstant : HistoricalConstant
  falsumConstant : HistoricalConstant

data HistoricalFunctor : Set where
  successorFunctor : HistoricalFunctor
  juxtapositionFunctor : HistoricalFunctor
  implicationFunctor : HistoricalFunctor
  conjunctionFunctor : HistoricalFunctor
  disjunctionFunctor : HistoricalFunctor
  particularizationFunctor : HistoricalFunctor
  generalizationFunctor : HistoricalFunctor
  recursionFunctor : HistoricalFunctor

functorArity : HistoricalFunctor → Nat
functorArity successorFunctor = 1
functorArity juxtapositionFunctor = 2
functorArity implicationFunctor = 2
functorArity conjunctionFunctor = 2
functorArity disjunctionFunctor = 2
functorArity particularizationFunctor = 2
functorArity generalizationFunctor = 2
functorArity recursionFunctor = 2

------------------------------------------------------------------------
-- Modified 16-relator signature.
--
-- The first fifteen are the p.142/p.148 surface.  The final constructor is the
-- p.193 addendum's unary _A relator: "w is an assertion schema over natural
-- numbers without predicate quantification".  This is the version relevant to
-- Kreisel--Zucker's review and to Wette's final stated 97-rule count.
------------------------------------------------------------------------

data HistoricalRelator : Set where
  naturalNumberRelator : HistoricalRelator
  naturalVariableRelator : HistoricalRelator
  naturalTermRelator : HistoricalRelator
  assertionSchemaRelator : HistoricalRelator
  inequalityRelator : HistoricalRelator
  duplicationRelator : HistoricalRelator
  predicateMarkArityRelator : HistoricalRelator
  termTupleRelator : HistoricalRelator
  freeForSyntaxRelator : HistoricalRelator
  distinctVariableTupleRelator : HistoricalRelator
  predicateSchemaRelator : HistoricalRelator
  implicationDerivabilityRelator : HistoricalRelator
  abbreviationRelator : HistoricalRelator
  juxtapositionResultRelator : HistoricalRelator
  substitutionRelator : HistoricalRelator
  assertionSchemaNoPredicateQuantificationRelator : HistoricalRelator

relatorArity : HistoricalRelator → Nat
relatorArity naturalNumberRelator = 1
relatorArity naturalVariableRelator = 1
relatorArity naturalTermRelator = 1
relatorArity assertionSchemaRelator = 1
relatorArity inequalityRelator = 2
relatorArity duplicationRelator = 2
relatorArity predicateMarkArityRelator = 2
relatorArity termTupleRelator = 2
relatorArity freeForSyntaxRelator = 2
relatorArity distinctVariableTupleRelator = 2
relatorArity predicateSchemaRelator = 2
relatorArity implicationDerivabilityRelator = 2
relatorArity abbreviationRelator = 2
relatorArity juxtapositionResultRelator = 3
relatorArity substitutionRelator = 4
relatorArity assertionSchemaNoPredicateQuantificationRelator = 1

------------------------------------------------------------------------
-- Exact pure syntax.
--
-- Wette first defines words over the constants/functors, then word terms by
-- adjoining finitely many word variables, and only then formulas by applying a
-- relator to the exact number of word terms dictated by its arity.  Keeping
-- Word and WordTerm distinct matters: the rule schemata range over word terms,
-- while substitution of concrete words for the word variables yields words.
------------------------------------------------------------------------

data Word : Set where
  constantWord : HistoricalConstant → Word
  unaryWord : (f : HistoricalFunctor) → functorArity f ≡ 1 → Word → Word
  binaryWord :
    (f : HistoricalFunctor) → functorArity f ≡ 2 → Word → Word → Word

-- Wette's specialized calculus uses nineteen word variables in rule schemata.
WordVariable : Set
WordVariable = Fin 19

data WordTerm : Set where
  variableWordTerm : WordVariable → WordTerm
  constantWordTerm : HistoricalConstant → WordTerm
  unaryWordTerm :
    (f : HistoricalFunctor) → functorArity f ≡ 1 → WordTerm → WordTerm
  binaryWordTerm :
    (f : HistoricalFunctor) →
    functorArity f ≡ 2 →
    WordTerm → WordTerm → WordTerm

record Formula : Set where
  constructor historicalFormula
  field
    relator : HistoricalRelator
    arguments : Vec WordTerm (relatorArity relator)

open Formula public

------------------------------------------------------------------------
-- Exact finite-cardinality facts are represented independently of constructor
-- enumeration proofs; those proofs can be added when a finite-enumeration
-- owner is attached.  These are source transcriptions, not cardinality axioms.
------------------------------------------------------------------------

record HistoricalSignatureCounts : Set where
  constructor historicalSignatureCounts
  field
    constantCount : Nat
    functorCount : Nat
    wordVariableCount : Nat
    modifiedRelatorCount : Nat
    finalModifiedRuleCount : Nat
    alternateRelatorCount : Nat
    alternateRuleCount : Nat
    mainRulePremiseCount : Nat

canonicalHistoricalSignatureCounts : HistoricalSignatureCounts
canonicalHistoricalSignatureCounts =
  historicalSignatureCounts 7 8 19 16 97 17 129 27

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record Wette1969HistoricalSignatureBoundary : Set where
  constructor wette1969HistoricalSignatureBoundary
  field
    primarySignatureTranscriptionStarted : Bool
    primarySignatureTranscriptionStartedIsTrue :
      primarySignatureTranscriptionStarted ≡ true

    wordTermsSeparatedFromConcreteWords : Bool
    wordTermsSeparatedFromConcreteWordsIsTrue :
      wordTermsSeparatedFromConcreteWords ≡ true

    formulaRelatorArityEnforcedByType : Bool
    formulaRelatorArityEnforcedByTypeIsTrue :
      formulaRelatorArityEnforcedByType ≡ true

    modifiedP193SignatureUsedAsCanonicalAuditSurface : Bool
    modifiedP193SignatureUsedAsCanonicalAuditSurfaceIsTrue :
      modifiedP193SignatureUsedAsCanonicalAuditSurface ≡ true

    pureSyntaxAlreadySuppliesIntendedSemantics : Bool
    pureSyntaxAlreadySuppliesIntendedSemanticsIsFalse :
      pureSyntaxAlreadySuppliesIntendedSemantics ≡ false

    signatureTranscriptionAlreadySuppliesAll97RuleBodies : Bool
    signatureTranscriptionAlreadySuppliesAll97RuleBodiesIsFalse :
      signatureTranscriptionAlreadySuppliesAll97RuleBodies ≡ false

canonicalWette1969HistoricalSignatureBoundary :
  Wette1969HistoricalSignatureBoundary
canonicalWette1969HistoricalSignatureBoundary =
  wette1969HistoricalSignatureBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
