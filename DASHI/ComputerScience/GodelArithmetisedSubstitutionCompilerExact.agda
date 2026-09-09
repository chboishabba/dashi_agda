module DASHI.ComputerScience.GodelArithmetisedSubstitutionCompilerExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel

------------------------------------------------------------------------
-- LEAST-PRIVILEGE CODE RETRACTION -> ARITHMETISED SUBSTITUTION
--
-- A Gödel code does not need a globally invertible Nat codec for the diagonal
-- compiler.  It is sufficient to recover every actually encoded unary formula:
--
--   decodeFormula (codeFormula A) = A.
--
-- This is the same abstract retraction shape used elsewhere by exact codecs,
-- but no binary/ternary carrier is identified with arithmetic syntax here.
------------------------------------------------------------------------

record FormulaCodeRetraction
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor formulaCodeRetraction
  field
    decodeFormula : Nat → Godel.Formula F
    decodeCodeFormula :
      (formula : Godel.Formula F) →
      decodeFormula (Godel.codeFormula F formula) ≡ formula

open FormulaCodeRetraction public

substituteCodeFromRetraction :
  (F : Godel.ArithmetisedFormalSystem) →
  FormulaCodeRetraction F →
  Nat → Nat → Nat
substituteCodeFromRetraction F R formulaCode n =
  Godel.codeSentence F
    (Godel.instantiate F
      (decodeFormula R formulaCode)
      (Godel.numeral F n))

substitutionExactFromRetraction :
  (F : Godel.ArithmetisedFormalSystem) →
  (R : FormulaCodeRetraction F) →
  (formula : Godel.Formula F) →
  (n : Nat) →
  substituteCodeFromRetraction F R (Godel.codeFormula F formula) n
  ≡
  Godel.codeSentence F
    (Godel.instantiate F formula (Godel.numeral F n))
substitutionExactFromRetraction F R formula n
  rewrite decodeCodeFormula R formula = refl

compileArithmetisedSubstitution :
  (F : Godel.ArithmetisedFormalSystem) →
  FormulaCodeRetraction F →
  Godel.ArithmetisedSubstitution F
compileArithmetisedSubstitution F R =
  record
    { substituteCode = substituteCodeFromRetraction F R
    ; substitutionExact = substitutionExactFromRetraction F R
    }

------------------------------------------------------------------------
-- DIAGONAL CAPSTONE
--
-- Once the same concrete formal system also represents
--
--   x ↦ A(sub(x,x))
--
-- as required by DiagonalFormulaConstruction, the already-owned generic
-- diagonal compiler produces the object-language fixed-point theorem.
------------------------------------------------------------------------

record ConcreteDiagonalProducer
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor concreteDiagonalProducer
  field
    formulaRetraction : FormulaCodeRetraction F
    diagonalConstruction :
      Godel.DiagonalFormulaConstruction F
        (compileArithmetisedSubstitution F formulaRetraction)

open ConcreteDiagonalProducer public

compileConcreteDiagonalProducer :
  (F : Godel.ArithmetisedFormalSystem) →
  ConcreteDiagonalProducer F →
  Godel.DiagonalLemmaAuthority F
compileConcreteDiagonalProducer F producer =
  Godel.diagonalLemmaFromConstruction
    F
    (compileArithmetisedSubstitution F (formulaRetraction producer))
    (diagonalConstruction producer)

------------------------------------------------------------------------
-- CURRENT REPO FRONTIER
------------------------------------------------------------------------

data DiagonalConcreteResidual : Set where
  concreteArithmeticFormalSystem : DiagonalConcreteResidual
  formulaCodeLeftInverse : DiagonalConcreteResidual
  selfSubstitutionRepresentability : DiagonalConcreteResidual

data ExistingScalarGodelCoordinatePaysFormulaRetraction : Set where
data StateEncodeDecodePostulatesPayRoundtrip : Set where

godelScalarCoordinateDoesNotPayFormulaRetraction :
  ExistingScalarGodelCoordinatePaysFormulaRetraction → ⊥
godelScalarCoordinateDoesNotPayFormulaRetraction ()

postulatedEncodeDecodeWithoutRoundtripDoesNotPayRetraction :
  StateEncodeDecodePostulatesPayRoundtrip → ⊥
postulatedEncodeDecodeWithoutRoundtripDoesNotPayRetraction ()

record DiagonalConcreteFrontier : Set where
  constructor diagonalConcreteFrontier
  field
    genericSubstitutionCompilerOwned : Bool
    genericDiagonalCompilerOwned : Bool
    concreteArithmeticFormalSystemRecovered : Bool
    formulaCodeRetractionRecovered : Bool
    selfSubstitutionRepresentabilityRecovered : Bool
    scalarGodelCoordinatePromotedToFormulaDecoder : Bool
    monsterStateCodecPromotedWithoutRoundtrip : Bool

canonicalDiagonalConcreteFrontier : DiagonalConcreteFrontier
canonicalDiagonalConcreteFrontier =
  diagonalConcreteFrontier
    true true false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FormulaRetractionAloneImpliesDiagonalLemma : Set where
data ExecutableCodeSubstitutionImpliesRepresentability : Set where
data ExactCodecRoundtripTransfersArithmeticMeaning : Set where

formulaRetractionAloneDoesNotSupplyDiagonalLemma :
  FormulaRetractionAloneImpliesDiagonalLemma → ⊥
formulaRetractionAloneDoesNotSupplyDiagonalLemma ()

codeSubstitutionDoesNotSupplyInternalRepresentability :
  ExecutableCodeSubstitutionImpliesRepresentability → ⊥
codeSubstitutionDoesNotSupplyInternalRepresentability ()

codecShapeReuseDoesNotTransferArithmeticMeaning :
  ExactCodecRoundtripTransfersArithmeticMeaning → ⊥
codecShapeReuseDoesNotTransferArithmeticMeaning ()
