module DASHI.ComputerScience.GodelConcreteDiagonalCurrentCutExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT CANONICAL DIAGONAL CUT
--
-- The executable base-12 code is retained as a useful implementation lane,
-- but its PR proof is NOT a mandatory prerequisite for the shortest theorem
-- route.  The canonical route may use the source-native Gödel coding for which
-- substitution primitive-recursiveness belongs to the historical construction.
------------------------------------------------------------------------

data LiveDiagonalResidual : Set where
  sourceNativeSubstitutionAndTheoremVAlignment
  representedFunctionPrecompositionClosure : LiveDiagonalResidual

data OptionalDiagonalProducerResidual : Set where
  base12SelfSubstitutionPrimitiveRecursive
  base12ToSourceNativeSameCodeWeld : OptionalDiagonalProducerResidual

record CurrentDiagonalCut : Set where
  constructor currentDiagonalCut
  field
    rawArithmeticSyntaxSourceWritten : Bool
    captureAvoidingInstantiationSourceWritten : Bool
    prefixStreamRoundtripSourceWritten : Bool
    base12NatRetractionSourceWritten : Bool
    genericArithmetisedSubstitutionCompilerOwned : Bool
    genericDiagonalCompilerOwned : Bool
    primitiveRecursiveRepresentabilityCompilerOwned : Bool
    theoremVRelationGraphAdapterOwned : Bool
    canonicalLiveResiduals : List LiveDiagonalResidual
    optionalProducerResiduals : List OptionalDiagonalProducerResidual
    base12PRIsMandatoryForDiagonal : Bool
    concreteDiagonalLemmaKernelCertified : Bool

canonicalCurrentDiagonalCut : CurrentDiagonalCut
canonicalCurrentDiagonalCut =
  currentDiagonalCut
    true true true true true true true true
    (sourceNativeSubstitutionAndTheoremVAlignment ∷
     representedFunctionPrecompositionClosure ∷ [])
    (base12SelfSubstitutionPrimitiveRecursive ∷
     base12ToSourceNativeSameCodeWeld ∷ [])
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceWrittenCodecMeansKernelCertified : Set where
data ClosedSerializationMeansClosedDiagonalLemma : Set where
data SourceRepresentabilityMeansCustomBase12PR : Set where
data OptionalBase12ProducerIsMandatoryTheoremDebt : Set where

sourceWrittenDoesNotMeanCertified :
  SourceWrittenCodecMeansKernelCertified → ⊥
sourceWrittenDoesNotMeanCertified ()

serializationDoesNotCloseDiagonal :
  ClosedSerializationMeansClosedDiagonalLemma → ⊥
serializationDoesNotCloseDiagonal ()

historicalRepresentabilityDoesNotPayCustomCode :
  SourceRepresentabilityMeansCustomBase12PR → ⊥
historicalRepresentabilityDoesNotPayCustomCode ()

base12ProducerDoesNotBecomeMandatory :
  OptionalBase12ProducerIsMandatoryTheoremDebt → ⊥
base12ProducerDoesNotBecomeMandatory ()
