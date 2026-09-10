module DASHI.ComputerScience.GodelConcreteDiagonalCurrentCutExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CURRENT THEOREM CUT AFTER CONCRETE SYNTAX/CODEC REDUCTION
--
-- This owner is intentionally tiny.  It prevents downstream planning from
-- reopening serialization, generic diagonalization, or historical theorem
-- inventory once those have been reduced to the two live theorem-bearing
-- coordinates below.
------------------------------------------------------------------------

data LiveDiagonalResidual : Set where
  sourceNativeRepresentabilityAlignment
  base12SelfSubstitutionPrimitiveRecursive : LiveDiagonalResidual

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
    liveResiduals : List LiveDiagonalResidual
    concreteDiagonalLemmaKernelCertified : Bool

canonicalCurrentDiagonalCut : CurrentDiagonalCut
canonicalCurrentDiagonalCut =
  currentDiagonalCut
    true true true true true true true
    (sourceNativeRepresentabilityAlignment ∷
     base12SelfSubstitutionPrimitiveRecursive ∷ [])
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceWrittenCodecMeansKernelCertified : Set where
data ClosedSerializationMeansClosedDiagonalLemma : Set where

data SourceRepresentabilityMeansCustomBase12PR : Set where

sourceWrittenDoesNotMeanCertified :
  SourceWrittenCodecMeansKernelCertified → ⊥
sourceWrittenDoesNotMeanCertified ()

serializationDoesNotCloseDiagonal :
  ClosedSerializationMeansClosedDiagonalLemma → ⊥
serializationDoesNotCloseDiagonal ()

historicalRepresentabilityDoesNotPayCustomCode :
  SourceRepresentabilityMeansCustomBase12PR → ⊥
historicalRepresentabilityDoesNotPayCustomCode ()
