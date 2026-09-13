module DASHI.ComputerScience.GodelArithmetisedFormalSystemShapeAuthorityExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel

------------------------------------------------------------------------
-- SHAPE AUTHORITY FOR THE ABSTRACT ARITHMETISED FORMAL-SYSTEM ABI
--
-- `Godel.ArithmetisedFormalSystem` deliberately keeps syntax abstract, but its
-- comments distinguish unary formulas, binary formulas and closed sentences.
-- An external adapter must not satisfy that interface by erasing those
-- distinctions (for example Formula = Sentence = all external formulas).
--
-- This companion record makes the shape coordinate proof-bearing without
-- breaking the existing generic compiler ABI.
------------------------------------------------------------------------

record FormulaSentenceShapeAuthority
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor formulaSentenceShapeAuthority
  field
    Variable : Set
    distinguishedUnary : Variable
    distinguishedBinaryLeft : Variable
    distinguishedBinaryRight : Variable

    FreeInUnary : Variable → Godel.Formula F → Set
    FreeInBinary : Variable → Godel.BinaryFormula F → Set

    unaryHasNoOtherFreeVariable :
      (v : Variable) →
      (φ : Godel.Formula F) →
      FreeInUnary v φ →
      v ≡ distinguishedUnary

    binaryHasNoOtherFreeVariable :
      (v : Variable) →
      (φ : Godel.BinaryFormula F) →
      FreeInBinary v φ →
      (v ≡ distinguishedBinaryLeft) ⊎
      (v ≡ distinguishedBinaryRight)

    binaryDistinguishedVariablesDistinct :
      distinguishedBinaryLeft ≡ distinguishedBinaryRight → ⊥

open FormulaSentenceShapeAuthority public

------------------------------------------------------------------------
-- Adapter receipt: source syntax must pay the actual shape relation used by
-- the adapter.  This is deliberately separate from theorem/provability
-- transport and from numeric coding.
------------------------------------------------------------------------

record ExternalSyntaxShapeWeld
    (F : Godel.ArithmetisedFormalSystem)
    (shape : FormulaSentenceShapeAuthority F) : Set₁ where
  constructor externalSyntaxShapeWeld
  field
    externalCarrierName : String
    sourceFreeVariableRelationNamed : Bool
    unaryCarrierIsSourceRestricted : Bool
    binaryCarrierIsSourceRestricted : Bool
    sentenceCarrierIsSourceClosed : Bool
    instantiateUsesSourceSubstitution : Bool
    instantiate2UsesSourceSubstitution : Bool
    sameObjectShapeEvidenceOwned : Bool

open ExternalSyntaxShapeWeld public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CommentedUnaryFormulaImpliesTypedUnaryCarrier : Set where
data DifferentNamesImplyDifferentShape : Set where
data FormulaEqualsSentenceIsAlwaysSound : Set where

aCommentDoesNotSupplyShapeProof :
  CommentedUnaryFormulaImpliesTypedUnaryCarrier → ⊥
aCommentDoesNotSupplyShapeProof ()

namesDoNotSupplyShapeSeparation :
  DifferentNamesImplyDifferentShape → ⊥
namesDoNotSupplyShapeSeparation ()

formulaSentenceCollapseIsNotGenerallySound :
  FormulaEqualsSentenceIsAlwaysSound → ⊥
formulaSentenceCollapseIsNotGenerallySound ()

record GodelArithmetisedFormalSystemShapeBoundary : Set where
  constructor godelArithmetisedFormalSystemShapeBoundary
  field
    originalABIStillAvailable : Bool
    proofBearingShapeCompanionOwned : Bool
    sourceAdapterMustRetainFreeVariableShape : Bool
    formulaSentenceCollapseAcceptedWithoutWeld : Bool

canonicalGodelArithmetisedFormalSystemShapeBoundary :
  GodelArithmetisedFormalSystemShapeBoundary
canonicalGodelArithmetisedFormalSystemShapeBoundary =
  godelArithmetisedFormalSystemShapeBoundary true true true false
