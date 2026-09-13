module DASHI.ComputerScience.GodelDiagonalConcreteFirstResidualExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelArithmetisedSubstitutionCompilerExact as Subst

------------------------------------------------------------------------
-- CONCRETE DIAGONAL FIRST RESIDUAL
--
-- The generic compiler chain is now owned:
--
--   formula-code retraction
--      -> ArithmetisedSubstitution
--   + representable x ↦ A(sub(x,x))
--      -> DiagonalLemmaAuthority.
--
-- This module freezes the remaining concrete producer choices so future proof
-- search does not reopen Gödel I/II while the code/syntax seam is still open.
------------------------------------------------------------------------

data FormulaRetractionProducerKind : Set where
  directFormulaNatCodec : FormulaRetractionProducerKind
  prefixSyntaxViaExactStreamCodec : FormulaRetractionProducerKind
  recursiveSyntaxViaPairingCodec : FormulaRetractionProducerKind

data ProducerReadiness : Set where
  executableAndRoundtripOwned : ProducerReadiness
  contractOnly : ProducerReadiness
  notRecovered : ProducerReadiness

record FormulaRetractionProducerStatus : Set where
  constructor formulaRetractionProducerStatus
  field
    producerKind : FormulaRetractionProducerKind
    readiness : ProducerReadiness
    sameArithmeticFormulaCarrier : Bool
    producesNatCode : Bool
    provesLeftInverseForEveryFormula : Bool

open FormulaRetractionProducerStatus public

directStatus : FormulaRetractionProducerStatus
directStatus =
  formulaRetractionProducerStatus
    directFormulaNatCodec notRecovered false true false

streamStatus : FormulaRetractionProducerStatus
streamStatus =
  formulaRetractionProducerStatus
    prefixSyntaxViaExactStreamCodec contractOnly false false false

pairingStatus : FormulaRetractionProducerStatus
pairingStatus =
  formulaRetractionProducerStatus
    recursiveSyntaxViaPairingCodec notRecovered false true false

------------------------------------------------------------------------
-- Least-privilege selected acquisition target.
------------------------------------------------------------------------

record FormulaRetractionAcquisitionTarget : Set where
  constructor formulaRetractionAcquisitionTarget
  field
    selectedProducer : FormulaRetractionProducerKind
    ConcreteArithmeticSystem : Set₁
    FormulaCarrier : Set
    encodeFormula : FormulaCarrier → Nat
    decodeFormula : Nat → FormulaCarrier
    requiredLaw : Set
    lawIsExactLeftInverse : Bool
    lawIsExactLeftInverseIsTrue : lawIsExactLeftInverse ≡ true

-- The current selected theorem shape is independent of the eventual encoding
-- implementation: recover the exact left inverse on the SAME arithmetic
-- formula carrier.  No claim is made that a producer is presently inhabited.
selectedFormulaRetractionShape :
  (System : Set₁) →
  (Formula : Set) →
  (encode : Formula → Nat) →
  (decode : Nat → Formula) →
  ((formula : Formula) → decode (encode formula) ≡ formula) →
  FormulaRetractionAcquisitionTarget
selectedFormulaRetractionShape System Formula encode decode roundtrip =
  formulaRetractionAcquisitionTarget
    directFormulaNatCodec
    System
    Formula
    encode
    decode
    ((formula : Formula) → decode (encode formula) ≡ formula)
    true
    refl

------------------------------------------------------------------------
-- Once the target is instantiated on an ArithmetisedFormalSystem, the
-- downstream substitution and diagonal compilers are already available.
------------------------------------------------------------------------

record ExactFormulaRetractionPayment
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor exactFormulaRetractionPayment
  field
    retraction : Subst.FormulaCodeRetraction F

open ExactFormulaRetractionPayment public

paymentCompilesSubstitution :
  (F : Godel.ArithmetisedFormalSystem) →
  ExactFormulaRetractionPayment F →
  Godel.ArithmetisedSubstitution F
paymentCompilesSubstitution F payment =
  Subst.compileArithmetisedSubstitution F (retraction payment)

record ExactDiagonalPayment
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor exactDiagonalPayment
  field
    formulaRetraction : Subst.FormulaCodeRetraction F
    selfSubstitutionRepresentation :
      Godel.DiagonalFormulaConstruction F
        (Subst.compileArithmetisedSubstitution F formulaRetraction)

open ExactDiagonalPayment public

paymentCompilesDiagonalLemma :
  (F : Godel.ArithmetisedFormalSystem) →
  ExactDiagonalPayment F →
  Godel.DiagonalLemmaAuthority F
paymentCompilesDiagonalLemma F payment =
  Godel.diagonalLemmaFromConstruction
    F
    (Subst.compileArithmetisedSubstitution F (formulaRetraction payment))
    (selfSubstitutionRepresentation payment)

------------------------------------------------------------------------
-- Introspective firewalls.
------------------------------------------------------------------------

data ExactCodecOnDifferentCarrierPaysFormulaRetraction : Set where
data CodecContractWithoutImplementationPaysFormulaRetraction : Set where
data OneWitnessRoundtripPaysUniversalFormulaRetraction : Set where
data FormulaRetractionPaysSelfSubstitutionRepresentability : Set where

otherCarrierCodecDoesNotPayArithmeticFormulaRetraction :
  ExactCodecOnDifferentCarrierPaysFormulaRetraction → ⊥
otherCarrierCodecDoesNotPayArithmeticFormulaRetraction ()

codecContractWithoutImplementationDoesNotPay :
  CodecContractWithoutImplementationPaysFormulaRetraction → ⊥
codecContractWithoutImplementationDoesNotPay ()

oneWitnessDoesNotPayUniversalRoundtrip :
  OneWitnessRoundtripPaysUniversalFormulaRetraction → ⊥
oneWitnessDoesNotPayUniversalRoundtrip ()

formulaRetractionDoesNotPayInternalRepresentation :
  FormulaRetractionPaysSelfSubstitutionRepresentability → ⊥
formulaRetractionDoesNotPayInternalRepresentation ()

record GodelDiagonalConcreteFirstResidualBoundary : Set where
  constructor godelDiagonalConcreteFirstResidualBoundary
  field
    genericSubstitutionCompilerClosed : Bool
    genericDiagonalCompilerClosed : Bool
    directFormulaNatCodecRecovered : Bool
    exactStreamCodecImplementationRecovered : Bool
    pairingCodecRecovered : Bool
    differentCarrierRoundtripAccepted : Bool
    witnessOnlyRoundtripAccepted : Bool
    firstConcreteTargetIsUniversalFormulaLeftInverse : Bool
    secondTargetIsInternalSelfSubstitutionRepresentability : Bool

canonicalGodelDiagonalConcreteFirstResidualBoundary :
  GodelDiagonalConcreteFirstResidualBoundary
canonicalGodelDiagonalConcreteFirstResidualBoundary =
  godelDiagonalConcreteFirstResidualBoundary
    true true false false false false false true true
