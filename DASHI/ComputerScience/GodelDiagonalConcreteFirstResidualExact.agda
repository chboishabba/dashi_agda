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
--
-- The universal left-inverse is proof-bearing.  Storing only the proposition
-- type or a Bool would erase the exact coordinate that distinguishes a real
-- codec from an unverified candidate.
------------------------------------------------------------------------

record FormulaRetractionAcquisitionTarget : Set₁ where
  constructor formulaRetractionAcquisitionTarget
  field
    selectedProducer : FormulaRetractionProducerKind
    FormulaCarrier : Set
    encodeFormula : FormulaCarrier → Nat
    decodeFormula : Nat → FormulaCarrier
    decodeEncodeFormula :
      (formula : FormulaCarrier) →
      decodeFormula (encodeFormula formula) ≡ formula

open FormulaRetractionAcquisitionTarget public

selectedFormulaRetractionShape :
  (Formula : Set) →
  (encode : Formula → Nat) →
  (decode : Nat → Formula) →
  ((formula : Formula) → decode (encode formula) ≡ formula) →
  FormulaRetractionAcquisitionTarget
selectedFormulaRetractionShape Formula encode decode roundtrip =
  formulaRetractionAcquisitionTarget
    directFormulaNatCodec
    Formula
    encode
    decode
    roundtrip

------------------------------------------------------------------------
-- Exact same-carrier payment for the formal-system code surface.
------------------------------------------------------------------------

record ExactFormulaRetractionPayment
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor exactFormulaRetractionPayment
  field
    decodeFormula : Nat → Godel.Formula F
    decodeCodeFormula :
      (formula : Godel.Formula F) →
      decodeFormula (Godel.codeFormula F formula) ≡ formula

open ExactFormulaRetractionPayment public

paymentAsRetraction :
  (F : Godel.ArithmetisedFormalSystem) →
  ExactFormulaRetractionPayment F →
  Subst.FormulaCodeRetraction F
paymentAsRetraction F payment =
  Subst.formulaCodeRetraction
    (decodeFormula payment)
    (decodeCodeFormula payment)

paymentCompilesSubstitution :
  (F : Godel.ArithmetisedFormalSystem) →
  ExactFormulaRetractionPayment F →
  Godel.ArithmetisedSubstitution F
paymentCompilesSubstitution F payment =
  Subst.compileArithmetisedSubstitution F (paymentAsRetraction F payment)

------------------------------------------------------------------------
-- A generic codec target only pays the formal-system retraction when it is
-- welded to the EXACT Formula/codeFormula carrier.  An isomorphic carrier or
-- an exact codec elsewhere in the repo is not enough.
------------------------------------------------------------------------

record ExactFormulaRetractionWeld
    (F : Godel.ArithmetisedFormalSystem)
    (target : FormulaRetractionAcquisitionTarget) : Set₁ where
  constructor exactFormulaRetractionWeld
  field
    targetToFormal : FormulaCarrier target → Godel.Formula F
    formalToTarget : Godel.Formula F → FormulaCarrier target
    targetToFormalAfterFormalToTarget :
      (formula : Godel.Formula F) →
      targetToFormal (formalToTarget formula) ≡ formula
    encodeCommutes :
      (formula : Godel.Formula F) →
      encodeFormula target (formalToTarget formula)
      ≡ Godel.codeFormula F formula
    decodeEncodedFormalCommutes :
      (formula : Godel.Formula F) →
      targetToFormal
        (decodeFormula target (Godel.codeFormula F formula))
      ≡ formula

open ExactFormulaRetractionWeld public

weldCompilesPayment :
  (F : Godel.ArithmetisedFormalSystem) →
  (target : FormulaRetractionAcquisitionTarget) →
  ExactFormulaRetractionWeld F target →
  ExactFormulaRetractionPayment F
weldCompilesPayment F target weld =
  exactFormulaRetractionPayment
    (λ n → targetToFormal weld (decodeFormula target n))
    (decodeEncodedFormalCommutes weld)

------------------------------------------------------------------------
-- Second residual: internal self-substitution representability.
------------------------------------------------------------------------

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
data PropositionTypeWithoutProofPaysFormulaRetraction : Set where
data CarrierIsomorphismAloneIdentifiesGodelCode : Set where

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

propositionWithoutWitnessDoesNotPay :
  PropositionTypeWithoutProofPaysFormulaRetraction → ⊥
propositionWithoutWitnessDoesNotPay ()

carrierIsomorphismDoesNotIdentifyGodelCode :
  CarrierIsomorphismAloneIdentifiesGodelCode → ⊥
carrierIsomorphismDoesNotIdentifyGodelCode ()

record GodelDiagonalConcreteFirstResidualBoundary : Set where
  constructor godelDiagonalConcreteFirstResidualBoundary
  field
    genericSubstitutionCompilerClosed : Bool
    genericDiagonalCompilerClosed : Bool
    acquisitionTargetStoresUniversalProof : Bool
    weakTautologicalCarrierWeldRetained : Bool
    directFormulaNatCodecRecovered : Bool
    exactStreamCodecImplementationRecovered : Bool
    pairingCodecRecovered : Bool
    differentCarrierRoundtripAccepted : Bool
    witnessOnlyRoundtripAccepted : Bool
    propositionTypeWithoutProofAccepted : Bool
    firstConcreteTargetIsUniversalFormulaLeftInverse : Bool
    sameCarrierGodelCodeWeldRequired : Bool
    secondTargetIsInternalSelfSubstitutionRepresentability : Bool

canonicalGodelDiagonalConcreteFirstResidualBoundary :
  GodelDiagonalConcreteFirstResidualBoundary
canonicalGodelDiagonalConcreteFirstResidualBoundary =
  godelDiagonalConcreteFirstResidualBoundary
    true true true false false false false false false false true true true
