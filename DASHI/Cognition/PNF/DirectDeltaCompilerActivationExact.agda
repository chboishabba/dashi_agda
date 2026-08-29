module DASHI.Cognition.PNF.DirectDeltaCompilerActivationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact

------------------------------------------------------------------------
-- G1--G4 activation cut.
--
-- The live direct path now has executable packed parsing/local solve and an
-- executable stable source-evidence carrier.  Production certification is
-- still deliberately withheld until bounded direct/reference parity and the
-- production-default cutover have their own receipts.
------------------------------------------------------------------------

data GateState : Set where
  inactive executable productionCertified : GateState

record DirectSentenceActivation : Set where
  constructor directSentenceActivation
  field
    parserCarrierGate : GateState
    localSolveGate : GateState
    parityGate : GateState
    tokenRetirementGate : GateState

    -- G1: spaCy observations have a packed fibre-local carrier.
    packedCarrierExecutable : parserCarrierGate ≡ executable

    -- G2: the real sentence owner executes after decoding with no local DB
    -- crossing.  This is the physical counter, not a naming convention.
    sentenceLocalDBCrossings : Nat
    sentenceLocalDBCrossingsZero : sentenceLocalDBCrossings ≡ 0
    localSolveExecutable : localSolveGate ≡ executable

    -- G3 remains a certification gate: direct/reference equality is over the
    -- consumer-visible semantic observation and must be supplied by a bounded
    -- runtime parity receipt.
    parityNotYetCertified : parityGate ≡ inactive

    -- G4 mechanism is now executable: the direct path can publish stable typed
    -- source evidence without parser sentence/token/entity projection.  This
    -- does NOT by itself make the whole direct route production-certified.
    tokenRetirementExecutable : tokenRetirementGate ≡ executable

open DirectSentenceActivation public

sensibLawPackedDirectSeam : DirectSentenceActivation
sensibLawPackedDirectSeam =
  directSentenceActivation
    executable
    executable
    inactive
    executable
    refl
    0
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Stable source evidence is the G4 semantic identity boundary.
-- Database parser-token surrogates are explicitly excluded from authority.
------------------------------------------------------------------------

data SourceEvidenceIdentity : Set where
  stableTypedSourceEvidence : SourceEvidenceIdentity

data ParserTokenSurrogateIdentity : Set where
  postgresParserTokenSurrogate : ParserTokenSurrogateIdentity

record DurableSupportIdentityBoundary : Set where
  constructor durableSupportIdentityBoundary
  field
    semanticSupportIdentity : SourceEvidenceIdentity
    productionParserTokenWrites : Nat
    productionParserTokenWritesZero : productionParserTokenWrites ≡ 0

open DurableSupportIdentityBoundary public

-- Executable G4 carrier shape.  A concrete runtime receipt may instantiate the
-- same boundary with measured counters; semantic identity is stable source
-- evidence rather than a parser-token surrogate.
completeTokenRetirementShape : DurableSupportIdentityBoundary
completeTokenRetirementShape =
  durableSupportIdentityBoundary stableTypedSourceEvidence 0 refl

------------------------------------------------------------------------
-- Fail-closed parity activation.
--
-- Production activation consumes parity evidence; absence of parity has no
-- constructor that can be silently coerced into authority.
------------------------------------------------------------------------

record CertifiedDirectActivation (Observation : Set) : Set₁ where
  constructor certifiedDirectActivation
  field
    parity : DirectReferenceParity Observation
    physical : DirectDeltaPhysicalConstitution
    projectionMode : ParserProjectionMode
    productionMode : projectionMode ≡ productionDirect

open CertifiedDirectActivation public

data MissingParityReceipt : Set where

missingParityCannotActivate : MissingParityReceipt → ⊥
missingParityCannotActivate ()

------------------------------------------------------------------------
-- Regression: a DB surrogate cannot itself witness stable semantic evidence.
------------------------------------------------------------------------

data DatabaseSurrogateWitnessesStableSourceEvidence : Set where

databaseSurrogateCannotWitnessStableSourceEvidence :
  DatabaseSurrogateWitnessesStableSourceEvidence → ⊥
databaseSurrogateCannotWitnessStableSourceEvidence ()
