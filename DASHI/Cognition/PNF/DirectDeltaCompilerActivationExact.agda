module DASHI.Cognition.PNF.DirectDeltaCompilerActivationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact

------------------------------------------------------------------------
-- G1--G4 activation cut.
--
-- This module is deliberately narrower than the architecture constitution.
-- It separates the executable G1/G2 seam from the still-required durable G4
-- evidence migration.  In particular, installing a direct code path is not
-- sufficient evidence that production has retired parser-token persistence.
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

    -- G3/G4 are not promoted merely because G1/G2 exist.  They require their
    -- own runtime receipts before production certification.
    parityNotYetCertified : parityGate ≡ inactive
    tokenRetirementNotYetCertified : tokenRetirementGate ≡ inactive

open DirectSentenceActivation public

sensibLawPackedDirectSeam : DirectSentenceActivation
sensibLawPackedDirectSeam =
  directSentenceActivation
    executable
    executable
    inactive
    inactive
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

-- A complete G4 witness has this shape.  The runtime must construct it from
-- the durable source-evidence carrier; this file does not fabricate that
-- receipt while support relations still depend on parser token ids.
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
