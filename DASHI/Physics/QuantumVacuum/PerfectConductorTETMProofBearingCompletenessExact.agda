module DASHI.Physics.QuantumVacuum.PerfectConductorTETMProofBearingCompletenessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.PerfectConductorTETMGenerationCompletenessBidiExact as Bidi
import DASHI.Physics.QuantumVacuum.PerfectConductorPlateModePDECutsetExact as PDE

------------------------------------------------------------------------
-- PROOF-BEARING TE/TM COMPLETENESS
--
-- The older PDE completion record carries several semantic coordinates merely
-- as Set labels.  This owner separates proposition from evidence.  No
-- completeness theorem is invented: a caller must supply actual inhabitants.
------------------------------------------------------------------------

record ProofBearingPhysicalModeCompleteness
    (G : Bidi.ForwardPlateModeGenerator) : Set₁ where
  field
    PhysicalMode : Set
    represents : Bidi.Candidate G → PhysicalMode → Set

    everyPhysicalModeGenerated :
      (mode : PhysicalMode) →
      Σ (Bidi.Candidate G) (λ candidate → represents candidate mode)

    ZeroSector : PhysicalMode → Set

    TETMUniqueAwayFromZeroSector : Set
    teTmUniqueAwayFromZeroSectorEvidence : TETMUniqueAwayFromZeroSector

    ZeroSectorCountingCorrect : Set
    zeroSectorCountingCorrectEvidence : ZeroSectorCountingCorrect

    TransverseLabelsComplete : Set
    transverseLabelsCompleteEvidence : TransverseLabelsComplete

    LongitudinalIndicesComplete : Set
    longitudinalIndicesCompleteEvidence : LongitudinalIndicesComplete

    FiniteEnergyDomainMatches : Set
    finiteEnergyDomainMatchesEvidence : FiniteEnergyDomainMatches

    SameBoundaryProblemAsGenerator : Set
    sameBoundaryProblemAsGeneratorEvidence : SameBoundaryProblemAsGenerator

    reading : String

open ProofBearingPhysicalModeCompleteness public

asBidiPhysicalModeCompleteness :
  ∀ {G} →
  ProofBearingPhysicalModeCompleteness G →
  Bidi.PhysicalModeCompleteness G
asBidiPhysicalModeCompleteness C = record
  { Bidi.PhysicalMode = PhysicalMode C
  ; Bidi.represents = represents C
  ; Bidi.everyPhysicalModeGenerated = everyPhysicalModeGenerated C
  ; Bidi.ZeroSector = ZeroSector C
  ; Bidi.teTmUniqueAwayFromZeroSector = TETMUniqueAwayFromZeroSector C
  ; Bidi.zeroSectorCountingCorrect = ZeroSectorCountingCorrect C
  ; Bidi.transverseLabelsComplete = TransverseLabelsComplete C
  ; Bidi.longitudinalIndicesComplete = LongitudinalIndicesComplete C
  ; Bidi.finiteEnergyDomainMatches = FiniteEnergyDomainMatches C
  ; Bidi.reading = reading C
  }

------------------------------------------------------------------------
-- PDE-facing proof-bearing completeness receipt.
------------------------------------------------------------------------

record ProofBearingTETMCompletenessReceipt : Set₁ where
  field
    PhysicalMode : Set
    TE TM : PhysicalMode → Set
    longitudinalIndex : PhysicalMode → Nat
    zeroSector : PhysicalMode → Set

    EveryPhysicalModeTEorTM : Set
    everyPhysicalModeTEorTMEvidence : EveryPhysicalModeTEorTM

    NoDoubleCountingAwayFromZeroSector : Set
    noDoubleCountingAwayFromZeroSectorEvidence :
      NoDoubleCountingAwayFromZeroSector

    ZeroSectorCountingCorrect : Set
    zeroSectorCountingCorrectEvidence : ZeroSectorCountingCorrect

    TransverseCompleteness : Set
    transverseCompletenessEvidence : TransverseCompleteness

    LongitudinalCompleteness : Set
    longitudinalCompletenessEvidence : LongitudinalCompleteness

    reading : String

open ProofBearingTETMCompletenessReceipt public

asLegacyTETMCompletenessReceipt :
  ProofBearingTETMCompletenessReceipt →
  PDE.TETMCompletenessReceipt
asLegacyTETMCompletenessReceipt C = record
  { PDE.PhysicalMode = PhysicalMode C
  ; PDE.TE = TE C
  ; PDE.TM = TM C
  ; PDE.longitudinalIndex = longitudinalIndex C
  ; PDE.zeroSector = zeroSector C
  ; PDE.everyPhysicalModeTEorTM = EveryPhysicalModeTEorTM C
  ; PDE.noDoubleCountingAwayFromZeroSector =
      NoDoubleCountingAwayFromZeroSector C
  ; PDE.zeroSectorCountingCorrect = ZeroSectorCountingCorrect C
  ; PDE.transverseCompleteness = TransverseCompleteness C
  ; PDE.longitudinalCompleteness = LongitudinalCompleteness C
  ; PDE.reading = reading C
  }

------------------------------------------------------------------------
-- The adapters preserve the legacy surfaces but do not allow the proposition
-- type alone to stand in for its witness.
------------------------------------------------------------------------

data BareCompletenessSetAutomaticallySuppliesEvidence : Set where

bareSetDoesNotSupplyCompletenessEvidence :
  BareCompletenessSetAutomaticallySuppliesEvidence → ⊥
bareSetDoesNotSupplyCompletenessEvidence ()

record Status : Set where
  field
    proofBearingCompletenessBoundaryOwned : Bool
    bidiLegacyAdapterOwned : Bool
    pdeLegacyAdapterOwned : Bool
    actualContinuumCompletenessClosed : Bool

    proofBearingCompletenessBoundaryOwnedIsTrue :
      proofBearingCompletenessBoundaryOwned ≡ true
    bidiLegacyAdapterOwnedIsTrue : bidiLegacyAdapterOwned ≡ true
    pdeLegacyAdapterOwnedIsTrue : pdeLegacyAdapterOwned ≡ true
    actualContinuumCompletenessClosedIsFalse :
      actualContinuumCompletenessClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { proofBearingCompletenessBoundaryOwned = true
  ; bidiLegacyAdapterOwned = true
  ; pdeLegacyAdapterOwned = true
  ; actualContinuumCompletenessClosed = false
  ; proofBearingCompletenessBoundaryOwnedIsTrue = refl
  ; bidiLegacyAdapterOwnedIsTrue = refl
  ; pdeLegacyAdapterOwnedIsTrue = refl
  ; actualContinuumCompletenessClosedIsFalse = refl
  }
