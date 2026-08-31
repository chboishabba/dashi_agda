module DASHI.Cognition.PNF.SentenceAnaphorSetwiseProjectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.DemandResolutionState as Demand
import DASHI.Cognition.PNF.SetBasedDemandPlanning as Planning

------------------------------------------------------------------------
-- E0d: sentence anaphor projection is an open-demand projection.
--
-- Surface spelling is evidence about the occurrence that created the hole; it
-- is not an identity constraint on the eventual witness.  Candidate evidence
-- may be projected set-wise, but projection itself cannot resolve the demand.
------------------------------------------------------------------------

record AnaphorOccurrence
    (OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol : Set) : Set where
  constructor anaphorOccurrence
  field
    occurrenceId : OccurrenceId
    surfaceSymbol : SurfaceSymbol
    roleSymbol : RoleSymbol
    residualSymbol : ResidualSymbol

open AnaphorOccurrence public

record OpenAnaphorProjection
    (OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol : Set) : Set where
  constructor openAnaphorProjection
  field
    sourceOccurrence : OccurrenceId
    surfaceEvidence : SurfaceSymbol
    roleEvidence : RoleSymbol
    residualType : ResidualSymbol
    lexicalIdentityConstraintPresent : Nat
    status : Demand.DemandStatus
    surfaceIsNotIdentity : lexicalIdentityConstraintPresent ≡ zero
    remainsOpen : status ≡ Demand.openDemand

open OpenAnaphorProjection public

projectOpenAnaphor :
  ∀ {OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol : Set} →
  AnaphorOccurrence OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol →
  OpenAnaphorProjection OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol
projectOpenAnaphor occurrence =
  openAnaphorProjection
    (occurrenceId occurrence)
    (surfaceSymbol occurrence)
    (roleSymbol occurrence)
    (residualSymbol occurrence)
    zero
    Demand.openDemand
    refl
    refl

projectionKeepsSurfaceEvidence :
  ∀ {OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol : Set}
    (occurrence : AnaphorOccurrence OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol) →
  surfaceEvidence (projectOpenAnaphor occurrence) ≡ surfaceSymbol occurrence
projectionKeepsSurfaceEvidence occurrence = refl

projectionDoesNotCreateLexicalIdentityConstraint :
  ∀ {OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol : Set}
    (occurrence : AnaphorOccurrence OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol) →
  lexicalIdentityConstraintPresent (projectOpenAnaphor occurrence) ≡ zero
projectionDoesNotCreateLexicalIdentityConstraint occurrence = refl

projectionLeavesDemandOpen :
  ∀ {OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol : Set}
    (occurrence : AnaphorOccurrence OccurrenceId SurfaceSymbol RoleSymbol ResidualSymbol) →
  status (projectOpenAnaphor occurrence) ≡ Demand.openDemand
projectionLeavesDemandOpen occurrence = refl

------------------------------------------------------------------------
-- Set-wise physical realization.
--
-- The existing SetBasedDemandPlanning certificate owns bounded relational
-- candidate planning.  E0d merely requires the anaphor producer to present the
-- same open-demand carrier in set-based rather than one-call-per-row form.
------------------------------------------------------------------------

record SentenceAnaphorSetwiseReceipt : Set where
  constructor sentenceAnaphorSetwiseReceipt
  field
    occurrenceCount : Nat
    projectionStatementCount : Nat
    perOccurrenceProceduralStatementCount : Nat
    recursiveSelfUpdateCount : Nat
    openDemandCount : Nat
    noRequiredPerOccurrenceStatement : perOccurrenceProceduralStatementCount ≡ zero
    noRecursiveSelfUpdate : recursiveSelfUpdateCount ≡ zero
    everyProjectedDemandRemainsOpen : openDemandCount ≡ occurrenceCount

open SentenceAnaphorSetwiseReceipt public

------------------------------------------------------------------------
-- Negative boundaries.
------------------------------------------------------------------------

data SurfaceSpellingIsWitnessIdentity : Set where
data CandidateEvidenceResolvesProjectedAnaphor : Set where
data SetwiseProjectionRequiresRecursiveDemandUpdate : Set where

data ProceduralPerOccurrenceProjectionIsSetBased : Set where

surfaceSpellingIsNotWitnessIdentity : SurfaceSpellingIsWitnessIdentity → ⊥
surfaceSpellingIsNotWitnessIdentity ()

candidateEvidenceCannotResolveProjection :
  CandidateEvidenceResolvesProjectedAnaphor → ⊥
candidateEvidenceCannotResolveProjection ()

setwiseProjectionNeedsNoRecursiveDemandRewrite :
  SetwiseProjectionRequiresRecursiveDemandUpdate → ⊥
setwiseProjectionNeedsNoRecursiveDemandRewrite ()

perOccurrenceProceduralProjectionIsNotSetBased :
  ProceduralPerOccurrenceProjectionIsSetBased → ⊥
perOccurrenceProceduralProjectionIsNotSetBased ()
