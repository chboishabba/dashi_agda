module DASHI.Physics.YangMills.BalabanClayGate4Attachment254CompletionReceipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4Attachment254CompletionLedger as Ledger

record Attachment254CompletionReceipt : Set where
  constructor attachment254CompletionReceipt
  field
    repositoryHead : String
    sourceAuditChecked : Bool
    su2PrincipalLogChecked : Bool
    endpointPredicateChecked : Bool
    selfAdjointFormNormChecked : Bool
    finiteRayleighSpectrumChecked : Bool
    summableSlackChecked : Bool
    ipsenRehmanPrimaryChecked : Bool
    betaConventionAuditChecked : Bool
    couplingInductionChecked : Bool
    tranchePostulateFree : Bool

open Attachment254CompletionReceipt public

record AuthoritativeAttachment254Evidence
    (receipt : Attachment254CompletionReceipt) : Set₁ where
  field
    sourceAuditTypechecks : Set
    su2PrincipalLogTypechecks : Set
    endpointPredicateTypechecks : Set
    selfAdjointFormNormTypechecks : Set
    finiteRayleighSpectrumTypechecks : Set
    summableSlackTypechecks : Set
    ipsenRehmanPrimaryTypechecks : Set
    betaConventionAuditTypechecks : Set
    couplingInductionTypechecks : Set
    trancheHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativeAttachment254Evidence public

attachment254SourceAuditTypecheckLevel : ProofLevel
attachment254SourceAuditTypecheckLevel = conditional

attachment254SU2PrincipalLogTypecheckLevel : ProofLevel
attachment254SU2PrincipalLogTypecheckLevel = conditional

attachment254EndpointPredicateTypecheckLevel : ProofLevel
attachment254EndpointPredicateTypecheckLevel = conditional

attachment254SelfAdjointFormNormTypecheckLevel : ProofLevel
attachment254SelfAdjointFormNormTypecheckLevel = conditional

attachment254FiniteRayleighSpectrumTypecheckLevel : ProofLevel
attachment254FiniteRayleighSpectrumTypecheckLevel = conditional

attachment254SummableSlackTypecheckLevel : ProofLevel
attachment254SummableSlackTypecheckLevel = conditional

attachment254IpsenRehmanPrimaryTypecheckLevel : ProofLevel
attachment254IpsenRehmanPrimaryTypecheckLevel = conditional

attachment254BetaConventionAuditTypecheckLevel : ProofLevel
attachment254BetaConventionAuditTypecheckLevel = conditional

attachment254CouplingInductionTypecheckLevel : ProofLevel
attachment254CouplingInductionTypecheckLevel = conditional

attachment254PostulateFreeLevel : ProofLevel
attachment254PostulateFreeLevel = conditional
