module DASHI.Reasoning.LacanPNFBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan
import DASHI.Reasoning.SFMVerifiedClaimPresentation as SFM

------------------------------------------------------------------------
-- PNF as a candidate Symbolic carrier.
------------------------------------------------------------------------

record SymbolicPNFLink : Set₁ where
  field
    source target : PNF.EventPNF
    signifierLink : Lacan.SignifierLink
    sourceMatches :
      Lacan.SignifierLink.source signifierLink ≡ source
    targetMatches :
      Lacan.SignifierLink.target signifierLink ≡ target
    symbolicProjectionReceipt : String

record ResidualCauseProjection : Set where
  field
    residual : Residual.ResidualLevel
    cause : Lacan.CandidateObjetA
    causeSourceMatches :
      Lacan.CandidateObjetA.sourceResidual cause ≡ residual
    projectionIsIdentity : Bool
    interpretationStatus : SFM.InterpretationStatus
    projectionReceipt : String

record PNFRealCandidateBridge : Set where
  field
    comparison : PNF.ComparisonResult
    recurrentFailureReceipt : String
    failedSymbolisationReceipt : String
    realInterpretationCandidate : Bool
    realInterpretationPromoted : Bool
    comparisonDefinitionallyIsReal : Bool

record LacanPNFBridgeBoundary : Set where
  field
    pnfSymbolicCarrierAvailable : Bool
    noMeetMaySeedRealCandidate : Bool
    noMeetDefinitionallyReal : Bool
    residualMaySeedCauseProjection : Bool
    residualDefinitionallyObjetA : Bool
    SFMStatusRequired : Bool
    projectionDiagnosesSubject : Bool
    boundaryNote : String

canonicalLacanPNFBridgeBoundary : LacanPNFBridgeBoundary
canonicalLacanPNFBridgeBoundary = record
  { pnfSymbolicCarrierAvailable = true
  ; noMeetMaySeedRealCandidate = true
  ; noMeetDefinitionallyReal = false
  ; residualMaySeedCauseProjection = true
  ; residualDefinitionallyObjetA = false
  ; SFMStatusRequired = true
  ; projectionDiagnosesSubject = false
  ; boundaryNote =
      "PNF supports signifier relations and governed cause/Real projections; no residual code is definitionally a Lacanian register or object."
  }
