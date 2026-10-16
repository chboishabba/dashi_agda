{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyGTPSShortTime2026AuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

record GTPSShortTimeStatus : Set where
  field
    SourceGeneralGTPSCarrierSourceWritten : Bool
    SourceGeneralGTPSCarrierSourceWrittenIsTrue :
      SourceGeneralGTPSCarrierSourceWritten ≡ true

    SourceShortTimeSquaredFunctionalSourceWritten : Bool
    SourceShortTimeSquaredFunctionalSourceWrittenIsTrue :
      SourceShortTimeSquaredFunctionalSourceWritten ≡ true

    SourceAlgebraDistanceSquaredFormulaSourceWritten : Bool
    SourceAlgebraDistanceSquaredFormulaSourceWrittenIsTrue :
      SourceAlgebraDistanceSquaredFormulaSourceWritten ≡ true

    FiniteShortTimeMinimizerSourceWritten : Bool
    FiniteShortTimeMinimizerSourceWrittenIsTrue :
      FiniteShortTimeMinimizerSourceWritten ≡ true

    SourceProjectorAutomaticallyAvailable : Bool
    SourceProjectorAutomaticallyAvailableIsFalse :
      SourceProjectorAutomaticallyAvailable ≡ false

    SourceRiemannianPullbackSourceWritten : Bool
    SourceRiemannianPullbackSourceWrittenIsFalse :
      SourceRiemannianPullbackSourceWritten ≡ false

    AlgebraSusceptibilitySourceWritten : Bool
    AlgebraSusceptibilitySourceWrittenIsFalse :
      AlgebraSusceptibilitySourceWritten ≡ false

    ThermodynamicLimitMQPTSourceWritten : Bool
    ThermodynamicLimitMQPTSourceWrittenIsFalse :
      ThermodynamicLimitMQPTSourceWritten ≡ false

canonicalGTPSShortTimeStatus : GTPSShortTimeStatus
canonicalGTPSShortTimeStatus = record
  { SourceGeneralGTPSCarrierSourceWritten = true
  ; SourceGeneralGTPSCarrierSourceWrittenIsTrue = refl
  ; SourceShortTimeSquaredFunctionalSourceWritten = true
  ; SourceShortTimeSquaredFunctionalSourceWrittenIsTrue = refl
  ; SourceAlgebraDistanceSquaredFormulaSourceWritten = true
  ; SourceAlgebraDistanceSquaredFormulaSourceWrittenIsTrue = refl
  ; FiniteShortTimeMinimizerSourceWritten = true
  ; FiniteShortTimeMinimizerSourceWrittenIsTrue = refl
  ; SourceProjectorAutomaticallyAvailable = false
  ; SourceProjectorAutomaticallyAvailableIsFalse = refl
  ; SourceRiemannianPullbackSourceWritten = false
  ; SourceRiemannianPullbackSourceWrittenIsFalse = refl
  ; AlgebraSusceptibilitySourceWritten = false
  ; AlgebraSusceptibilitySourceWrittenIsFalse = refl
  ; ThermodynamicLimitMQPTSourceWritten = false
  ; ThermodynamicLimitMQPTSourceWrittenIsFalse = refl
  }

zanardiDallasAndreadakis2026ExternalClaim : Sources.AttributionReceipt
zanardiDallasAndreadakis2026ExternalClaim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Mereological Quantum Phase Transitions, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w; arXiv:2510.06389"
    "Defines generalized TPSs through operator *-subalgebras and their commutants/direct-sum virtual bipartitions, gives short-time scrambling sigma_s(A,H)=||Q_A(H)||_2 with Q_A=1-P_(A+A'), and algebra distance D(A',A)=d^-1||P_A'-P_A||_HS; further Riemannian pullback, algebra susceptibility and m-QPT claims remain external scientific authority."

leanGTPSShortTimeSourceReceipt : Sources.AttributionReceipt
leanGTPSShortTimeSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: QuantumMereologyGTPSShortTime2026"
    "Source-written Lean reconstruction of a finite source-facing g-TPS carrier with explicit commutant witness, proof-carrying orthogonal-projection interfaces, squared short-time scrambling and squared algebra-distance formulas, plus finite-family minimum existence. No automatic projector producer, susceptibility or m-QPT theorem is imported."

dashiGTPSShortTimeCrossModuleReceipt : Sources.AttributionReceipt
dashiGTPSShortTimeCrossModuleReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records the source/formal split: external literature owns the scientific formulas/interpretation, Lean owns its finite formal reconstruction, and Agda mirrors only the source-written status without claiming kernel proof replay."
