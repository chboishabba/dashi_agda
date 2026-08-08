module DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound24 where

------------------------------------------------------------------------
-- Normalized current paper-facing Navier-Stokes interface.
--
-- The existing theorem interface owns the A6--A9 and Round 23 Clay-contract
-- spine.  Round 24 adds the broad claimed-paper corpus, exact no-go packages
-- and L0--L23 highest-alpha ladder.  This module assembles those two surfaces
-- without changing any mathematical status and without promoting the terminal
-- theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterface as Base
import DASHI.Papers.NavierStokes.ClayContractRound23 as Clay23
import DASHI.Papers.NavierStokes.ClaimCorpusHighestAlphaRound24 as Round24
import DASHI.Physics.Closure.NSTriadKNLuoClaimedSolutionCorpusRound24Exact as Corpus

record CurrentNSPaperTheoremInterfaceRound24 : Setω where
  field
    baseInterface : Base.NSPaperTheoremStatus
    baseInterfaceIsCanonical :
      baseInterface ≡ Base.canonicalNSPaperTheoremStatus

    claimCorpusStatus :
      Round24.ClaimCorpusHighestAlphaRound24Status
    claimCorpusStatusIsCanonical :
      claimCorpusStatus
      ≡ Round24.canonicalClaimCorpusHighestAlphaRound24Status

    literalClayTargetImplemented :
      Clay23.literalFeffermanPeriodicStatementImplemented
        (Base.clayContractRound23 baseInterface)
      ≡ true

    corpusNotProofAuthority :
      Corpus.allCorpusSourcesAreProofAuthorities ≡ false

    corpusNotDeclaredExhaustive :
      Corpus.corpusSearchIsDeclaredExhaustive ≡ false

    physicalProducersRemainOpen :
      Round24.allPhysicalProducersInhabited claimCorpusStatus ≡ false

    clayPromotionRemainsFalse :
      Base.clayTerminalPromotion baseInterface ≡ false

open CurrentNSPaperTheoremInterfaceRound24 public

canonicalCurrentNSPaperTheoremInterfaceRound24 :
  CurrentNSPaperTheoremInterfaceRound24
canonicalCurrentNSPaperTheoremInterfaceRound24 = record
  { baseInterface = Base.canonicalNSPaperTheoremStatus
  ; baseInterfaceIsCanonical = refl
  ; claimCorpusStatus =
      Round24.canonicalClaimCorpusHighestAlphaRound24Status
  ; claimCorpusStatusIsCanonical = refl
  ; literalClayTargetImplemented =
      Base.nsPaperLiteralClayTargetImplemented
  ; corpusNotProofAuthority =
      Round24.claimCorpusIsNotProofAuthority
  ; corpusNotDeclaredExhaustive =
      Round24.claimCorpusSearchNotDeclaredExhaustive
  ; physicalProducersRemainOpen =
      Round24.physicalProducersRemainOpen
  ; clayPromotionRemainsFalse =
      Base.nsPaperInterfaceTerminalFalse
  }

currentLiteralTargetImplemented :
  Clay23.literalFeffermanPeriodicStatementImplemented
    (Base.clayContractRound23
      (baseInterface canonicalCurrentNSPaperTheoremInterfaceRound24))
  ≡ true
currentLiteralTargetImplemented =
  Base.nsPaperLiteralClayTargetImplemented

currentPhysicalProducersOpen :
  Round24.allPhysicalProducersInhabited
    (claimCorpusStatus canonicalCurrentNSPaperTheoremInterfaceRound24)
  ≡ false
currentPhysicalProducersOpen =
  Round24.physicalProducersRemainOpen

currentClayPromotionFalse :
  Base.clayTerminalPromotion
    (baseInterface canonicalCurrentNSPaperTheoremInterfaceRound24)
  ≡ false
currentClayPromotionFalse =
  Base.nsPaperInterfaceTerminalFalse
