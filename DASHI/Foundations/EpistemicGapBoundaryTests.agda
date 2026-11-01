module DASHI.Foundations.EpistemicGapBoundaryTests where

open import DASHI.Core.Prelude
open import DASHI.Foundations.EpistemicGapBoundary

data OriginQuestion : Set where
  originOfLife : OriginQuestion

data NaturalMechanism : Set where
  chemicalGradient : NaturalMechanism
  autocatalyticNetwork : NaturalMechanism

observedChemistryClaim : WarrantedClaim OriginQuestion NaturalMechanism
observedChemistryClaim = promoteObserved originOfLife chemicalGradient

derivedNetworkClaim : WarrantedClaim OriginQuestion NaturalMechanism
derivedNetworkClaim = promoteDerived originOfLife autocatalyticNetwork

data SpiritualMeaning : Set where
  kinshipWithLife : SpiritualMeaning
  immanentNature : SpiritualMeaning

relationalInterpretation : InterpretiveFrame OriginQuestion SpiritualMeaning
relationalInterpretation = record
  { phenomenon = originOfLife
  ; meaning = kinshipWithLife
  ; mode = relational
  }

spinozistInterpretation : InterpretiveFrame OriginQuestion SpiritualMeaning
spinozistInterpretation = record
  { phenomenon = originOfLife
  ; meaning = immanentNature
  ; mode = spiritual
  }

unknownOriginClaim : ExplanatoryClaim OriginQuestion NaturalMechanism
unknownOriginClaim = record
  { phenomenon = originOfLife
  ; explanation = autocatalyticNetwork
  ; evidence = unknown
  }

unknownOriginCannotBeWarranted :
  Grounded (ExplanatoryClaim.evidence unknownOriginClaim) → ⊥
unknownOriginCannotBeWarranted = unknownIsNotGrounded

originResearchObligation : ResearchObligation OriginQuestion
originResearchObligation =
  unknownGeneratesObligation originOfLife
    (unknown {A = NaturalMechanism})

originQuestionRemainsOpen :
  ResearchObligation.openQuestion originResearchObligation
originQuestionRemainsOpen = tt
