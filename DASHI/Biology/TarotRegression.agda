module DASHI.Biology.TarotRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.TarotInterpretationPNFExact as PNF
import DASHI.Biology.TarotSemanticKernelExact as Semantic
import DASHI.Biology.TarotSpreadHyperfabricExact as Spread
import DASHI.Cognition.PNF.EventAlgebra as EventPNF
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Aggregate exact regressions for the tarot tranche.
------------------------------------------------------------------------

deckRegression :
  Tarot.listCount Tarot.allCards ≡ 78
deckRegression = Tarot.riderWaiteSmithDeckCountIsSeventyEight

majorAndMinorDecompositionRegression :
  Tarot.listCount Tarot.allMajorArcana ≡ 22
  ×
  Tarot.listCount (Tarot.cardsOfSuit Tarot.wands) ≡ 14
  ×
  Tarot.listCount (Tarot.cardsOfSuit Tarot.cups) ≡ 14
  ×
  Tarot.listCount (Tarot.cardsOfSuit Tarot.swords) ≡ 14
  ×
  Tarot.listCount (Tarot.cardsOfSuit Tarot.pentacles) ≡ 14
majorAndMinorDecompositionRegression =
  refl , refl , refl , refl , refl

canonicalSpreadHasThreeDistinctDraws :
  Tarot.listCount
    (Spread.layoutDraws Spread.canonicalThreeCardLayout)
  ≡ 3
canonicalSpreadHasThreeDistinctDraws = refl

deathIsTransformationNotLiteralDeathRegression :
  Semantic.centralMeaning
    (Semantic.meaning (Tarot.major Tarot.death))
  ≡ "Ending, irreversible transformation, clearing away"
deathIsTransformationNotLiteralDeathRegression = refl

reversalIsNotBooleanNegationRegression :
  Semantic.possibleReversalLenses
    (Semantic.meaningFor
      (Tarot.cardToken
        (Tarot.major Tarot.theTower)
        Tarot.reversedOrientation
        Tarot.riderWaiteSmith
        []))
  ≡ Semantic.blocked
    ∷ Semantic.internalised
    ∷ Semantic.excessive
    ∷ Semantic.deficient
    ∷ Semantic.distorted
    ∷ Semantic.releasing
    ∷ []
reversalIsNotBooleanNegationRegression = refl

residualSurvivesNormalisationRegression :
  PNF.unresolvedResiduals PNF.canonicalInterpretationNF
  ≡ Residual.partial ∷ []
residualSurvivesNormalisationRegression = refl

residualMapsThroughExistingPNFAlgebra :
  PNF.interpretationResidualClass PNF.canonicalInterpretationNF
  ≡ EventPNF.residuallyDifferent
residualMapsThroughExistingPNFAlgebra = refl

authorityRegression :
  PNF.historicalGameOriginSupported PNF.canonicalTarotAuthorityFlags ≡ true
  ×
  PNF.ancientEgyptianOriginSupported PNF.canonicalTarotAuthorityFlags ≡ false
  ×
  PNF.futureCausationProved PNF.canonicalTarotAuthorityFlags ≡ false
  ×
  PNF.clinicalDiagnosisAuthorised PNF.canonicalTarotAuthorityFlags ≡ false
  ×
  PNF.reflectiveInterpretationAvailable PNF.canonicalTarotAuthorityFlags ≡ true
authorityRegression = refl , refl , refl , refl , refl

associativeCompilationRegression :
  PNF.compileTarotPNF PNF.canonicalReflectiveTrace
  ≡
  PNF.compileTarotPNF PNF.canonicalReflectiveTrace
associativeCompilationRegression = refl
