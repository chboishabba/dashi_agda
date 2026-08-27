module DASHI.Governance.RecognitionDistributionRepresentationAxesExact where

------------------------------------------------------------------------
-- REDISTRIBUTION / RECOGNITION / REPRESENTATION AXES
--
-- SOURCE CALIBRATION
-- Nancy Fraser, "Social Justice in the Age of Identity Politics:
-- Redistribution, Recognition, and Participation", in Redistribution or
-- Recognition? A Political-Philosophical Exchange, Verso, 2003.
-- ISBN 9781859844922. No DOI asserted for the book chapter here.
-- Nancy Fraser, Scales of Justice: Reimagining Political Space in a
-- Globalizing World, Columbia University Press, 2009.
-- ISBN 9780231146807. No DOI asserted for the book.
--
-- Fraser motivates the separability of redistribution, recognition and
-- representation. The finite non-factorability witnesses are DASHI mathematics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

data ParticipationState : Set where
  highRecognitionLowDistribution
  highRecognitionHighDistribution
  highDistributionLowRepresentation
  highDistributionHighRepresentation
  : ParticipationState

data Distribution : Set where lowDistribution highDistribution : Distribution
data Recognition : Set where lowRecognition highRecognition : Recognition
data Representation : Set where lowRepresentation highRepresentation : Representation

distribution : ParticipationState → Distribution
distribution highRecognitionLowDistribution = lowDistribution
distribution highRecognitionHighDistribution = highDistribution
distribution highDistributionLowRepresentation = highDistribution
distribution highDistributionHighRepresentation = highDistribution

recognition : ParticipationState → Recognition
recognition highRecognitionLowDistribution = highRecognition
recognition highRecognitionHighDistribution = highRecognition
recognition highDistributionLowRepresentation = lowRecognition
recognition highDistributionHighRepresentation = highRecognition

representation : ParticipationState → Representation
representation highRecognitionLowDistribution = lowRepresentation
representation highRecognitionHighDistribution = highRepresentation
representation highDistributionLowRepresentation = lowRepresentation
representation highDistributionHighRepresentation = highRepresentation

recognitionCannotRecoverDistribution :
  INF.FactorsThrough recognition distribution → ⊥
recognitionCannotRecoverDistribution =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      highRecognitionLowDistribution
      highRecognitionHighDistribution
      refl
      (λ ()))

distributionCannotRecoverRepresentation :
  INF.FactorsThrough distribution representation → ⊥
distributionCannotRecoverRepresentation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      highDistributionLowRepresentation
      highDistributionHighRepresentation
      refl
      (λ ()))

record ParticipationAxesBoundary : Set where
  constructor participation-axes-boundary
  field
    recognitionEqualsDistribution : Bool
    recognitionEqualsDistributionIsFalse : recognitionEqualsDistribution ≡ false
    distributionEqualsRepresentation : Bool
    distributionEqualsRepresentationIsFalse : distributionEqualsRepresentation ≡ false
    anySingleAxisDefinesJustice : Bool
    anySingleAxisDefinesJusticeIsFalse : anySingleAxisDefinesJustice ≡ false
    threeAxesDefinitionallySumToJustice : Bool
    threeAxesDefinitionallySumToJusticeIsFalse :
      threeAxesDefinitionallySumToJustice ≡ false

canonicalParticipationAxesBoundary : ParticipationAxesBoundary
canonicalParticipationAxesBoundary =
  participation-axes-boundary false refl false refl false refl false refl
