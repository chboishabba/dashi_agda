module DASHI.Biology.ConsciousAccessRound6CrossPollinationRegression where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.VisualMotifTransitionOperator as Motif
import DASHI.Biology.TernaryVisualMotifSemiconjugacyExact as Semiconjugacy
import DASHI.Biology.TernaryMorphogeneticVisualFieldExact as MorphField
import DASHI.Biology.MorphogeneticVisualGenerator as Morphogenesis
import DASHI.Biology.TernaryMotifNeuralObservationQuotientExact as NeuralQuotient
import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Biology.TriadicVisualBraidCrossPollinationExact as BraidCross
import DASHI.Biology.TriadicBraidDialecticExact as TriadicBraid
import DASHI.Biology.VisualPathBraidResidual as VisualBraid
import DASHI.Biology.TernaryHallTransitionCoalitionExact as HallCross
import DASHI.Biology.ConsciousAccessRound6CrossSourceBridge as Sources

record ConsciousAccessRound6CrossPollinationRegression : Setω where
  field
    motifSemiconjugacy :
      (t : Triadic.KernelTrit) →
      Semiconjugacy.motifOfTrit (Semiconjugacy.ternaryPhaseStep t)
      ≡
      Motif.motifStep Motif.reweightedMotifRegime
        (Semiconjugacy.motifOfTrit t)

    ternaryPeriodThree :
      (t : Triadic.KernelTrit) →
      Semiconjugacy.ternaryPhaseStep
        (Semiconjugacy.ternaryPhaseStep
          (Semiconjugacy.ternaryPhaseStep t))
      ≡
      t

    morphogeneticFieldSection :
      (t : Triadic.KernelTrit) →
      MorphField.phaseOfField (MorphField.fieldOfTrit t) ≡ t

    squareModeProjectsToTunnel :
      MorphField.motifOfField Morphogenesis.squareModeField
      ≡
      Motif.tunnelMotif

    neuralCoarseCollision :
      Neural.fmriLikeObservation
        (NeuralQuotient.activationOfTrit Triadic.negativeTrit)
      ≡
      Neural.fmriLikeObservation
        (NeuralQuotient.activationOfTrit Triadic.zeroTrit)

    neuralVariationStillDiffers :
      Neural.laplacianVariation
        (NeuralQuotient.activationOfTrit Triadic.negativeTrit)
      ≡ 2
      ×
      Neural.laplacianVariation
        (NeuralQuotient.activationOfTrit Triadic.zeroTrit)
      ≡ 3

    braidEndpointsAgree :
      TriadicBraid.endpoint TriadicBraid.leftTransition
      ≡
      TriadicBraid.endpoint TriadicBraid.rightTransition

    braidWordsRemainDifferent :
      TriadicBraid.wordKind
        (TriadicBraid.residual TriadicBraid.leftTransition)
      ≡
      TriadicBraid.wordKind
        (TriadicBraid.residual TriadicBraid.rightTransition)
      →
      ⊥

    visualHistoryResidualIsOne :
      VisualBraid.historyResidual
        VisualBraid.inhibitionThenCompletion
        VisualBraid.completionThenInhibition
        false
      ≡
      1

    integratedTernaryHallObjectiveZero :
      HallCross.jointObjective HallCross.integratedTernaryHallCandidate
      ≡
      0

    sourceBridgeCountIsFour :
      Sources.canonicalRound6CrossSourceCount ≡ 4

open ConsciousAccessRound6CrossPollinationRegression public

canonicalConsciousAccessRound6CrossPollinationRegression :
  ConsciousAccessRound6CrossPollinationRegression
canonicalConsciousAccessRound6CrossPollinationRegression =
  record
    { motifSemiconjugacy = Semiconjugacy.ternaryMotifSemiconjugacy
    ; ternaryPeriodThree = Semiconjugacy.ternaryPhasePeriodThree
    ; morphogeneticFieldSection = MorphField.fieldSection
    ; squareModeProjectsToTunnel = MorphField.squareModeProjectsToTunnel
    ; neuralCoarseCollision = NeuralQuotient.negativeAndZeroShareCoarseObservation
    ; neuralVariationStillDiffers =
        NeuralQuotient.negativeAndZeroHaveDifferentVariation
    ; braidEndpointsAgree = TriadicBraid.braidRelationSharesEndpoint
    ; braidWordsRemainDifferent =
        TriadicBraid.braidRelationRetainsDistinctWordResidual
    ; visualHistoryResidualIsOne =
        VisualBraid.canonicalHistoryResidualIsOne
    ; integratedTernaryHallObjectiveZero =
        HallCross.integratedTernaryHallObjectiveIsZero
    ; sourceBridgeCountIsFour =
        Sources.canonicalRound6CrossSourceCountIsFour
    }
