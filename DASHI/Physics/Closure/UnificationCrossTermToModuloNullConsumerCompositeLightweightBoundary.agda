module DASHI.Physics.Closure.UnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.UnificationCrossTermChildCompositeLightweightBoundary
  as Child
import DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary
  as Theorem
import DASHI.Physics.Closure.UnificationNullTransportModuloNullConsumerLightweightBoundary
  as Consumer
import DASHI.Physics.Closure.UnificationModuloNullLinearityFromCrossTermNullityBoundary
  as ModuloNull

record UnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary : Setω where
  field
    theoremBoundaryReferenceRecorded :
      Bool
    theoremBoundaryReferenceRecordedIsTrue :
      theoremBoundaryReferenceRecorded ≡ true
    theoremWallGrammarText :
      String
    theoremWallGrammarTextIsCanonical :
      theoremWallGrammarText
      ≡ Theorem.candidateTheoremGrammarText
          Theorem.canonicalUnificationCrossTermNullityTheoremBoundary
    downstreamConsumerChainText :
      String
    downstreamConsumerChainTextIsCanonical :
      downstreamConsumerChainText
      ≡ Theorem.downstreamConsumerChainText
          Theorem.canonicalUnificationCrossTermNullityTheoremBoundary
    exactUCTGrammarBoundaryRecorded :
      Theorem.theoremClauseCount
        (Theorem.exactGrammarBoundary
          Theorem.canonicalUnificationCrossTermNullityTheoremBoundary)
      ≡ 8
    childComposite :
      Child.UnificationCrossTermChildCompositeLightweightBoundary
    childCompositeIsCanonical :
      childComposite ≡ Child.canonicalUnificationCrossTermChildCompositeLightweightBoundary
    consumerBoundary :
      Consumer.UnificationNullTransportModuloNullConsumerLightweightBoundary
    consumerBoundaryIsCanonical :
      consumerBoundary
        ≡ Consumer.canonicalUnificationNullTransportModuloNullConsumerLightweightBoundary
    moduloNullRouteReferenceRecorded :
      Bool
    moduloNullRouteReferenceRecordedIsTrue :
      moduloNullRouteReferenceRecorded ≡ true
    uct1ResidualPDESpecificationStillUnspecified :
      Theorem.residualPDEHypothesesSpecified
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ false
    uct2EllipticityOrParabolicityClassStillUnspecified :
      Theorem.ellipticityOrParabolicityClassSpecified
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ false
    uct3CarlemanHypothesesStillUnspecified :
      Theorem.carlemanHypothesesSpecified
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ false
    uct4TheoremTargetRecorded :
      Theorem.actualTheoremTargetRecorded
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ true
    analyticIntakeContractRecorded :
      Theorem.analyticIntakeRecorded
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ true
    moduloNullConsumerHandoffRecorded :
      Theorem.moduloNullLinearityConsumerRecorded
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ true
    uct5ModuloNullConsumerRecorded :
      Theorem.moduloNullLinearityConsumerRecorded
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ true
    uct6FourPointConsumerRecorded :
      Theorem.fourPointConsumerRecorded
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ true
    uct7ParallelogramConsumerRecorded :
      Theorem.parallelogramConsumerRecorded
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ true
    uct8JordanVonNeumannAdapterConsumerRecorded :
      Theorem.jordanVonNeumannAdapterConsumerRecorded
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ true
    uctIntakeStillUnimported :
      Theorem.analyticIntakeImported
        Theorem.canonicalUnificationCrossTermNullityTheoremBoundary ≡ false
    childStillFalse :
      Child.UnificationCrossTermChildCompositeLightweightBoundary.crossTermStillFalse
        Child.canonicalUnificationCrossTermChildCompositeLightweightBoundary ≡ refl
    consumerStillFalse :
      Consumer.NullTransportModuloNullConsumerProvedLightweight ≡ false
    terminalStillFalse :
      ModuloNull.terminalUnificationPromotion
        ModuloNull.canonicalUnificationModuloNullLinearityFromCrossTermNullityBoundary ≡ false

canonicalUnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary :
  UnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary
canonicalUnificationCrossTermToModuloNullConsumerCompositeLightweightBoundary =
  record
    { theoremBoundaryReferenceRecorded = true
    ; theoremBoundaryReferenceRecordedIsTrue = refl
    ; theoremWallGrammarText =
        Theorem.candidateTheoremGrammarText
          Theorem.canonicalUnificationCrossTermNullityTheoremBoundary
    ; theoremWallGrammarTextIsCanonical =
        refl
    ; downstreamConsumerChainText =
        Theorem.downstreamConsumerChainText
          Theorem.canonicalUnificationCrossTermNullityTheoremBoundary
    ; downstreamConsumerChainTextIsCanonical =
        refl
    ; exactUCTGrammarBoundaryRecorded =
        Theorem.theoremClauseCountIs8
          (Theorem.exactGrammarBoundary
            Theorem.canonicalUnificationCrossTermNullityTheoremBoundary)
    ; childComposite =
        Child.canonicalUnificationCrossTermChildCompositeLightweightBoundary
    ; childCompositeIsCanonical = refl
    ; consumerBoundary =
        Consumer.canonicalUnificationNullTransportModuloNullConsumerLightweightBoundary
    ; consumerBoundaryIsCanonical = refl
    ; moduloNullRouteReferenceRecorded = true
    ; moduloNullRouteReferenceRecordedIsTrue = refl
    ; uct1ResidualPDESpecificationStillUnspecified =
        Theorem.canonicalCrossTermNullityResidualPDEHypothesesStillUnspecified
    ; uct2EllipticityOrParabolicityClassStillUnspecified =
        Theorem.canonicalCrossTermNullityEllipticityOrParabolicityClassStillUnspecified
    ; uct3CarlemanHypothesesStillUnspecified =
        Theorem.canonicalCrossTermNullityCarlemanHypothesesStillUnspecified
    ; uct4TheoremTargetRecorded =
        Theorem.canonicalCrossTermNullityActualTargetRecorded
    ; analyticIntakeContractRecorded =
        Theorem.canonicalCrossTermNullityAnalyticIntakeRecorded
    ; moduloNullConsumerHandoffRecorded =
        Theorem.canonicalCrossTermNullityModuloNullLinearityConsumerRecorded
    ; uct5ModuloNullConsumerRecorded =
        Theorem.canonicalCrossTermNullityModuloNullLinearityConsumerRecorded
    ; uct6FourPointConsumerRecorded =
        Theorem.canonicalCrossTermNullityFourPointConsumerRecorded
    ; uct7ParallelogramConsumerRecorded =
        Theorem.canonicalCrossTermNullityParallelogramConsumerRecorded
    ; uct8JordanVonNeumannAdapterConsumerRecorded =
        Theorem.canonicalCrossTermNullityJordanVonNeumannAdapterConsumerRecorded
    ; uctIntakeStillUnimported =
        Theorem.canonicalCrossTermNullityAnalyticIntakeStillUnimported
    ; childStillFalse = refl
    ; consumerStillFalse = refl
    ; terminalStillFalse = refl
    }
