{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayExhaustiveResidualClassificationRound507Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayExhaustiveResidualClassificationRound507Exact as R507
import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
open import DASHI.Physics.YangMills.CompactLieProofLevel

inheritsSixtyEightLeafBoard :
  R507.allResidualLeafCount ≡ 68
inheritsSixtyEightLeafBoard = refl

constructorChoiceEqualityStillPruned :
  R507.constructorChoiceEqualityIsAResidualKind ≡ false
constructorChoiceEqualityStillPruned = refl

sourceNameDoesNotAutoDischargeEndpoint :
  R507.opaqueEndpointPredicateMayBeDischargedBySimilarlyNamedSourceTheorem ≡ false
sourceNameDoesNotAutoDischargeEndpoint = refl

classificationCompilerMachineChecked :
  R507.round507ExhaustiveClassificationCompilerLevel ≡ machineChecked
classificationCompilerMachineChecked = refl

continuityAtEmptyIsSourceAnalysis :
  R507.kind R496.a3ContinuityAtEmpty ≡ R507.sourceAnalysis
continuityAtEmptyIsSourceAnalysis = refl

finiteWilsonRPIsAttachment :
  R507.kind R496.aFiniteWilsonRPSameObjectAttachment ≡ R507.sourceLiteralAttachment
finiteWilsonRPIsAttachment = refl

massGapMeaningIsEndpointSemantics :
  R507.kind R496.bStrictPositiveMassGapSemantics ≡ R507.endpointSemantics
massGapMeaningIsEndpointSemantics = refl
