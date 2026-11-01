module DASHI.Physics.Probes.AllProbes where

open import Agda.Primitive using (Setω)

import DASHI.Physics.Probes.NSPromotionProbe as NS
import DASHI.Physics.Probes.YMPromotionProbe as YM
import DASHI.Physics.Probes.UnificationPromotionProbe as Unification
import DASHI.Physics.Probes.CurrentProofProfilePromotionProbe as CurrentProofProfile

record ProbeSurfaceContracts : Setω where
  field
    nsCutset :
      NS.NSPromotionProbeCutsetReceipt

    ymCutset :
      YM.YMPromotionProbeCutsetReceipt

    unificationCutset :
      Unification.UnificationPromotionProbeCutsetReceipt

    currentProofProfileCutset :
      CurrentProofProfile.CurrentProofProfilePromotionProbeCutsetReceipt

canonicalProbeSurfaceContracts :
  ProbeSurfaceContracts
canonicalProbeSurfaceContracts =
  record
    { nsCutset =
        NS.canonicalNSPromotionProbeCutsetReceipt
    ; ymCutset =
        YM.canonicalYMPromotionProbeCutsetReceipt
    ; unificationCutset =
        Unification.canonicalUnificationPromotionProbeCutsetReceipt
    ; currentProofProfileCutset =
        CurrentProofProfile.canonicalCurrentProofProfilePromotionProbeCutsetReceipt
    }
