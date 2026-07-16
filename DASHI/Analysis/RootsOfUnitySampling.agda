module DASHI.Analysis.RootsOfUnitySampling where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MaassFourierCarrier as MFC

------------------------------------------------------------------------
-- This is only the finite sampling square.  It deliberately says nothing
-- about global automorphy or existence of a nearby Maaß eigenfunction.

record AliasFreeGrid (Γ : MFC.ΓMaass) : Set where
  field
    aliasFreeReading : String

record ExactTruncatedRecovery (Γ : MFC.ΓMaass)
  (state : MFC.TruncatedFourierState Γ) : Set where
  field
    grid             : AliasFreeGrid Γ
    recovered        : MFC.RecoveredCoefficientVector Γ
    recoveryIsDFT    : recovered ≡ MFC.rootsOfUnityRecover (MFC.horocycleSample state)
    exactnessReading : String

