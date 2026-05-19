module DASHI.Physics.Closure.CanonicalP2OfflineL2ObstructionCertificate where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Empty using (⊥)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF
open import DASHI.Physics.Closure.CanonicalP2KeyScheduleBridgeObstruction as CPKSO
open import DASHI.Physics.Closure.ShiftContractEigenShadowNormalizedPackage as SENP
open import DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryControlAttempt as SCEC
open import DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryObstruction as SEOSO

------------------------------------------------------------------------
-- Theorem-thin offline L2 obstruction certificate for the missing P2 bridge.
--
-- This is intentionally not a positive `β_p2` construction.  It packages the
-- current normalized eigenShadow obstruction as a discrete L2-style lower
-- bound certificate: the below-δ condition is the already-landed equality of
-- the normalized eigenShadow surface, and any candidate bridge that would turn
-- that condition into `p2` key equality contradicts the existing obstruction.

δ_p2 : Nat
δ_p2 = suc zero

NormalizedShadowBelowδP2 : Set₁
NormalizedShadowBelowδP2 =
  ∀ {q} →
  CCF.CanonicalFibre q →
  CCF.CanonicalFibre q →
  Set

normalizedShadowBelowδ_p2 : NormalizedShadowBelowδP2
normalizedShadowBelowδ_p2 x y =
  SCEC.canonicalNormalizedEigenShadow (CCF.carrier x)
    ≡
  SCEC.canonicalNormalizedEigenShadow (CCF.carrier y)

record OfflineL2P2BridgeCandidate
  (belowδ : NormalizedShadowBelowδP2)
  : Setω where
  field
    belowδ-forces-p2-key :
      ∀ {q} →
      (x y : CCF.CanonicalFibre q) →
      belowδ x y →
      FOS.profileSummaryAt p2 (CCFF.primeField x)
        ≡
      FOS.profileSummaryAt p2 (CCFF.primeField y)

normalizedShadowBelowδ_p2BridgeImpossible :
  OfflineL2P2BridgeCandidate normalizedShadowBelowδ_p2 → ⊥
normalizedShadowBelowδ_p2BridgeImpossible β =
  CPKSO.CanonicalP2KeyScheduleBridgeObstruction.normalizedSurfaceTooWeak
    CPKSO.canonicalP2KeyScheduleBridgeObstruction
    (OfflineL2P2BridgeCandidate.belowδ-forces-p2-key β)

record CanonicalP2OfflineL2ObstructionCertificate : Setω where
  field
    lowerBoundδ_p2 : Nat
    normalizedBelowδCondition : NormalizedShadowBelowδP2
    bridgeObstruction :
      CPKSO.CanonicalP2KeyScheduleBridgeObstruction
    shiftNormalizedPackage :
      SENP.ShiftContractEigenShadowNormalizedPackage
    canonicalShadowOrbitSummaryObstruction :
      SEOSO.ShiftContractEigenShadowOrbitSummaryObstruction

    allBelowδCandidatesImpossible :
      OfflineL2P2BridgeCandidate normalizedBelowδCondition → ⊥

canonicalP2OfflineL2ObstructionCertificate :
  CanonicalP2OfflineL2ObstructionCertificate
canonicalP2OfflineL2ObstructionCertificate =
  record
    { lowerBoundδ_p2 = δ_p2
    ; normalizedBelowδCondition = normalizedShadowBelowδ_p2
    ; bridgeObstruction =
        CPKSO.canonicalP2KeyScheduleBridgeObstruction
    ; shiftNormalizedPackage =
        SENP.canonicalShiftContractEigenShadowNormalizedPackage
    ; canonicalShadowOrbitSummaryObstruction =
        SEOSO.canonicalShiftContractEigenShadowOrbitSummaryObstruction
    ; allBelowδCandidatesImpossible =
        normalizedShadowBelowδ_p2BridgeImpossible
    }
