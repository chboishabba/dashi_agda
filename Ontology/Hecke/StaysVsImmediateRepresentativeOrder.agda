module Ontology.Hecke.StaysVsImmediateRepresentativeOrder where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)

open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( CertifiedExitToAnchoredClass
    ; CertifiedStayClass
    ; certifiedBalancedComposed
    ; certifiedBalancedCycle
    ; certifiedDenseComposed
    ; certifiedExplicitWidth1
    ; certifiedExplicitWidth3
    )
open import Ontology.Hecke.DefectOrbitPressureOrder as DOPO
  using
    ( AnchoredVsImmediateOrbitOrderOK
    ; ImmediateExitOrbitPressureOK
    ; StayVsImmediateOrbitOrderOK
    )
open import Ontology.Hecke.ExitToAnchoredRepresentativeComputations as ETRC
  using
    ( exitToAnchoredCollapseClass
    ; exitToAnchoredForcedStableOrbitP2-balancedComposed
    ; exitToAnchoredForcedStableOrbitP2-balancedCycle
    ; exitToAnchoredRepresentativeForcedStableCountOrbitP2
    ; exitToAnchoredRepresentativeIllegalCountP2
    )
open import Ontology.Hecke.ImmediateExitRepresentativeComputations as IERC
  using
    ( CertifiedImmediateExitClass
    ; exitAnchoredTrajectory
    ; exitExplicitWidth2
    ; exitFullSupportCascade
    ; immediateExitCollapseClass
    ; immediateExitForcedStableOrbitP2-anchoredTrajectory
    ; immediateExitForcedStableOrbitP2-explicitWidth2
    ; immediateExitForcedStableOrbitP2-fullSupportCascade
    ; immediateExitIllegalCountP2-anchoredTrajectory
    ; immediateExitIllegalCountP2-explicitWidth2
    ; immediateExitIllegalCountP2-fullSupportCascade
    ; immediateExitRepresentativeForcedStableCountOrbitP2
    ; immediateExitRepresentativeIllegalCountP2
    )
open import Ontology.Hecke.StaysOneMoreStepRepresentativeComputations as SSRC
  using
    ( stayCollapseClass
    ; stayForcedStableOrbitP2-denseComposed
    ; stayForcedStableOrbitP2-explicitWidth1
    ; stayForcedStableOrbitP2-explicitWidth3
    ; stayRepresentativeForcedStableCountOrbitP2
    )

------------------------------------------------------------------------
-- Concrete representative-order witnesses on the current certified set.
--
-- This module is intentionally small.  It discharges the current guarded
-- pressure-order predicates directly from the exact `p2` count theorems,
-- without introducing another normalization-heavy summary surface.

2≤15 : 2 ≤ 15
2≤15 = s≤s (s≤s z≤n)

stayRepresentative≤immediateRepresentativeOrbitP2 :
  ∀ cs ce →
  stayRepresentativeForcedStableCountOrbitP2 cs
    ≤
  immediateExitRepresentativeForcedStableCountOrbitP2 ce
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedExplicitWidth1 IERC.exitExplicitWidth2
  rewrite stayForcedStableOrbitP2-explicitWidth1
        | immediateExitForcedStableOrbitP2-explicitWidth2
  = 2≤15
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedExplicitWidth1 IERC.exitAnchoredTrajectory
  rewrite stayForcedStableOrbitP2-explicitWidth1
        | immediateExitForcedStableOrbitP2-anchoredTrajectory
  = 2≤15
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedExplicitWidth1 IERC.exitFullSupportCascade
  rewrite stayForcedStableOrbitP2-explicitWidth1
        | immediateExitForcedStableOrbitP2-fullSupportCascade
  = 2≤15
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedExplicitWidth3 IERC.exitExplicitWidth2
  rewrite stayForcedStableOrbitP2-explicitWidth3
        | immediateExitForcedStableOrbitP2-explicitWidth2
  = ≤-refl
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedExplicitWidth3 IERC.exitAnchoredTrajectory
  rewrite stayForcedStableOrbitP2-explicitWidth3
        | immediateExitForcedStableOrbitP2-anchoredTrajectory
  = ≤-refl
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedExplicitWidth3 IERC.exitFullSupportCascade
  rewrite stayForcedStableOrbitP2-explicitWidth3
        | immediateExitForcedStableOrbitP2-fullSupportCascade
  = ≤-refl
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedDenseComposed IERC.exitExplicitWidth2
  rewrite stayForcedStableOrbitP2-denseComposed
        | immediateExitForcedStableOrbitP2-explicitWidth2
  = ≤-refl
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedDenseComposed IERC.exitAnchoredTrajectory
  rewrite stayForcedStableOrbitP2-denseComposed
        | immediateExitForcedStableOrbitP2-anchoredTrajectory
  = ≤-refl
stayRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedDenseComposed IERC.exitFullSupportCascade
  rewrite stayForcedStableOrbitP2-denseComposed
        | immediateExitForcedStableOrbitP2-fullSupportCascade
  = ≤-refl

anchoredRepresentative≤immediateRepresentativeOrbitP2 :
  ∀ ca ce →
  exitToAnchoredRepresentativeForcedStableCountOrbitP2 ca
    ≤
  immediateExitRepresentativeForcedStableCountOrbitP2 ce
anchoredRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedBalancedCycle IERC.exitExplicitWidth2
  rewrite exitToAnchoredForcedStableOrbitP2-balancedCycle
        | immediateExitForcedStableOrbitP2-explicitWidth2
  = ≤-refl
anchoredRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedBalancedCycle IERC.exitAnchoredTrajectory
  rewrite exitToAnchoredForcedStableOrbitP2-balancedCycle
        | immediateExitForcedStableOrbitP2-anchoredTrajectory
  = ≤-refl
anchoredRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedBalancedCycle IERC.exitFullSupportCascade
  rewrite exitToAnchoredForcedStableOrbitP2-balancedCycle
        | immediateExitForcedStableOrbitP2-fullSupportCascade
  = ≤-refl
anchoredRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedBalancedComposed IERC.exitExplicitWidth2
  rewrite exitToAnchoredForcedStableOrbitP2-balancedComposed
        | immediateExitForcedStableOrbitP2-explicitWidth2
  = ≤-refl
anchoredRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedBalancedComposed IERC.exitAnchoredTrajectory
  rewrite exitToAnchoredForcedStableOrbitP2-balancedComposed
        | immediateExitForcedStableOrbitP2-anchoredTrajectory
  = ≤-refl
anchoredRepresentative≤immediateRepresentativeOrbitP2
  GT.certifiedBalancedComposed IERC.exitFullSupportCascade
  rewrite exitToAnchoredForcedStableOrbitP2-balancedComposed
        | immediateExitForcedStableOrbitP2-fullSupportCascade
  = ≤-refl

immediateExitOrbitPressureOK-certified :
  ∀ ce →
  ImmediateExitOrbitPressureOK (immediateExitCollapseClass ce)
immediateExitOrbitPressureOK-certified IERC.exitExplicitWidth2
  rewrite immediateExitIllegalCountP2-explicitWidth2
  = s≤s z≤n
immediateExitOrbitPressureOK-certified IERC.exitAnchoredTrajectory
  rewrite immediateExitIllegalCountP2-anchoredTrajectory
  = s≤s z≤n
immediateExitOrbitPressureOK-certified IERC.exitFullSupportCascade
  rewrite immediateExitIllegalCountP2-fullSupportCascade
  = s≤s z≤n

stayVsImmediateOrbitOrderOK-certified :
  ∀ cs ce →
  StayVsImmediateOrbitOrderOK
    (stayCollapseClass cs)
    (immediateExitCollapseClass ce)
stayVsImmediateOrbitOrderOK-certified =
  stayRepresentative≤immediateRepresentativeOrbitP2

anchoredVsImmediateOrbitOrderOK-certified :
  ∀ ca ce →
  AnchoredVsImmediateOrbitOrderOK
    (exitToAnchoredCollapseClass ca)
    (immediateExitCollapseClass ce)
anchoredVsImmediateOrbitOrderOK-certified =
  anchoredRepresentative≤immediateRepresentativeOrbitP2
