module Ontology.Hecke.CertifiedRepresentativePersistence where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( CollapseTime
    ; GeneratorCollapseClass
    ; collapseTime
    ; immediateExit
    ; exitToAnchored
    ; staysOneMoreStep
    )
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
open import Ontology.Hecke.ExitToAnchoredRepresentativeComputations as ETRC
  using
    ( exitToAnchoredCollapseClass
    ; exitToAnchoredCollapseTime
    ; exitToAnchoredForcedStableOrbitP2-balancedComposed
    ; exitToAnchoredForcedStableOrbitP2-balancedCycle
    ; exitToAnchoredRepresentativeForcedStableCountOrbitP2
    )
open import Ontology.Hecke.ImmediateExitRepresentativeComputations as IERC
  using
    ( CertifiedImmediateExitClass
    ; exitAnchoredTrajectory
    ; exitExplicitWidth2
    ; exitFullSupportCascade
    ; immediateExitCollapseClass
    ; immediateExitCollapseTime
    ; immediateExitForcedStableOrbitP2-anchoredTrajectory
    ; immediateExitForcedStableOrbitP2-explicitWidth2
    ; immediateExitForcedStableOrbitP2-fullSupportCascade
    ; immediateExitRepresentativeForcedStableCountOrbitP2
    )
open import Ontology.Hecke.StaysOneMoreStepRepresentativeComputations as SSRC
  using
    ( stayCollapseClass
    ; stayCollapseTime
    ; stayForcedStableOrbitP2-denseComposed
    ; stayForcedStableOrbitP2-explicitWidth1
    ; stayForcedStableOrbitP2-explicitWidth3
    ; stayRepresentativeForcedStableCountOrbitP2
    )

------------------------------------------------------------------------
-- Exact `p2` persistence layer on the current certified Hecke-side
-- representatives.
--
-- This is intentionally narrower than a full collapse-time quotient theorem.
-- It packages the first genuinely collapse-free numeric factorization that
-- the current exact representative computations support:
-- `forcedStableCountOrbitP2` determines a small persistence tier on the
-- certified representative set.

2≤15 : 2 ≤ 15
2≤15 = s≤s (s≤s z≤n)

1≤15 : suc zero ≤ 15
1≤15 = s≤s z≤n

data CertifiedRepresentativeClass : Set where
  stayRep :
    CertifiedStayClass → CertifiedRepresentativeClass
  anchoredRep :
    CertifiedExitToAnchoredClass → CertifiedRepresentativeClass
  immediateRep :
    CertifiedImmediateExitClass → CertifiedRepresentativeClass

certifiedRepresentativeCollapseClass :
  CertifiedRepresentativeClass → GeneratorCollapseClass
certifiedRepresentativeCollapseClass (stayRep c) =
  stayCollapseClass c
certifiedRepresentativeCollapseClass (anchoredRep c) =
  exitToAnchoredCollapseClass c
certifiedRepresentativeCollapseClass (immediateRep c) =
  immediateExitCollapseClass c

certifiedRepresentativeCollapseTime :
  (c : CertifiedRepresentativeClass) →
  CollapseTime
certifiedRepresentativeCollapseTime c =
  collapseTime (certifiedRepresentativeCollapseClass c)

forcedStableOrbitP2At : CertifiedRepresentativeClass → Nat
forcedStableOrbitP2At (stayRep c) =
  stayRepresentativeForcedStableCountOrbitP2 c
forcedStableOrbitP2At (anchoredRep c) =
  exitToAnchoredRepresentativeForcedStableCountOrbitP2 c
forcedStableOrbitP2At (immediateRep c) =
  immediateExitRepresentativeForcedStableCountOrbitP2 c

data P2OrbitCountBand : Nat → Set where
  reduced2 : P2OrbitCountBand 2
  saturated15 : P2OrbitCountBand 15

orbitCountBandAt :
  (c : CertifiedRepresentativeClass) →
  P2OrbitCountBand (forcedStableOrbitP2At c)
orbitCountBandAt (stayRep GT.certifiedExplicitWidth1)
  rewrite stayForcedStableOrbitP2-explicitWidth1 = reduced2
orbitCountBandAt (stayRep GT.certifiedExplicitWidth3)
  rewrite stayForcedStableOrbitP2-explicitWidth3 = saturated15
orbitCountBandAt (stayRep GT.certifiedDenseComposed)
  rewrite stayForcedStableOrbitP2-denseComposed = saturated15
orbitCountBandAt (anchoredRep GT.certifiedBalancedCycle)
  rewrite exitToAnchoredForcedStableOrbitP2-balancedCycle = saturated15
orbitCountBandAt (anchoredRep GT.certifiedBalancedComposed)
  rewrite exitToAnchoredForcedStableOrbitP2-balancedComposed = saturated15
orbitCountBandAt (immediateRep IERC.exitExplicitWidth2)
  rewrite immediateExitForcedStableOrbitP2-explicitWidth2 = saturated15
orbitCountBandAt (immediateRep IERC.exitAnchoredTrajectory)
  rewrite immediateExitForcedStableOrbitP2-anchoredTrajectory = saturated15
orbitCountBandAt (immediateRep IERC.exitFullSupportCascade)
  rewrite immediateExitForcedStableOrbitP2-fullSupportCascade = saturated15

data P2PersistenceTier : Set where
  reducedPersistence : P2PersistenceTier
  saturatedPersistence : P2PersistenceTier

tierFromOrbitCountBand :
  ∀ {n} →
  P2OrbitCountBand n → P2PersistenceTier
tierFromOrbitCountBand reduced2 = reducedPersistence
tierFromOrbitCountBand saturated15 = saturatedPersistence

p2PersistenceTierAt :
  CertifiedRepresentativeClass → P2PersistenceTier
p2PersistenceTierAt c =
  tierFromOrbitCountBand (orbitCountBandAt c)

p2PersistenceTier-factors-through-orbitCountBand :
  ∀ c →
  p2PersistenceTierAt c
    ≡
  tierFromOrbitCountBand (orbitCountBandAt c)
p2PersistenceTier-factors-through-orbitCountBand _ = refl

stayRepresentativeOrbitP2≤15 :
  ∀ c →
  stayRepresentativeForcedStableCountOrbitP2 c ≤ 15
stayRepresentativeOrbitP2≤15 GT.certifiedExplicitWidth1
  rewrite stayForcedStableOrbitP2-explicitWidth1 = 2≤15
stayRepresentativeOrbitP2≤15 GT.certifiedExplicitWidth3
  rewrite stayForcedStableOrbitP2-explicitWidth3 = ≤-refl
stayRepresentativeOrbitP2≤15 GT.certifiedDenseComposed
  rewrite stayForcedStableOrbitP2-denseComposed = ≤-refl

anchoredRepresentativeOrbitP2≡15 :
  ∀ c →
  exitToAnchoredRepresentativeForcedStableCountOrbitP2 c ≡ 15
anchoredRepresentativeOrbitP2≡15 GT.certifiedBalancedCycle =
  exitToAnchoredForcedStableOrbitP2-balancedCycle
anchoredRepresentativeOrbitP2≡15 GT.certifiedBalancedComposed =
  exitToAnchoredForcedStableOrbitP2-balancedComposed

immediateRepresentativeOrbitP2≡15 :
  ∀ c →
  immediateExitRepresentativeForcedStableCountOrbitP2 c ≡ 15
immediateRepresentativeOrbitP2≡15 IERC.exitExplicitWidth2 =
  immediateExitForcedStableOrbitP2-explicitWidth2
immediateRepresentativeOrbitP2≡15 IERC.exitAnchoredTrajectory =
  immediateExitForcedStableOrbitP2-anchoredTrajectory
immediateRepresentativeOrbitP2≡15 IERC.exitFullSupportCascade =
  immediateExitForcedStableOrbitP2-fullSupportCascade

immediateRepresentativePositiveOrbitPressure :
  ∀ c →
  suc zero ≤ immediateExitRepresentativeForcedStableCountOrbitP2 c
immediateRepresentativePositiveOrbitPressure IERC.exitExplicitWidth2
  rewrite immediateExitForcedStableOrbitP2-explicitWidth2 = 1≤15
immediateRepresentativePositiveOrbitPressure IERC.exitAnchoredTrajectory
  rewrite immediateExitForcedStableOrbitP2-anchoredTrajectory = 1≤15
immediateRepresentativePositiveOrbitPressure IERC.exitFullSupportCascade
  rewrite immediateExitForcedStableOrbitP2-fullSupportCascade = 1≤15

anchoredRepresentativePositiveOrbitPressure :
  ∀ c →
  suc zero ≤ exitToAnchoredRepresentativeForcedStableCountOrbitP2 c
anchoredRepresentativePositiveOrbitPressure GT.certifiedBalancedCycle
  rewrite exitToAnchoredForcedStableOrbitP2-balancedCycle = 1≤15
anchoredRepresentativePositiveOrbitPressure GT.certifiedBalancedComposed
  rewrite exitToAnchoredForcedStableOrbitP2-balancedComposed = 1≤15

data CertifiedRepresentativePersistenceFactorization : Set₁ where
  canonicalCertifiedRepresentativePersistenceFactorization :
    CertifiedRepresentativePersistenceFactorization

------------------------------------------------------------------------
-- Current exact tier identities.

explicitWidth1-reducedPersistence :
  p2PersistenceTierAt (stayRep GT.certifiedExplicitWidth1)
    ≡
  reducedPersistence
explicitWidth1-reducedPersistence = refl

explicitWidth3-saturatedPersistence :
  p2PersistenceTierAt (stayRep GT.certifiedExplicitWidth3)
    ≡
  saturatedPersistence
explicitWidth3-saturatedPersistence = refl

denseComposed-saturatedPersistence :
  p2PersistenceTierAt (stayRep GT.certifiedDenseComposed)
    ≡
  saturatedPersistence
denseComposed-saturatedPersistence = refl

balancedCycle-saturatedPersistence :
  p2PersistenceTierAt (anchoredRep GT.certifiedBalancedCycle)
    ≡
  saturatedPersistence
balancedCycle-saturatedPersistence = refl

balancedComposed-saturatedPersistence :
  p2PersistenceTierAt (anchoredRep GT.certifiedBalancedComposed)
    ≡
  saturatedPersistence
balancedComposed-saturatedPersistence = refl

explicitWidth2-saturatedPersistence :
  p2PersistenceTierAt (immediateRep IERC.exitExplicitWidth2)
    ≡
  saturatedPersistence
explicitWidth2-saturatedPersistence = refl

anchoredTrajectory-saturatedPersistence :
  p2PersistenceTierAt (immediateRep IERC.exitAnchoredTrajectory)
    ≡
  saturatedPersistence
anchoredTrajectory-saturatedPersistence = refl

fullSupportCascade-saturatedPersistence :
  p2PersistenceTierAt (immediateRep IERC.exitFullSupportCascade)
    ≡
  saturatedPersistence
fullSupportCascade-saturatedPersistence = refl
