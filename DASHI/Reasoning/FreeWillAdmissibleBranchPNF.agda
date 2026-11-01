module DASHI.Reasoning.FreeWillAdmissibleBranchPNF where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Observer-local admissible-branch vocabulary.
--
-- This module records the new thread delta: "free will" is modelled only as
-- observer-local navigation among nearby admissible manifold branches.  The
-- surface fuses local PNF evidence with population packets, treats
-- conceivable alternatives as an observer-local branch-volume estimate, and
-- keeps inverse choice/world constraints bidirectional.  It is not a
-- metaphysical theorem and it does not enumerate all possible branches.

data ObserverLocality : Set where
  situatedObserverLocal : ObserverLocality
  populationLocal : ObserverLocality
  manifoldNeighbourhoodLocal : ObserverLocality

data BranchNavigationMode : Set where
  nearbyAdmissibleNavigation : BranchNavigationMode
  inverseChoiceConstraintNavigation : BranchNavigationMode
  bidirectionalWorldConstraintNavigation : BranchNavigationMode

data BranchVolumeEstimateKind : Set where
  zeroVisibleBranches : BranchVolumeEstimateKind
  finiteNearbyEstimate : BranchVolumeEstimateKind
  underdeterminedEstimate : BranchVolumeEstimateKind
  scopeExceededEstimate : BranchVolumeEstimateKind

data FusionDisposition : Set where
  fusionHeld : FusionDisposition
  fusionAdmissibleCandidate : FusionDisposition
  fusionContradictory : FusionDisposition
  fusionUnsupported : FusionDisposition

data ChoiceWorldConstraintKind : Set where
  choiceConstrainsWorld : ChoiceWorldConstraintKind
  worldConstrainsChoice : ChoiceWorldConstraintKind
  inverseChoiceConstraint : ChoiceWorldConstraintKind
  bidirectionalConstraint : ChoiceWorldConstraintKind
  residualConstraint : ChoiceWorldConstraintKind

data FreeWillBranchGuard : Set where
  NoMetaphysicalFreeWillProof : FreeWillBranchGuard
  NoDeterminismProof : FreeWillBranchGuard
  NoIndividualIntentRecovery : FreeWillBranchGuard
  NoPopulationConsensusTruthClaim : FreeWillBranchGuard
  NoArbitraryFantasyPromotion : FreeWillBranchGuard
  NoBranchEnumerationCompleteness : FreeWillBranchGuard

canonicalFreeWillBranchGuards : List FreeWillBranchGuard
canonicalFreeWillBranchGuards =
  NoMetaphysicalFreeWillProof
  ∷ NoDeterminismProof
  ∷ NoIndividualIntentRecovery
  ∷ NoPopulationConsensusTruthClaim
  ∷ NoArbitraryFantasyPromotion
  ∷ NoBranchEnumerationCompleteness
  ∷ []

------------------------------------------------------------------------
-- Core observer-local surface.

record ObserverLocalBranchNavigationSurface : Set₁ where
  field
    Observer : Set
    WorldState : Set
    ManifoldBranch : Set
    Choice : Set
    NavigationReceipt : Set
    ConstraintReceipt : Set
    BranchVolumeEstimate : Set
    ConstraintResidual : Set

    observerLocality : ObserverLocality
    navigationMode : BranchNavigationMode

    observeWorld :
      Observer →
      WorldState →
      WorldState

    nearbyBranches :
      Observer →
      WorldState →
      List ManifoldBranch

    admissibleBranch :
      Observer →
      WorldState →
      ManifoldBranch →
      Set

    branchDistance :
      Observer →
      WorldState →
      ManifoldBranch →
      Nat

    navigateByChoice :
      Observer →
      WorldState →
      Choice →
      ManifoldBranch

    navigationReceiptFor :
      Observer →
      WorldState →
      Choice →
      NavigationReceipt

    receiptAdmissible :
      NavigationReceipt →
      Set

    choiceConstrains :
      Choice →
      WorldState →
      Set

    worldConstrains :
      WorldState →
      Choice →
      Set

    inverseChoiceForBranch :
      ManifoldBranch →
      Choice

    bidirectionalConstraintReceipt :
      Choice →
      ManifoldBranch →
      ConstraintReceipt

    constraintResidual :
      ConstraintReceipt →
      ConstraintResidual

    residualAsPNF :
      ConstraintResidual →
      Residual.ResidualLevel

    conceivableVolume :
      Observer →
      WorldState →
      BranchVolumeEstimate

    volumeEstimateKind :
      BranchVolumeEstimate →
      BranchVolumeEstimateKind

    volumeEstimateAdmissible :
      BranchVolumeEstimate →
      Set

    observerLocalOnly :
      String

open ObserverLocalBranchNavigationSurface public

record PNFPopulationBranchFusionSurface
    (navigation : ObserverLocalBranchNavigationSurface) : Set₁ where
  field
    PopulationPacket : Set
    PopulationReceipt : Set
    PopulationEstimate : Set

    localChoicePNF :
      Observer navigation →
      Choice navigation →
      Residual.PredicatePNF

    branchPNF :
      ManifoldBranch navigation →
      Residual.PredicatePNF

    populationPNF :
      PopulationPacket →
      Residual.PredicatePNF

    populationReceiptFor :
      PopulationPacket →
      PopulationReceipt

    populationReceiptAdmissible :
      PopulationReceipt →
      Set

    populationEstimate :
      PopulationPacket →
      PopulationEstimate

    pnfResidualFor :
      Observer navigation →
      Choice navigation →
      ManifoldBranch navigation →
      Residual.ResidualLevel

    populationResidualFor :
      PopulationPacket →
      ManifoldBranch navigation →
      Residual.ResidualLevel

    fusedResidual :
      Observer navigation →
      Choice navigation →
      PopulationPacket →
      ManifoldBranch navigation →
      Residual.ResidualLevel

    fusedDisposition :
      Observer navigation →
      Choice navigation →
      PopulationPacket →
      ManifoldBranch navigation →
      FusionDisposition

    fusionReading :
      String

open PNFPopulationBranchFusionSurface public

record ConceivableBranchVolumeWitness
    (navigation : ObserverLocalBranchNavigationSurface) : Set where
  field
    observer :
      Observer navigation

    world :
      WorldState navigation

    estimate :
      BranchVolumeEstimate navigation

    estimateMatchesSurface :
      estimate ≡ conceivableVolume navigation observer world

    estimateIsAdmissible :
      volumeEstimateAdmissible navigation estimate

    estimateKind :
      BranchVolumeEstimateKind

    estimateKindMatches :
      volumeEstimateKind navigation estimate ≡ estimateKind

    witnessReading :
      String

open ConceivableBranchVolumeWitness public

record BidirectionalChoiceWorldConstraintWitness
    (navigation : ObserverLocalBranchNavigationSurface) : Set where
  field
    observer :
      Observer navigation

    world :
      WorldState navigation

    choice :
      Choice navigation

    branch :
      ManifoldBranch navigation

    branchIsNavigationImage :
      branch ≡ navigateByChoice navigation observer world choice

    choiceGate :
      choiceConstrains navigation choice world

    worldGate :
      worldConstrains navigation world choice

    inverseChoice :
      Choice navigation

    inverseChoiceMatches :
      inverseChoice ≡ inverseChoiceForBranch navigation branch

    constraintReceipt :
      ConstraintReceipt navigation

    constraintReceiptMatches :
      constraintReceipt
      ≡
      bidirectionalConstraintReceipt navigation choice branch

    pnfResidual :
      Residual.ResidualLevel

    pnfResidualMatches :
      pnfResidual
      ≡
      residualAsPNF navigation
        (constraintResidual navigation constraintReceipt)

    witnessReading :
      String

open BidirectionalChoiceWorldConstraintWitness public

record FreeWillAdmissibleBranchPNFThreadDelta : Set₁ where
  field
    navigationSurface :
      ObserverLocalBranchNavigationSurface

    pnfPopulationFusion :
      PNFPopulationBranchFusionSurface navigationSurface

    canonicalConceivableWitness :
      ConceivableBranchVolumeWitness navigationSurface

    canonicalConstraintWitness :
      BidirectionalChoiceWorldConstraintWitness navigationSurface

    guards :
      List FreeWillBranchGuard

    guardsAreCanonical :
      guards ≡ canonicalFreeWillBranchGuards

    metaphysicalFreeWillProof :
      Bool

    metaphysicalFreeWillProofIsFalse :
      metaphysicalFreeWillProof ≡ false

    determinismProof :
      Bool

    determinismProofIsFalse :
      determinismProof ≡ false

    individualIntentRecovery :
      Bool

    individualIntentRecoveryIsFalse :
      individualIntentRecovery ≡ false

    populationConsensusTruthClaim :
      Bool

    populationConsensusTruthClaimIsFalse :
      populationConsensusTruthClaim ≡ false

    arbitraryFantasyPromotion :
      Bool

    arbitraryFantasyPromotionIsFalse :
      arbitraryFantasyPromotion ≡ false

    branchEnumerationCompleteness :
      Bool

    branchEnumerationCompletenessIsFalse :
      branchEnumerationCompleteness ≡ false

    threadReading :
      String

open FreeWillAdmissibleBranchPNFThreadDelta public

record FreeWillBranchNonPromotionCertificate
    (delta : FreeWillAdmissibleBranchPNFThreadDelta) : Set where
  field
    metaphysicalProofBlocked :
      metaphysicalFreeWillProof delta ≡ false

    determinismProofBlocked :
      determinismProof delta ≡ false

    individualIntentRecoveryBlocked :
      individualIntentRecovery delta ≡ false

    populationConsensusTruthBlocked :
      populationConsensusTruthClaim delta ≡ false

    fantasyPromotionBlocked :
      arbitraryFantasyPromotion delta ≡ false

    enumerationCompletenessBlocked :
      branchEnumerationCompleteness delta ≡ false

    certificateReading :
      String

open FreeWillBranchNonPromotionCertificate public

------------------------------------------------------------------------
-- Canonical toy inhabitants.

data ToyFreeWillToken : Set where
  toyObserver : ToyFreeWillToken
  toyWorld : ToyFreeWillToken
  toyNearbyBranch : ToyFreeWillToken
  toyAlternateBranch : ToyFreeWillToken
  toyChoice : ToyFreeWillToken
  toyInverseChoice : ToyFreeWillToken
  toyNavigationReceipt : ToyFreeWillToken
  toyConstraintReceipt : ToyFreeWillToken
  toyConstraintResidual : ToyFreeWillToken
  toyPopulationPacket : ToyFreeWillToken
  toyPopulationReceipt : ToyFreeWillToken
  toyPopulationEstimate : ToyFreeWillToken
  toyBranchVolumeEstimate : ToyFreeWillToken

toyChoicePNF : Residual.PredicatePNF
toyChoicePNF =
  Residual.predicatePNF
    "observer-navigates"
    Residual.sig-agent-goal
    (Residual.opaqueArg "toy-observer")
    (Residual.absent)
    (Residual.opaqueArg "nearby-admissible-branch")
    Residual.modal
    Residual.hedgedEvidence
    "toy-local-choice-receipt"

toyBranchPNF : Residual.PredicatePNF
toyBranchPNF =
  Residual.predicatePNF
    "branch-is-nearby"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "toy-nearby-branch")
    Residual.absent
    Residual.modal
    Residual.hedgedEvidence
    "toy-branch-receipt"

toyPopulationPNF : Residual.PredicatePNF
toyPopulationPNF =
  Residual.predicatePNF
    "population-estimates-branch-volume"
    Residual.sig-agent-theme
    (Residual.opaqueArg "toy-population")
    (Residual.opaqueArg "admissible-branch-volume")
    Residual.absent
    Residual.modal
    Residual.attributedEvidence
    "toy-population-receipt"

canonicalObserverLocalBranchNavigationSurface :
  ObserverLocalBranchNavigationSurface
canonicalObserverLocalBranchNavigationSurface =
  record
    { Observer =
        ToyFreeWillToken
    ; WorldState =
        ToyFreeWillToken
    ; ManifoldBranch =
        ToyFreeWillToken
    ; Choice =
        ToyFreeWillToken
    ; NavigationReceipt =
        ToyFreeWillToken
    ; ConstraintReceipt =
        ToyFreeWillToken
    ; BranchVolumeEstimate =
        ToyFreeWillToken
    ; ConstraintResidual =
        ToyFreeWillToken
    ; observerLocality =
        situatedObserverLocal
    ; navigationMode =
        bidirectionalWorldConstraintNavigation
    ; observeWorld =
        λ _ world → world
    ; nearbyBranches =
        λ _ _ → toyNearbyBranch ∷ toyAlternateBranch ∷ []
    ; admissibleBranch =
        λ _ _ _ → ⊤
    ; branchDistance =
        λ _ _ branch →
          caseBranchDistance branch
    ; navigateByChoice =
        λ _ _ _ → toyNearbyBranch
    ; navigationReceiptFor =
        λ _ _ _ → toyNavigationReceipt
    ; receiptAdmissible =
        λ _ → ⊤
    ; choiceConstrains =
        λ _ _ → ⊤
    ; worldConstrains =
        λ _ _ → ⊤
    ; inverseChoiceForBranch =
        λ _ → toyInverseChoice
    ; bidirectionalConstraintReceipt =
        λ _ _ → toyConstraintReceipt
    ; constraintResidual =
        λ _ → toyConstraintResidual
    ; residualAsPNF =
        λ _ → Residual.partial
    ; conceivableVolume =
        λ _ _ → toyBranchVolumeEstimate
    ; volumeEstimateKind =
        λ _ → finiteNearbyEstimate
    ; volumeEstimateAdmissible =
        λ _ → ⊤
    ; observerLocalOnly =
        "Conceivable alternatives are observer-local estimates of nearby admissible branch volume."
    }
  where
    caseBranchDistance : ToyFreeWillToken → Nat
    caseBranchDistance toyNearbyBranch = suc zero
    caseBranchDistance toyAlternateBranch = suc (suc zero)
    caseBranchDistance _ = zero

canonicalPNFPopulationBranchFusionSurface :
  PNFPopulationBranchFusionSurface
    canonicalObserverLocalBranchNavigationSurface
canonicalPNFPopulationBranchFusionSurface =
  record
    { PopulationPacket =
        ToyFreeWillToken
    ; PopulationReceipt =
        ToyFreeWillToken
    ; PopulationEstimate =
        ToyFreeWillToken
    ; localChoicePNF =
        λ _ _ → toyChoicePNF
    ; branchPNF =
        λ _ → toyBranchPNF
    ; populationPNF =
        λ _ → toyPopulationPNF
    ; populationReceiptFor =
        λ _ → toyPopulationReceipt
    ; populationReceiptAdmissible =
        λ _ → ⊤
    ; populationEstimate =
        λ _ → toyPopulationEstimate
    ; pnfResidualFor =
        λ _ _ _ → Residual.partial
    ; populationResidualFor =
        λ _ _ → Residual.noTypedMeet
    ; fusedResidual =
        λ _ _ _ _ → Residual.noTypedMeet
    ; fusedDisposition =
        λ _ _ _ _ → fusionHeld
    ; fusionReading =
        "Toy fusion holds observer-local PNF and population packets together without treating population consensus as truth."
    }

canonicalConceivableBranchVolumeWitness :
  ConceivableBranchVolumeWitness
    canonicalObserverLocalBranchNavigationSurface
canonicalConceivableBranchVolumeWitness =
  record
    { observer =
        toyObserver
    ; world =
        toyWorld
    ; estimate =
        toyBranchVolumeEstimate
    ; estimateMatchesSurface =
        refl
    ; estimateIsAdmissible =
        tt
    ; estimateKind =
        finiteNearbyEstimate
    ; estimateKindMatches =
        refl
    ; witnessReading =
        "The toy conceivable witness is a finite nearby estimate, not a complete branch enumeration."
    }

canonicalBidirectionalChoiceWorldConstraintWitness :
  BidirectionalChoiceWorldConstraintWitness
    canonicalObserverLocalBranchNavigationSurface
canonicalBidirectionalChoiceWorldConstraintWitness =
  record
    { observer =
        toyObserver
    ; world =
        toyWorld
    ; choice =
        toyChoice
    ; branch =
        toyNearbyBranch
    ; branchIsNavigationImage =
        refl
    ; choiceGate =
        tt
    ; worldGate =
        tt
    ; inverseChoice =
        toyInverseChoice
    ; inverseChoiceMatches =
        refl
    ; constraintReceipt =
        toyConstraintReceipt
    ; constraintReceiptMatches =
        refl
    ; pnfResidual =
        Residual.partial
    ; pnfResidualMatches =
        refl
    ; witnessReading =
        "Choice constrains the world branch and world state constrains admissible choice; the inverse is local and residual-bearing."
    }

canonicalFreeWillAdmissibleBranchPNFThreadDelta :
  FreeWillAdmissibleBranchPNFThreadDelta
canonicalFreeWillAdmissibleBranchPNFThreadDelta =
  record
    { navigationSurface =
        canonicalObserverLocalBranchNavigationSurface
    ; pnfPopulationFusion =
        canonicalPNFPopulationBranchFusionSurface
    ; canonicalConceivableWitness =
        canonicalConceivableBranchVolumeWitness
    ; canonicalConstraintWitness =
        canonicalBidirectionalChoiceWorldConstraintWitness
    ; guards =
        canonicalFreeWillBranchGuards
    ; guardsAreCanonical =
        refl
    ; metaphysicalFreeWillProof =
        false
    ; metaphysicalFreeWillProofIsFalse =
        refl
    ; determinismProof =
        false
    ; determinismProofIsFalse =
        refl
    ; individualIntentRecovery =
        false
    ; individualIntentRecoveryIsFalse =
        refl
    ; populationConsensusTruthClaim =
        false
    ; populationConsensusTruthClaimIsFalse =
        refl
    ; arbitraryFantasyPromotion =
        false
    ; arbitraryFantasyPromotionIsFalse =
        refl
    ; branchEnumerationCompleteness =
        false
    ; branchEnumerationCompletenessIsFalse =
        refl
    ; threadReading =
        "Free-will language is discharged as observer-local branch navigation over nearby admissible manifold branches with PNF/population fusion and bidirectional choice/world constraints."
    }

canonicalFreeWillBranchNonPromotionCertificate :
  FreeWillBranchNonPromotionCertificate
    canonicalFreeWillAdmissibleBranchPNFThreadDelta
canonicalFreeWillBranchNonPromotionCertificate =
  record
    { metaphysicalProofBlocked =
        refl
    ; determinismProofBlocked =
        refl
    ; individualIntentRecoveryBlocked =
        refl
    ; populationConsensusTruthBlocked =
        refl
    ; fantasyPromotionBlocked =
        refl
    ; enumerationCompletenessBlocked =
        refl
    ; certificateReading =
        "The canonical delta blocks metaphysical proof, determinism proof, intent recovery, consensus-as-truth, fantasy promotion, and complete branch enumeration."
    }

canonicalFusionResidualHeld :
  fusedResidual
    canonicalPNFPopulationBranchFusionSurface
    toyObserver
    toyChoice
    toyPopulationPacket
    toyNearbyBranch
  ≡
  Residual.noTypedMeet
canonicalFusionResidualHeld = refl

canonicalConstraintResidualPartial :
  pnfResidual canonicalBidirectionalChoiceWorldConstraintWitness
  ≡
  Residual.partial
canonicalConstraintResidualPartial = refl
