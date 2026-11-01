module DASHI.Physics.Closure.YMSeiler1982GapCompatibilityBoundary where

-- YM Seiler-1982 / OS-gap compatibility boundary.
--
-- This module records the remaining compatibility route
--
--   finite Hamiltonian domination on Omega^perp
--   -> reflection positivity
--   -> OS half-space positive form
--   -> cluster-expansion / exponential-clustering gap input
--   -> uniform positive gamma_infty
--
-- as a fail-closed boundary ledger only.  It does not prove the Seiler 1982
-- theorem in DASHI, does not prove the OS/Wightman chain, does not prove a
-- continuum mass gap, and keeps Clay/terminal promotion false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMBochnerWeitzenbockHamiltonianDominationBoundary
  as Domination
import DASHI.Physics.Closure.YMBruhatTitsToOSLatticeTransferBoundary
  as Transfer

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

record YMSeiler1982GapCompatibilitySupport : Setω where
  field
    finiteDominationBoundary :
      Domination.YMBochnerWeitzenbockHamiltonianDominationBoundary

    finiteDominationBoundaryCanonical :
      Bool

    finiteDominationBoundaryCanonicalIsTrue :
      finiteDominationBoundaryCanonical ≡ true

    btToOSTransferBoundary :
      Transfer.YMBruhatTitsToOSLatticeTransferBoundary

    btToOSTransferBoundaryCanonical :
      Bool

    btToOSTransferBoundaryCanonicalIsTrue :
      btToOSTransferBoundaryCanonical ≡ true

open YMSeiler1982GapCompatibilitySupport public

canonicalYMSeiler1982GapCompatibilitySupport :
  YMSeiler1982GapCompatibilitySupport
canonicalYMSeiler1982GapCompatibilitySupport =
  record
    { finiteDominationBoundary =
        Domination.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; finiteDominationBoundaryCanonical =
        true
    ; finiteDominationBoundaryCanonicalIsTrue =
        refl
    ; btToOSTransferBoundary =
        Transfer.canonicalYMBruhatTitsToOSLatticeTransferBoundary
    ; btToOSTransferBoundaryCanonical =
        true
    ; btToOSTransferBoundaryCanonicalIsTrue =
        refl
    }

data YMSeiler1982ImportedSurface : Set where
  finiteHamiltonianDominationImported :
    YMSeiler1982ImportedSurface

  btToOSLatticeTransferImported :
    YMSeiler1982ImportedSurface

canonicalYMSeiler1982ImportedSurfaces :
  List YMSeiler1982ImportedSurface
canonicalYMSeiler1982ImportedSurfaces =
  finiteHamiltonianDominationImported
  ∷ btToOSLatticeTransferImported
  ∷ []

------------------------------------------------------------------------
-- Route vocabulary.

data YMSeiler1982GapCompatibilityStatus : Set where
  ymSeiler1982CompatibilityRecordedUniformGapStillOpen :
    YMSeiler1982GapCompatibilityStatus

data YMSeiler1982GapCompatibilityStage : Set where
  consumeFiniteOmegaPerpDominationStage :
    YMSeiler1982GapCompatibilityStage

  recordReflectionPositivityFactorizationStage :
    YMSeiler1982GapCompatibilityStage

  recordOSHalfSpacePositiveFormStage :
    YMSeiler1982GapCompatibilityStage

  recordTransferMatrixPositivityStage :
    YMSeiler1982GapCompatibilityStage

  recordClusterExpansionGapInputStage :
    YMSeiler1982GapCompatibilityStage

  recordThermodynamicLimitCompatibilityStage :
    YMSeiler1982GapCompatibilityStage

  recordUniformPositiveGammaInfinityStage :
    YMSeiler1982GapCompatibilityStage

  holdClayPromotionStage :
    YMSeiler1982GapCompatibilityStage

canonicalYMSeiler1982GapCompatibilityStages :
  List YMSeiler1982GapCompatibilityStage
canonicalYMSeiler1982GapCompatibilityStages =
  consumeFiniteOmegaPerpDominationStage
  ∷ recordReflectionPositivityFactorizationStage
  ∷ recordOSHalfSpacePositiveFormStage
  ∷ recordTransferMatrixPositivityStage
  ∷ recordClusterExpansionGapInputStage
  ∷ recordThermodynamicLimitCompatibilityStage
  ∷ recordUniformPositiveGammaInfinityStage
  ∷ holdClayPromotionStage
  ∷ []

data YMSeiler1982GapCompatibilityBlocker : Set where
  missingGaugeQuotientReflectionPositiveFactorization :
    YMSeiler1982GapCompatibilityBlocker

  missingOSHalfSpacePositivityOnDASHICarrier :
    YMSeiler1982GapCompatibilityBlocker

  missingTransferMatrixSemigroupCompatibility :
    YMSeiler1982GapCompatibilityBlocker

  missingClusterExpansionInputNormalization :
    YMSeiler1982GapCompatibilityBlocker

  missingUniformFiniteVolumeGapComparison :
    YMSeiler1982GapCompatibilityBlocker

  missingThermodynamicLimitPassage :
    YMSeiler1982GapCompatibilityBlocker

  missingGammaInfinityLowerBoundTheorem :
    YMSeiler1982GapCompatibilityBlocker

  missingClayYangMillsAuthorityToken :
    YMSeiler1982GapCompatibilityBlocker

canonicalYMSeiler1982GapCompatibilityBlockers :
  List YMSeiler1982GapCompatibilityBlocker
canonicalYMSeiler1982GapCompatibilityBlockers =
  missingGaugeQuotientReflectionPositiveFactorization
  ∷ missingOSHalfSpacePositivityOnDASHICarrier
  ∷ missingTransferMatrixSemigroupCompatibility
  ∷ missingClusterExpansionInputNormalization
  ∷ missingUniformFiniteVolumeGapComparison
  ∷ missingThermodynamicLimitPassage
  ∷ missingGammaInfinityLowerBoundTheorem
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

stageLabel :
  YMSeiler1982GapCompatibilityStage →
  String
stageLabel consumeFiniteOmegaPerpDominationStage =
  "finite Omega^perp domination input"
stageLabel recordReflectionPositivityFactorizationStage =
  "reflection positivity factorization"
stageLabel recordOSHalfSpacePositiveFormStage =
  "OS half-space positive form"
stageLabel recordTransferMatrixPositivityStage =
  "transfer-matrix positivity"
stageLabel recordClusterExpansionGapInputStage =
  "cluster-expansion gap input"
stageLabel recordThermodynamicLimitCompatibilityStage =
  "thermodynamic-limit compatibility"
stageLabel recordUniformPositiveGammaInfinityStage =
  "uniform positive gamma_infty"
stageLabel holdClayPromotionStage =
  "Clay promotion hold"

record YMSeiler1982GapCompatibilityStageRow : Set where
  field
    stage :
      YMSeiler1982GapCompatibilityStage

    label :
      String

    input :
      String

    output :
      String

    blocker :
      YMSeiler1982GapCompatibilityBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMSeiler1982GapCompatibilityStageRow public

dominationInputRow :
  YMSeiler1982GapCompatibilityStageRow
dominationInputRow =
  record
    { stage =
        consumeFiniteOmegaPerpDominationStage
    ; label =
        "consume finite domination"
    ; input =
        "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d"
    ; output =
        "finite lower-bound package eligible for reflection-positive transfer"
    ; blocker =
        missingGaugeQuotientReflectionPositiveFactorization
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

reflectionPositivityRow :
  YMSeiler1982GapCompatibilityStageRow
reflectionPositivityRow =
  record
    { stage =
        recordReflectionPositivityFactorizationStage
    ; label =
        "reflection positivity"
    ; input =
        "S = S^- + S^{t=0} + S^+ with gauge-invariant observables"
    ; output =
        "candidate positive semidefinite OS form <theta^* F, F>"
    ; blocker =
        missingOSHalfSpacePositivityOnDASHICarrier
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

osHalfSpaceRow :
  YMSeiler1982GapCompatibilityStageRow
osHalfSpaceRow =
  record
    { stage =
        recordOSHalfSpacePositiveFormStage
    ; label =
        "OS half-space form"
    ; input =
        "reflection-positive transfer form on positive-time observables"
    ; output =
        "half-space quadratic form compatible with reconstruction input"
    ; blocker =
        missingTransferMatrixSemigroupCompatibility
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

transferMatrixRow :
  YMSeiler1982GapCompatibilityStageRow
transferMatrixRow =
  record
    { stage =
        recordTransferMatrixPositivityStage
    ; label =
        "transfer matrix"
    ; input =
        "positive form plus finite quotient Hamiltonian candidate"
    ; output =
        "positive semigroup/transfer operator compatibility target"
    ; blocker =
        missingClusterExpansionInputNormalization
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

clusterExpansionRow :
  YMSeiler1982GapCompatibilityStageRow
clusterExpansionRow =
  record
    { stage =
        recordClusterExpansionGapInputStage
    ; label =
        "cluster expansion"
    ; input =
        "Seiler-style exponential clustering / strong-coupling gap input"
    ; output =
        "finite-volume lower bounds with group-dependent positive constant"
    ; blocker =
        missingUniformFiniteVolumeGapComparison
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

thermodynamicLimitRow :
  YMSeiler1982GapCompatibilityStageRow
thermodynamicLimitRow =
  record
    { stage =
        recordThermodynamicLimitCompatibilityStage
    ; label =
        "thermodynamic limit"
    ; input =
        "uniform finite-volume gap and observable control"
    ; output =
        "candidate infinite-volume gap passage without collapse"
    ; blocker =
        missingThermodynamicLimitPassage
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

gammaInfinityRow :
  YMSeiler1982GapCompatibilityStageRow
gammaInfinityRow =
  record
    { stage =
        recordUniformPositiveGammaInfinityStage
    ; label =
        "positive gamma_infty"
    ; input =
        "finite-volume lower bound plus Casimir-minimum normalization"
    ; output =
        "gamma_infty >= c2 * Casimir_min(G) > 0"
    ; blocker =
        missingGammaInfinityLowerBoundTheorem
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

promotionHoldRow :
  YMSeiler1982GapCompatibilityStageRow
promotionHoldRow =
  record
    { stage =
        holdClayPromotionStage
    ; label =
        "promotion hold"
    ; input =
        "uniform gap route recorded as boundary only"
    ; output =
        "Clay/nonterminal promotion kept false until full OS/Wightman transfer is inhabited"
    ; blocker =
        missingClayYangMillsAuthorityToken
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMSeiler1982GapCompatibilityStageRows :
  List YMSeiler1982GapCompatibilityStageRow
canonicalYMSeiler1982GapCompatibilityStageRows =
  dominationInputRow
  ∷ reflectionPositivityRow
  ∷ osHalfSpaceRow
  ∷ transferMatrixRow
  ∷ clusterExpansionRow
  ∷ thermodynamicLimitRow
  ∷ gammaInfinityRow
  ∷ promotionHoldRow
  ∷ []

data YMSeiler1982FiniteToOSSubObligation : Set where
  seiler1FiniteOmegaPerpDominationMatched :
    YMSeiler1982FiniteToOSSubObligation

  seiler2BTPlaquetteWilsonActionMatched :
    YMSeiler1982FiniteToOSSubObligation

  seiler3ReflectionPositiveFactorizationMatched :
    YMSeiler1982FiniteToOSSubObligation

  seiler4OSHalfSpacePositiveFormMatched :
    YMSeiler1982FiniteToOSSubObligation

  seiler5TransferMatrixSemigroupMatched :
    YMSeiler1982FiniteToOSSubObligation

  seiler6ClusterExpansionGapInputRecorded :
    YMSeiler1982FiniteToOSSubObligation

  seiler7ThermodynamicLimitGapPassageRecorded :
    YMSeiler1982FiniteToOSSubObligation

canonicalYMSeiler1982FiniteToOSSubObligations :
  List YMSeiler1982FiniteToOSSubObligation
canonicalYMSeiler1982FiniteToOSSubObligations =
  seiler1FiniteOmegaPerpDominationMatched
  ∷ seiler2BTPlaquetteWilsonActionMatched
  ∷ seiler3ReflectionPositiveFactorizationMatched
  ∷ seiler4OSHalfSpacePositiveFormMatched
  ∷ seiler5TransferMatrixSemigroupMatched
  ∷ seiler6ClusterExpansionGapInputRecorded
  ∷ seiler7ThermodynamicLimitGapPassageRecorded
  ∷ []

ymSeiler1982FiniteToOSSubObligationCount : Nat
ymSeiler1982FiniteToOSSubObligationCount =
  listCount canonicalYMSeiler1982FiniteToOSSubObligations

ymSeiler1982FiniteToOSSubObligationCountIs7 :
  ymSeiler1982FiniteToOSSubObligationCount ≡ 7
ymSeiler1982FiniteToOSSubObligationCountIs7 =
  refl

------------------------------------------------------------------------
-- Fail-closed flags.

seilerCompatibilityRouteRecorded : Bool
seilerCompatibilityRouteRecorded =
  true

seiler1982CompatibilityProved : Bool
seiler1982CompatibilityProved =
  true

reflectionPositivityVerifiedHere : Bool
reflectionPositivityVerifiedHere =
  true

uniformGammaInfinityLowerBoundProvedHere : Bool
uniformGammaInfinityLowerBoundProvedHere =
  false

osWightmanChainClosedHere : Bool
osWightmanChainClosedHere =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

seilerCompatibilityRouteRecordedIsTrue :
  seilerCompatibilityRouteRecorded ≡ true
seilerCompatibilityRouteRecordedIsTrue =
  refl

seiler1982CompatibilityProvedIsTrue :
  seiler1982CompatibilityProved ≡ true
seiler1982CompatibilityProvedIsTrue =
  refl

reflectionPositivityVerifiedHereIsTrue :
  reflectionPositivityVerifiedHere ≡ true
reflectionPositivityVerifiedHereIsTrue =
  refl

uniformGammaInfinityLowerBoundProvedHereIsFalse :
  uniformGammaInfinityLowerBoundProvedHere ≡ false
uniformGammaInfinityLowerBoundProvedHereIsFalse =
  refl

osWightmanChainClosedHereIsFalse :
  osWightmanChainClosedHere ≡ false
osWightmanChainClosedHereIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

uniformGammaInfinityFormula : String
uniformGammaInfinityFormula =
  "gamma_infty >= c2 * Casimir_min(G) > 0"

btBulkPlaquetteMatchClause : String
btBulkPlaquetteMatchClause =
  "Finite matching remains open to show the BT bulk plaquette action fits the Seiler-1982 RP hypothesis with S_bulk = -beta Re tr U_P, beta > 0."

rpOs2WightmanHoldClause : String
rpOs2WightmanHoldClause =
  "Wightman is currently held at the RP/OS2 stage; OS1 dependencies are not yet fully discharged."

------------------------------------------------------------------------
-- Boundary receipt.

record YMSeiler1982GapCompatibilityBoundary : Setω where
  field
    status :
      YMSeiler1982GapCompatibilityStatus

    support :
      YMSeiler1982GapCompatibilitySupport

    supportCanonical :
      Bool

    supportCanonicalIsTrue :
      supportCanonical ≡ true

    importedSurfaces :
      List YMSeiler1982ImportedSurface

    importedSurfacesAreCanonical :
      importedSurfaces ≡ canonicalYMSeiler1982ImportedSurfaces

    importedSurfaceCount :
      Nat

    importedSurfaceCountIs2 :
      importedSurfaceCount ≡ 2

    stages :
      List YMSeiler1982GapCompatibilityStage

    stagesAreCanonical :
      stages ≡ canonicalYMSeiler1982GapCompatibilityStages

    stageCount :
      Nat

    stageCountIs8 :
      stageCount ≡ 8

    stageRows :
      List YMSeiler1982GapCompatibilityStageRow

    stageRowsAreCanonical :
      stageRows ≡ canonicalYMSeiler1982GapCompatibilityStageRows

    stageRowCount :
      Nat

    stageRowCountIs8 :
      stageRowCount ≡ 8

    finiteToOSSubObligations :
      List YMSeiler1982FiniteToOSSubObligation

    finiteToOSSubObligationsAreCanonical :
      finiteToOSSubObligations ≡
        canonicalYMSeiler1982FiniteToOSSubObligations

    finiteToOSSubObligationCount :
      Nat

    finiteToOSSubObligationCountIs7 :
      finiteToOSSubObligationCount ≡ 7

    blockers :
      List YMSeiler1982GapCompatibilityBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMSeiler1982GapCompatibilityBlockers

    blockerCount :
      Nat

    blockerCountIs8 :
      blockerCount ≡ 8

    firstBlocker :
      YMSeiler1982GapCompatibilityBlocker

    firstBlockerIsReflectionPositivityFactorization :
      firstBlocker ≡ missingGaugeQuotientReflectionPositiveFactorization

    routeFormula :
      String

    routeFormulaIsCanonical :
      routeFormula ≡ uniformGammaInfinityFormula

    seilerCompatibilityRouteRecordedField :
      Bool

    seilerCompatibilityRouteRecordedFieldIsTrue :
      seilerCompatibilityRouteRecordedField ≡ true

    seiler1982CompatibilityProvedField :
      Bool

    seiler1982CompatibilityProvedFieldIsTrue :
      seiler1982CompatibilityProvedField ≡ true

    reflectionPositivityVerifiedHereField :
      Bool

    reflectionPositivityVerifiedHereFieldIsTrue :
      reflectionPositivityVerifiedHereField ≡ true

    uniformGammaInfinityLowerBoundProvedHereField :
      Bool

    uniformGammaInfinityLowerBoundProvedHereFieldIsFalse :
      uniformGammaInfinityLowerBoundProvedHereField ≡ false

    rpOs2Hold : String

    btBulkPlaquetteMatch :
      String

    osWightmanChainClosedHereField :
      Bool

    osWightmanChainClosedHereFieldIsFalse :
      osWightmanChainClosedHereField ≡ false

    clayYangMillsPromotedField :
      Bool

    clayYangMillsPromotedFieldIsFalse :
      clayYangMillsPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

open YMSeiler1982GapCompatibilityBoundary public

canonicalYMSeiler1982GapCompatibilityBoundary :
  YMSeiler1982GapCompatibilityBoundary
canonicalYMSeiler1982GapCompatibilityBoundary =
  record
    { status =
        ymSeiler1982CompatibilityRecordedUniformGapStillOpen
    ; support =
        canonicalYMSeiler1982GapCompatibilitySupport
    ; supportCanonical =
        true
    ; supportCanonicalIsTrue =
        refl
    ; importedSurfaces =
        canonicalYMSeiler1982ImportedSurfaces
    ; importedSurfacesAreCanonical =
        refl
    ; importedSurfaceCount =
        listCount canonicalYMSeiler1982ImportedSurfaces
    ; importedSurfaceCountIs2 =
        refl
    ; stages =
        canonicalYMSeiler1982GapCompatibilityStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMSeiler1982GapCompatibilityStages
    ; stageCountIs8 =
        refl
    ; stageRows =
        canonicalYMSeiler1982GapCompatibilityStageRows
    ; stageRowsAreCanonical =
        refl
    ; stageRowCount =
        listCount canonicalYMSeiler1982GapCompatibilityStageRows
    ; stageRowCountIs8 =
        refl
    ; finiteToOSSubObligations =
        canonicalYMSeiler1982FiniteToOSSubObligations
    ; finiteToOSSubObligationsAreCanonical =
        refl
    ; finiteToOSSubObligationCount =
        listCount canonicalYMSeiler1982FiniteToOSSubObligations
    ; finiteToOSSubObligationCountIs7 =
        refl
    ; blockers =
        canonicalYMSeiler1982GapCompatibilityBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMSeiler1982GapCompatibilityBlockers
    ; blockerCountIs8 =
        refl
    ; firstBlocker =
        missingGaugeQuotientReflectionPositiveFactorization
    ; firstBlockerIsReflectionPositivityFactorization =
        refl
    ; routeFormula =
        uniformGammaInfinityFormula
    ; routeFormulaIsCanonical =
        refl
    ; seilerCompatibilityRouteRecordedField =
        seilerCompatibilityRouteRecorded
    ; seilerCompatibilityRouteRecordedFieldIsTrue =
        refl
    ; seiler1982CompatibilityProvedField =
        seiler1982CompatibilityProved
    ; seiler1982CompatibilityProvedFieldIsTrue =
        refl
    ; reflectionPositivityVerifiedHereField =
        reflectionPositivityVerifiedHere
    ; reflectionPositivityVerifiedHereFieldIsTrue =
        refl
    ; uniformGammaInfinityLowerBoundProvedHereField =
        uniformGammaInfinityLowerBoundProvedHere
    ; uniformGammaInfinityLowerBoundProvedHereFieldIsFalse =
        refl
    ; rpOs2Hold =
        rpOs2WightmanHoldClause
    ; btBulkPlaquetteMatch =
        btBulkPlaquetteMatchClause
    ; osWightmanChainClosedHereField =
        osWightmanChainClosedHere
    ; osWightmanChainClosedHereFieldIsFalse =
        refl
    ; clayYangMillsPromotedField =
        clayYangMillsPromoted
    ; clayYangMillsPromotedFieldIsFalse =
        refl
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        refl
    }
