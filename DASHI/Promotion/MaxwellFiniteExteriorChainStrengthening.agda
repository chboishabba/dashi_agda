module DASHI.Promotion.MaxwellFiniteExteriorChainStrengthening where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.ClassicalFieldObligations as Classical
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Exterior
import DASHI.Promotion.MaxwellHodgeSourceCalibration as Calibration
import DASHI.Promotion.MaxwellHodgeSourceConservationObligations as Conservation

------------------------------------------------------------------------
-- Maxwell finite exterior-chain strengthening.
--
-- This module is a second-level, fail-closed Maxwell surface.  The older
-- adapter constructs the homogeneous finite exterior-calculus fragment
-- F = d A and d F = 0.  This file records the full finite chain that a
-- Maxwell promotion must traverse:
--
--   A -> F -> d F = 0 -> *F -> d * F -> J -> d * F = J
--     -> d J = 0 -> div J = 0 -> units/observables -> promotion guard.
--
-- Only the homogeneous curvature chain is constructed.  Metric/Hodge,
-- source-current extraction, source equations, calibration, empirical
-- comparison, and Maxwell promotion remain blocked.

data FiniteMaxwellChainNode : Set where
  potentialOneFormNode : FiniteMaxwellChainNode
  curvatureTwoFormNode : FiniteMaxwellChainNode
  homogeneousBianchiNode : FiniteMaxwellChainNode
  metricOrientationNode : FiniteMaxwellChainNode
  hodgeDualTwoFormNode : FiniteMaxwellChainNode
  exteriorDStarFNode : FiniteMaxwellChainNode
  sourceCurrentThreeFormNode : FiniteMaxwellChainNode
  inhomogeneousEquationNode : FiniteMaxwellChainNode
  continuityDJZeroNode : FiniteMaxwellChainNode
  divergenceJZeroNode : FiniteMaxwellChainNode
  unitCalibrationNode : FiniteMaxwellChainNode
  empiricalObservableNode : FiniteMaxwellChainNode
  maxwellPromotionGuardNode : FiniteMaxwellChainNode

data FiniteMaxwellChainStage : Set where
  constructedFiniteExteriorStage : FiniteMaxwellChainStage
  authorityBoundaryStage : FiniteMaxwellChainStage
  proofBoundaryStage : FiniteMaxwellChainStage
  calibrationBoundaryStage : FiniteMaxwellChainStage
  empiricalBoundaryStage : FiniteMaxwellChainStage
  promotionGuardClosedStage : FiniteMaxwellChainStage

data FiniteMaxwellChainBlocker : Set where
  noBlockerConstructedHomogeneous : FiniteMaxwellChainBlocker
  metricOrientationAuthorityBlocker : FiniteMaxwellChainBlocker
  hodgeStarAuthorityBlocker : FiniteMaxwellChainBlocker
  sourceExtractionProofBlocker : FiniteMaxwellChainBlocker
  inhomogeneousEquationProofBlocker : FiniteMaxwellChainBlocker
  sourceConservationProofBlocker : FiniteMaxwellChainBlocker
  vectorDivergenceConventionProofBlocker : FiniteMaxwellChainBlocker
  unitCalibrationAuthorityBlocker : FiniteMaxwellChainBlocker
  empiricalObservableAuthorityBlocker : FiniteMaxwellChainBlocker
  maxwellPromotionGuardBlocker : FiniteMaxwellChainBlocker

classifyFiniteMaxwellNode :
  FiniteMaxwellChainNode → FiniteMaxwellChainStage
classifyFiniteMaxwellNode potentialOneFormNode =
  constructedFiniteExteriorStage
classifyFiniteMaxwellNode curvatureTwoFormNode =
  constructedFiniteExteriorStage
classifyFiniteMaxwellNode homogeneousBianchiNode =
  constructedFiniteExteriorStage
classifyFiniteMaxwellNode metricOrientationNode =
  authorityBoundaryStage
classifyFiniteMaxwellNode hodgeDualTwoFormNode =
  authorityBoundaryStage
classifyFiniteMaxwellNode exteriorDStarFNode =
  proofBoundaryStage
classifyFiniteMaxwellNode sourceCurrentThreeFormNode =
  proofBoundaryStage
classifyFiniteMaxwellNode inhomogeneousEquationNode =
  proofBoundaryStage
classifyFiniteMaxwellNode continuityDJZeroNode =
  proofBoundaryStage
classifyFiniteMaxwellNode divergenceJZeroNode =
  proofBoundaryStage
classifyFiniteMaxwellNode unitCalibrationNode =
  calibrationBoundaryStage
classifyFiniteMaxwellNode empiricalObservableNode =
  empiricalBoundaryStage
classifyFiniteMaxwellNode maxwellPromotionGuardNode =
  promotionGuardClosedStage

blockerForFiniteMaxwellNode :
  FiniteMaxwellChainNode → FiniteMaxwellChainBlocker
blockerForFiniteMaxwellNode potentialOneFormNode =
  noBlockerConstructedHomogeneous
blockerForFiniteMaxwellNode curvatureTwoFormNode =
  noBlockerConstructedHomogeneous
blockerForFiniteMaxwellNode homogeneousBianchiNode =
  noBlockerConstructedHomogeneous
blockerForFiniteMaxwellNode metricOrientationNode =
  metricOrientationAuthorityBlocker
blockerForFiniteMaxwellNode hodgeDualTwoFormNode =
  hodgeStarAuthorityBlocker
blockerForFiniteMaxwellNode exteriorDStarFNode =
  hodgeStarAuthorityBlocker
blockerForFiniteMaxwellNode sourceCurrentThreeFormNode =
  sourceExtractionProofBlocker
blockerForFiniteMaxwellNode inhomogeneousEquationNode =
  inhomogeneousEquationProofBlocker
blockerForFiniteMaxwellNode continuityDJZeroNode =
  sourceConservationProofBlocker
blockerForFiniteMaxwellNode divergenceJZeroNode =
  vectorDivergenceConventionProofBlocker
blockerForFiniteMaxwellNode unitCalibrationNode =
  unitCalibrationAuthorityBlocker
blockerForFiniteMaxwellNode empiricalObservableNode =
  empiricalObservableAuthorityBlocker
blockerForFiniteMaxwellNode maxwellPromotionGuardNode =
  maxwellPromotionGuardBlocker

nodeBlocksPromotion : FiniteMaxwellChainNode → Bool
nodeBlocksPromotion potentialOneFormNode = false
nodeBlocksPromotion curvatureTwoFormNode = false
nodeBlocksPromotion homogeneousBianchiNode = false
nodeBlocksPromotion metricOrientationNode = true
nodeBlocksPromotion hodgeDualTwoFormNode = true
nodeBlocksPromotion exteriorDStarFNode = true
nodeBlocksPromotion sourceCurrentThreeFormNode = true
nodeBlocksPromotion inhomogeneousEquationNode = true
nodeBlocksPromotion continuityDJZeroNode = true
nodeBlocksPromotion divergenceJZeroNode = true
nodeBlocksPromotion unitCalibrationNode = true
nodeBlocksPromotion empiricalObservableNode = true
nodeBlocksPromotion maxwellPromotionGuardNode = true

record FiniteMaxwellExteriorChainRow : Set where
  field
    node : FiniteMaxwellChainNode
    stage : FiniteMaxwellChainStage
    stageMatchesClassifier :
      stage ≡ classifyFiniteMaxwellNode node
    finiteCarrier : String
    equationOrAdapterTarget : String
    requiredReceipt : String
    selectedBlocker : FiniteMaxwellChainBlocker
    selectedBlockerMatches :
      selectedBlocker ≡ blockerForFiniteMaxwellNode node
    blocksMaxwellPromotion : Bool
    blocksMaxwellPromotionMatches :
      blocksMaxwellPromotion ≡ nodeBlocksPromotion node

open FiniteMaxwellExteriorChainRow public

potentialOneFormRow : FiniteMaxwellExteriorChainRow
potentialOneFormRow = record
  { node = potentialOneFormNode
  ; stage = constructedFiniteExteriorStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "A : finite symbolic one-form"
  ; equationOrAdapterTarget =
      Exterior.CanonicalCurvatureConstruction.curvatureDefinition
        Exterior.canonicalCurvatureConstruction
  ; requiredReceipt = "constructed by canonicalMaxwellExteriorCalculusAdapter"
  ; selectedBlocker = noBlockerConstructedHomogeneous
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = false
  ; blocksMaxwellPromotionMatches = refl
  }

curvatureTwoFormRow : FiniteMaxwellExteriorChainRow
curvatureTwoFormRow = record
  { node = curvatureTwoFormNode
  ; stage = constructedFiniteExteriorStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "F : finite symbolic two-form"
  ; equationOrAdapterTarget = "F = d A"
  ; requiredReceipt =
      Classical.MaxwellCurvatureObligation.curvatureConstruction
        Classical.canonicalMaxwellCurvatureObligation
  ; selectedBlocker = noBlockerConstructedHomogeneous
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = false
  ; blocksMaxwellPromotionMatches = refl
  }

homogeneousBianchiRow : FiniteMaxwellExteriorChainRow
homogeneousBianchiRow = record
  { node = homogeneousBianchiNode
  ; stage = constructedFiniteExteriorStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "d F : finite symbolic three-form"
  ; equationOrAdapterTarget =
      Exterior.CanonicalCurvatureConstruction.homogeneousEquationTarget
        Exterior.canonicalCurvatureConstruction
  ; requiredReceipt =
      Classical.MaxwellCurvatureObligation.bianchiIdentityTarget
        Classical.canonicalMaxwellCurvatureObligation
  ; selectedBlocker = noBlockerConstructedHomogeneous
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = false
  ; blocksMaxwellPromotionMatches = refl
  }

metricOrientationRow : FiniteMaxwellExteriorChainRow
metricOrientationRow = record
  { node = metricOrientationNode
  ; stage = authorityBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "metric, orientation, and volume convention"
  ; equationOrAdapterTarget = "select Lorentz metric/orientation for *"
  ; requiredReceipt =
      Classical.MaxwellHodgeObligation.metricCarrierRequired
        Classical.canonicalMaxwellHodgeObligation
  ; selectedBlocker = metricOrientationAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

hodgeDualTwoFormRow : FiniteMaxwellExteriorChainRow
hodgeDualTwoFormRow = record
  { node = hodgeDualTwoFormNode
  ; stage = authorityBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "*F : finite symbolic two-form"
  ; equationOrAdapterTarget =
      Classical.MaxwellHodgeObligation.hodgeStarOnTwoFormsRequired
        Classical.canonicalMaxwellHodgeObligation
  ; requiredReceipt =
      Exterior.HodgeSourceAuthorityBoundary.hodgeStarAuthorityRequired
        Exterior.canonicalHodgeSourceAuthorityBoundary
  ; selectedBlocker = hodgeStarAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

exteriorDStarFRow : FiniteMaxwellExteriorChainRow
exteriorDStarFRow = record
  { node = exteriorDStarFNode
  ; stage = proofBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "d * F : finite symbolic three-form"
  ; equationOrAdapterTarget = "d * F is the source-equation left side"
  ; requiredReceipt =
      "Hodge authority plus proof that Exterior.d2 (*F) is the selected left side"
  ; selectedBlocker = hodgeStarAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

sourceCurrentThreeFormRow : FiniteMaxwellExteriorChainRow
sourceCurrentThreeFormRow = record
  { node = sourceCurrentThreeFormNode
  ; stage = proofBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "J : finite symbolic source-current three-form"
  ; equationOrAdapterTarget =
      Classical.MaxwellSourceCurrentObligation.sourceExtractionReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; requiredReceipt =
      Exterior.HodgeSourceAuthorityBoundary.sourceCurrentAuthorityRequired
        Exterior.canonicalHodgeSourceAuthorityBoundary
  ; selectedBlocker = sourceExtractionProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

inhomogeneousEquationRow : FiniteMaxwellExteriorChainRow
inhomogeneousEquationRow = record
  { node = inhomogeneousEquationNode
  ; stage = proofBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "d * F and J comparison row"
  ; equationOrAdapterTarget =
      Classical.MaxwellFieldEquationPromotionObligation.inhomogeneousEquationTarget
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; requiredReceipt =
      "proof or accepted authority receipt identifying finite d * F with finite J"
  ; selectedBlocker = inhomogeneousEquationProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

continuityDJZeroRow : FiniteMaxwellExteriorChainRow
continuityDJZeroRow = record
  { node = continuityDJZeroNode
  ; stage = proofBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "d J : finite symbolic four-form"
  ; equationOrAdapterTarget =
      Classical.MaxwellSourceCurrentObligation.continuityEquationTarget
        Classical.canonicalMaxwellSourceCurrentObligation
  ; requiredReceipt =
      "proof that extracted finite current has zero exterior divergence"
  ; selectedBlocker = sourceConservationProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

divergenceJZeroRow : FiniteMaxwellExteriorChainRow
divergenceJZeroRow = record
  { node = divergenceJZeroNode
  ; stage = proofBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "div J / partial_mu J^mu convention row"
  ; equationOrAdapterTarget = "div J = 0 / partial_mu J^mu = 0"
  ; requiredReceipt =
      "proof that vector-current divergence convention agrees with d J = 0"
  ; selectedBlocker = vectorDivergenceConventionProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

unitCalibrationRow : FiniteMaxwellExteriorChainRow
unitCalibrationRow = record
  { node = unitCalibrationNode
  ; stage = calibrationBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "SI charge-current and epsilon_0/mu_0 calibration"
  ; equationOrAdapterTarget =
      Classical.MaxwellHodgeObligation.epsilon0Mu0AuthorityRequired
        Classical.canonicalMaxwellHodgeObligation
  ; requiredReceipt =
      Classical.MaxwellSourceCurrentObligation.chargeCalibrationReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; selectedBlocker = unitCalibrationAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

empiricalObservableRow : FiniteMaxwellExteriorChainRow
empiricalObservableRow = record
  { node = empiricalObservableNode
  ; stage = empiricalBoundaryStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "field/flux/source empirical observable adapter"
  ; equationOrAdapterTarget =
      Classical.MaxwellFieldEquationPromotionObligation.empiricalObservableAdapterRequired
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; requiredReceipt =
      "accepted provider, comparison law, covariance, and calibration receipt"
  ; selectedBlocker = empiricalObservableAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

maxwellPromotionGuardRow : FiniteMaxwellExteriorChainRow
maxwellPromotionGuardRow = record
  { node = maxwellPromotionGuardNode
  ; stage = promotionGuardClosedStage
  ; stageMatchesClassifier = refl
  ; finiteCarrier = "Maxwell field-equation promotion guard"
  ; equationOrAdapterTarget = "Maxwell field equations promoted"
  ; requiredReceipt =
      "all finite exterior-chain, Hodge, source, calibration, and empirical rows closed"
  ; selectedBlocker = maxwellPromotionGuardBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionMatches = refl
  }

canonicalFiniteMaxwellExteriorChainRows :
  List FiniteMaxwellExteriorChainRow
canonicalFiniteMaxwellExteriorChainRows =
  potentialOneFormRow
  ∷ curvatureTwoFormRow
  ∷ homogeneousBianchiRow
  ∷ metricOrientationRow
  ∷ hodgeDualTwoFormRow
  ∷ exteriorDStarFRow
  ∷ sourceCurrentThreeFormRow
  ∷ inhomogeneousEquationRow
  ∷ continuityDJZeroRow
  ∷ divergenceJZeroRow
  ∷ unitCalibrationRow
  ∷ empiricalObservableRow
  ∷ maxwellPromotionGuardRow
  ∷ []

canonicalFiniteConstructedRows : List FiniteMaxwellExteriorChainRow
canonicalFiniteConstructedRows =
  potentialOneFormRow
  ∷ curvatureTwoFormRow
  ∷ homogeneousBianchiRow
  ∷ []

canonicalFiniteAuthorityRows : List FiniteMaxwellExteriorChainRow
canonicalFiniteAuthorityRows =
  metricOrientationRow
  ∷ hodgeDualTwoFormRow
  ∷ []

canonicalFiniteProofRows : List FiniteMaxwellExteriorChainRow
canonicalFiniteProofRows =
  exteriorDStarFRow
  ∷ sourceCurrentThreeFormRow
  ∷ inhomogeneousEquationRow
  ∷ continuityDJZeroRow
  ∷ divergenceJZeroRow
  ∷ []

canonicalFiniteCalibrationRows : List FiniteMaxwellExteriorChainRow
canonicalFiniteCalibrationRows =
  unitCalibrationRow
  ∷ []

canonicalFiniteEmpiricalRows : List FiniteMaxwellExteriorChainRow
canonicalFiniteEmpiricalRows =
  empiricalObservableRow
  ∷ []

canonicalFinitePromotionFalseRows : List FiniteMaxwellExteriorChainRow
canonicalFinitePromotionFalseRows =
  maxwellPromotionGuardRow
  ∷ []

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

record MaxwellFiniteExteriorChainStrengthening : Set₁ where
  field
    sourceExteriorAdapter :
      Exterior.MaxwellExteriorCalculusAdapter
    sourceCalibration :
      Calibration.MaxwellHodgeSourceCalibration
    sourceConservationClosure :
      Conservation.MaxwellHodgeSourceConservationClosure
    potential : Exterior.OneForm
    curvature : Exterior.TwoForm
    homogeneousDField : Exterior.ThreeForm
    hodgeDual : Exterior.TwoForm
    dHodgeDual : Exterior.ThreeForm
    sourceCurrent : Exterior.ThreeForm
    dSourceCurrent : Exterior.FourForm
    potentialIsCanonical :
      potential ≡ Exterior.canonicalPotentialOneForm
    curvatureIsDOfPotential :
      curvature ≡ Exterior.d1 potential
    homogeneousDFieldIsZero :
      homogeneousDField ≡ Exterior.zeroThreeForm
    hodgeDualIsSymbolicStar :
      hodgeDual ≡ Exterior.hodge2Symbolic curvature
    dHodgeDualIsAdapterBoundary :
      dHodgeDual ≡
      Exterior.HodgeSourceAuthorityBoundary.symbolicDStarF
        Exterior.canonicalHodgeSourceAuthorityBoundary
    sourceCurrentIsCanonical :
      sourceCurrent ≡ Exterior.sourceCurrentThreeForm
    dSourceCurrentIsD3OfSourceCurrent :
      dSourceCurrent ≡ Exterior.d3 sourceCurrent
    rows : List FiniteMaxwellExteriorChainRow
    constructedRows : List FiniteMaxwellExteriorChainRow
    authorityRows : List FiniteMaxwellExteriorChainRow
    proofRows : List FiniteMaxwellExteriorChainRow
    calibrationRows : List FiniteMaxwellExteriorChainRow
    empiricalRows : List FiniteMaxwellExteriorChainRow
    promotionFalseRows : List FiniteMaxwellExteriorChainRow
    totalRowCount : Nat
    totalRowCountMatches :
      totalRowCount ≡ listLength rows
    constructedRowCount : Nat
    constructedRowCountMatches :
      constructedRowCount ≡ listLength constructedRows
    authorityRowCount : Nat
    authorityRowCountMatches :
      authorityRowCount ≡ listLength authorityRows
    proofRowCount : Nat
    proofRowCountMatches :
      proofRowCount ≡ listLength proofRows
    calibrationRowCount : Nat
    calibrationRowCountMatches :
      calibrationRowCount ≡ listLength calibrationRows
    empiricalRowCount : Nat
    empiricalRowCountMatches :
      empiricalRowCount ≡ listLength empiricalRows
    promotionFalseRowCount : Nat
    promotionFalseRowCountMatches :
      promotionFalseRowCount ≡ listLength promotionFalseRows
    consumedConservationRowCount : Nat
    consumedConservationRowCountIs10 :
      consumedConservationRowCount ≡ 10
    consumedCalibrationInputCount : Nat
    consumedCalibrationInputCountIs6 :
      consumedCalibrationInputCount ≡ 6
    consumedExteriorConstructedEquationCount : Nat
    consumedExteriorConstructedEquationCountIs1 :
      consumedExteriorConstructedEquationCount ≡ 1
    dFZeroConstructed : Bool
    dFZeroConstructedIsTrue :
      dFZeroConstructed ≡ true
    dStarFEqualsJPromoted : Bool
    dStarFEqualsJPromotedIsFalse :
      dStarFEqualsJPromoted ≡ false
    dJZeroPromoted : Bool
    dJZeroPromotedIsFalse :
      dJZeroPromoted ≡ false
    divJZeroPromoted : Bool
    divJZeroPromotedIsFalse :
      divJZeroPromoted ≡ false
    hodgeMetricPromoted : Bool
    hodgeMetricPromotedIsFalse :
      hodgeMetricPromoted ≡ false
    sourceExtractionPromoted : Bool
    sourceExtractionPromotedIsFalse :
      sourceExtractionPromoted ≡ false
    maxwellFieldEquationPromoted : Bool
    maxwellFieldEquationPromotedIsFalse :
      maxwellFieldEquationPromoted ≡ false

open MaxwellFiniteExteriorChainStrengthening public

canonicalMaxwellFiniteExteriorChainStrengthening :
  MaxwellFiniteExteriorChainStrengthening
canonicalMaxwellFiniteExteriorChainStrengthening = record
  { sourceExteriorAdapter =
      Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; sourceCalibration =
      Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceConservationClosure =
      Conservation.canonicalMaxwellHodgeSourceConservationClosure
  ; potential =
      Exterior.canonicalPotentialOneForm
  ; curvature =
      Exterior.canonicalCurvatureTwoForm
  ; homogeneousDField =
      Exterior.d2 Exterior.canonicalCurvatureTwoForm
  ; hodgeDual =
      Exterior.hodge2Symbolic Exterior.canonicalCurvatureTwoForm
  ; dHodgeDual =
      Exterior.d2
        (Exterior.hodge2Symbolic Exterior.canonicalCurvatureTwoForm)
  ; sourceCurrent =
      Exterior.sourceCurrentThreeForm
  ; dSourceCurrent =
      Exterior.d3 Exterior.sourceCurrentThreeForm
  ; potentialIsCanonical =
      refl
  ; curvatureIsDOfPotential =
      refl
  ; homogeneousDFieldIsZero =
      refl
  ; hodgeDualIsSymbolicStar =
      refl
  ; dHodgeDualIsAdapterBoundary =
      refl
  ; sourceCurrentIsCanonical =
      refl
  ; dSourceCurrentIsD3OfSourceCurrent =
      refl
  ; rows =
      canonicalFiniteMaxwellExteriorChainRows
  ; constructedRows =
      canonicalFiniteConstructedRows
  ; authorityRows =
      canonicalFiniteAuthorityRows
  ; proofRows =
      canonicalFiniteProofRows
  ; calibrationRows =
      canonicalFiniteCalibrationRows
  ; empiricalRows =
      canonicalFiniteEmpiricalRows
  ; promotionFalseRows =
      canonicalFinitePromotionFalseRows
  ; totalRowCount =
      13
  ; totalRowCountMatches =
      refl
  ; constructedRowCount =
      3
  ; constructedRowCountMatches =
      refl
  ; authorityRowCount =
      2
  ; authorityRowCountMatches =
      refl
  ; proofRowCount =
      5
  ; proofRowCountMatches =
      refl
  ; calibrationRowCount =
      1
  ; calibrationRowCountMatches =
      refl
  ; empiricalRowCount =
      1
  ; empiricalRowCountMatches =
      refl
  ; promotionFalseRowCount =
      1
  ; promotionFalseRowCountMatches =
      refl
  ; consumedConservationRowCount =
      Conservation.MaxwellHodgeSourceConservationClosure.totalObligationCount
        Conservation.canonicalMaxwellHodgeSourceConservationClosure
  ; consumedConservationRowCountIs10 =
      refl
  ; consumedCalibrationInputCount =
      Calibration.MaxwellHodgeSourceCalibration.totalCalibrationInputCount
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; consumedCalibrationInputCountIs6 =
      refl
  ; consumedExteriorConstructedEquationCount =
      Exterior.MaxwellExteriorCalculusAdapter.constructedEquationCount
        Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; consumedExteriorConstructedEquationCountIs1 =
      refl
  ; dFZeroConstructed =
      true
  ; dFZeroConstructedIsTrue =
      refl
  ; dStarFEqualsJPromoted =
      false
  ; dStarFEqualsJPromotedIsFalse =
      refl
  ; dJZeroPromoted =
      false
  ; dJZeroPromotedIsFalse =
      refl
  ; divJZeroPromoted =
      false
  ; divJZeroPromotedIsFalse =
      refl
  ; hodgeMetricPromoted =
      Calibration.MaxwellHodgeSourceCalibration.hodgePromotion
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; hodgeMetricPromotedIsFalse =
      Calibration.MaxwellHodgeSourceCalibration.hodgePromotionIsFalse
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceExtractionPromoted =
      Calibration.MaxwellHodgeSourceCalibration.sourceCurrentPromotion
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceExtractionPromotedIsFalse =
      Calibration.MaxwellHodgeSourceCalibration.sourceCurrentPromotionIsFalse
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; maxwellFieldEquationPromoted =
      Classical.MaxwellFieldEquationPromotionObligation.maxwellFieldEquationPromoted
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; maxwellFieldEquationPromotedIsFalse =
      Classical.MaxwellFieldEquationPromotionObligation.maxwellFieldEquationPromotedProof
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  }

canonicalFiniteMaxwellExteriorChainRowCountIs13 :
  MaxwellFiniteExteriorChainStrengthening.totalRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 13
canonicalFiniteMaxwellExteriorChainRowCountIs13 = refl

canonicalFiniteMaxwellConstructedRowCountIs3 :
  MaxwellFiniteExteriorChainStrengthening.constructedRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 3
canonicalFiniteMaxwellConstructedRowCountIs3 = refl

canonicalFiniteMaxwellAuthorityRowCountIs2 :
  MaxwellFiniteExteriorChainStrengthening.authorityRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 2
canonicalFiniteMaxwellAuthorityRowCountIs2 = refl

canonicalFiniteMaxwellProofRowCountIs5 :
  MaxwellFiniteExteriorChainStrengthening.proofRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 5
canonicalFiniteMaxwellProofRowCountIs5 = refl

canonicalFiniteMaxwellCalibrationRowCountIs1 :
  MaxwellFiniteExteriorChainStrengthening.calibrationRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 1
canonicalFiniteMaxwellCalibrationRowCountIs1 = refl

canonicalFiniteMaxwellEmpiricalRowCountIs1 :
  MaxwellFiniteExteriorChainStrengthening.empiricalRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 1
canonicalFiniteMaxwellEmpiricalRowCountIs1 = refl

canonicalFiniteMaxwellPromotionFalseRowCountIs1 :
  MaxwellFiniteExteriorChainStrengthening.promotionFalseRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 1
canonicalFiniteMaxwellPromotionFalseRowCountIs1 = refl

canonicalFiniteMaxwellConsumesConservationCount10 :
  MaxwellFiniteExteriorChainStrengthening.consumedConservationRowCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 10
canonicalFiniteMaxwellConsumesConservationCount10 = refl

canonicalFiniteMaxwellConsumesCalibrationCount6 :
  MaxwellFiniteExteriorChainStrengthening.consumedCalibrationInputCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 6
canonicalFiniteMaxwellConsumesCalibrationCount6 = refl

canonicalFiniteMaxwellConsumesExteriorConstructedCount1 :
  MaxwellFiniteExteriorChainStrengthening.consumedExteriorConstructedEquationCount
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ 1
canonicalFiniteMaxwellConsumesExteriorConstructedCount1 = refl

canonicalFiniteMaxwellCurvatureIsDOfPotential :
  MaxwellFiniteExteriorChainStrengthening.curvature
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡
  Exterior.d1
    (MaxwellFiniteExteriorChainStrengthening.potential
      canonicalMaxwellFiniteExteriorChainStrengthening)
canonicalFiniteMaxwellCurvatureIsDOfPotential = refl

canonicalFiniteMaxwellDFIsZero :
  MaxwellFiniteExteriorChainStrengthening.homogeneousDField
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ Exterior.zeroThreeForm
canonicalFiniteMaxwellDFIsZero = refl

canonicalFiniteMaxwellDStarFIsUnverified :
  MaxwellFiniteExteriorChainStrengthening.dHodgeDual
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ Exterior.unverifiedDStarFThreeForm
canonicalFiniteMaxwellDStarFIsUnverified = refl

canonicalFiniteMaxwellDSourceCurrentIsContinuityForm :
  MaxwellFiniteExteriorChainStrengthening.dSourceCurrent
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ Exterior.continuityFourForm
canonicalFiniteMaxwellDSourceCurrentIsContinuityForm = refl

canonicalFiniteMaxwellDStarFEqualsJPromotionFalse :
  MaxwellFiniteExteriorChainStrengthening.dStarFEqualsJPromoted
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ false
canonicalFiniteMaxwellDStarFEqualsJPromotionFalse = refl

canonicalFiniteMaxwellDJZeroPromotionFalse :
  MaxwellFiniteExteriorChainStrengthening.dJZeroPromoted
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ false
canonicalFiniteMaxwellDJZeroPromotionFalse = refl

canonicalFiniteMaxwellDivJZeroPromotionFalse :
  MaxwellFiniteExteriorChainStrengthening.divJZeroPromoted
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ false
canonicalFiniteMaxwellDivJZeroPromotionFalse = refl

canonicalFiniteMaxwellFieldEquationPromotionFalse :
  MaxwellFiniteExteriorChainStrengthening.maxwellFieldEquationPromoted
    canonicalMaxwellFiniteExteriorChainStrengthening
  ≡ false
canonicalFiniteMaxwellFieldEquationPromotionFalse = refl
