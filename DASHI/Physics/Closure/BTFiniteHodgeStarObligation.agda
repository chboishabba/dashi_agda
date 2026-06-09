module DASHI.Physics.Closure.BTFiniteHodgeStarObligation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMStrictSelectedHodgeAlgebraLaws as YMHodge
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Exterior
import DASHI.Promotion.MaxwellFiniteExteriorChainStrengthening as Chain
import DASHI.Promotion.MaxwellHodgeSourceConservationObligations as Conservation

------------------------------------------------------------------------
-- BT finite Hodge-star obligation surface.
--
-- This is a non-promoting theorem-target receipt for the proposed
-- BTFiniteHodgeStar lane.  It packages the finite-depth BT-building/cell
-- complex target against the existing Maxwell exterior-chain and Hodge/source
-- blockers, plus the already-calculated selected finite YM Hodge algebra.
--
-- The constructed content remains symbolic/selected-finite only.  A genuine
-- metric Hodge star on weighted primal/dual BT cells, star-square law,
-- pairing, integration by parts, d * F = J, and d J = 0 are named as exact
-- obligations.  No Maxwell, Yang-Mills, Clay, or terminal promotion follows.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data BTFiniteHodgeStage : Set where
  substrateTargetStage : BTFiniteHodgeStage
  metricHodgeTargetStage : BTFiniteHodgeStage
  pairingVariationTargetStage : BTFiniteHodgeStage
  sourceEquationTargetStage : BTFiniteHodgeStage
  conservationTargetStage : BTFiniteHodgeStage
  empiricalPromotionGuardStage : BTFiniteHodgeStage

data BTFiniteHodgeRowName : Set where
  finiteDepthBTCellComplexRow : BTFiniteHodgeRowName
  weightedPrimalCellsRow : BTFiniteHodgeRowName
  weightedDualCellsRow : BTFiniteHodgeRowName
  discreteHodgeStarRow : BTFiniteHodgeRowName
  hodgeStarSquareLawRow : BTFiniteHodgeRowName
  hodgePairingRow : BTFiniteHodgeRowName
  finiteIntegrationByPartsRow : BTFiniteHodgeRowName
  inhomogeneousDStarFEqualsJRow : BTFiniteHodgeRowName
  sourceConservationDJZeroRow : BTFiniteHodgeRowName
  empiricalObservableBoundaryRow : BTFiniteHodgeRowName
  maxwellPromotionGuardRow : BTFiniteHodgeRowName

data BTFiniteHodgeBlocker : Set where
  finiteBTBuildingCarrierMissing : BTFiniteHodgeBlocker
  weightedPrimalDualMetricMissing : BTFiniteHodgeBlocker
  discreteHodgeStarConstructionMissing : BTFiniteHodgeBlocker
  hodgeStarSquareProofMissing : BTFiniteHodgeBlocker
  hodgePairingConstructionMissing : BTFiniteHodgeBlocker
  finiteIntegrationByPartsProofMissing : BTFiniteHodgeBlocker
  dStarFEqualsJProofMissing : BTFiniteHodgeBlocker
  sourceConservationProofMissing : BTFiniteHodgeBlocker
  empiricalObservableAuthorityMissing : BTFiniteHodgeBlocker
  maxwellPromotionGuardClosed : BTFiniteHodgeBlocker

stageForRow : BTFiniteHodgeRowName → BTFiniteHodgeStage
stageForRow finiteDepthBTCellComplexRow =
  substrateTargetStage
stageForRow weightedPrimalCellsRow =
  substrateTargetStage
stageForRow weightedDualCellsRow =
  substrateTargetStage
stageForRow discreteHodgeStarRow =
  metricHodgeTargetStage
stageForRow hodgeStarSquareLawRow =
  metricHodgeTargetStage
stageForRow hodgePairingRow =
  pairingVariationTargetStage
stageForRow finiteIntegrationByPartsRow =
  pairingVariationTargetStage
stageForRow inhomogeneousDStarFEqualsJRow =
  sourceEquationTargetStage
stageForRow sourceConservationDJZeroRow =
  conservationTargetStage
stageForRow empiricalObservableBoundaryRow =
  empiricalPromotionGuardStage
stageForRow maxwellPromotionGuardRow =
  empiricalPromotionGuardStage

blockerForRow : BTFiniteHodgeRowName → BTFiniteHodgeBlocker
blockerForRow finiteDepthBTCellComplexRow =
  finiteBTBuildingCarrierMissing
blockerForRow weightedPrimalCellsRow =
  weightedPrimalDualMetricMissing
blockerForRow weightedDualCellsRow =
  weightedPrimalDualMetricMissing
blockerForRow discreteHodgeStarRow =
  discreteHodgeStarConstructionMissing
blockerForRow hodgeStarSquareLawRow =
  hodgeStarSquareProofMissing
blockerForRow hodgePairingRow =
  hodgePairingConstructionMissing
blockerForRow finiteIntegrationByPartsRow =
  finiteIntegrationByPartsProofMissing
blockerForRow inhomogeneousDStarFEqualsJRow =
  dStarFEqualsJProofMissing
blockerForRow sourceConservationDJZeroRow =
  sourceConservationProofMissing
blockerForRow empiricalObservableBoundaryRow =
  empiricalObservableAuthorityMissing
blockerForRow maxwellPromotionGuardRow =
  maxwellPromotionGuardClosed

data BTDepthIndex : Set where
  finiteDepthBTBuildingDepth : BTDepthIndex

data BTCellComplexCarrier : Set where
  finiteDepthBTBuildingCellComplex : BTCellComplexCarrier

data BTPrimalCellCarrier : Set where
  weightedBTPrimalCell : BTPrimalCellCarrier

data BTDualCellCarrier : Set where
  weightedBTDualCell : BTDualCellCarrier

data BTCellWeight : Set where
  selectedPositiveCellWeight : BTCellWeight

data BTFinitePairingCarrier : Set where
  btFinitePairingTarget :
    Exterior.TwoForm →
    Exterior.TwoForm →
    BTFinitePairingCarrier

data BTFiniteIBPTarget : Set where
  btFiniteIBPTarget :
    Exterior.OneForm →
    Exterior.TwoForm →
    Exterior.ThreeForm →
    BTFiniteIBPTarget

btSymbolicHodgeStar : Exterior.TwoForm → Exterior.TwoForm
btSymbolicHodgeStar =
  Exterior.hodge2Symbolic

btSymbolicDStarF : Exterior.TwoForm → Exterior.ThreeForm
btSymbolicDStarF twoForm =
  Exterior.d2 (btSymbolicHodgeStar twoForm)

btSymbolicSourceCurrent : Exterior.ThreeForm
btSymbolicSourceCurrent =
  Exterior.sourceCurrentThreeForm

btSymbolicDCurrent : Exterior.FourForm
btSymbolicDCurrent =
  Exterior.d3 btSymbolicSourceCurrent

record BTFiniteHodgeStarObligationRow : Set where
  field
    rowName : BTFiniteHodgeRowName
    stage : BTFiniteHodgeStage
    stageMatchesClassifier :
      stage ≡ stageForRow rowName
    targetStatement : String
    consumedMaxwellSurface : String
    requiredReceipt : String
    selectedBlocker : BTFiniteHodgeBlocker
    selectedBlockerMatches :
      selectedBlocker ≡ blockerForRow rowName
    blocksPromotion : Bool
    blocksPromotionIsTrue :
      blocksPromotion ≡ true

open BTFiniteHodgeStarObligationRow public

mkBTFiniteHodgeRow :
  (rowName : BTFiniteHodgeRowName) →
  String →
  String →
  String →
  BTFiniteHodgeStarObligationRow
mkBTFiniteHodgeRow rowName target consumed required =
  record
    { rowName = rowName
    ; stage = stageForRow rowName
    ; stageMatchesClassifier = refl
    ; targetStatement = target
    ; consumedMaxwellSurface = consumed
    ; requiredReceipt = required
    ; selectedBlocker = blockerForRow rowName
    ; selectedBlockerMatches = refl
    ; blocksPromotion = true
    ; blocksPromotionIsTrue = refl
    }

finiteDepthBTCellComplexObligationRow :
  BTFiniteHodgeStarObligationRow
finiteDepthBTCellComplexObligationRow =
  mkBTFiniteHodgeRow
    finiteDepthBTCellComplexRow
    "finite-depth Bruhat-Tits building/cell complex K_d"
    "Maxwell exterior form inventory supplies degrees 0..4, not K_d"
    "construct finite clopen BT-building carrier with boundary shell depth"

weightedPrimalCellsObligationRow :
  BTFiniteHodgeStarObligationRow
weightedPrimalCellsObligationRow =
  mkBTFiniteHodgeRow
    weightedPrimalCellsRow
    "weighted primal cells for C^k(K_d)"
    "Maxwell finite exterior chain names metric/orientation authority"
    "supply positive cell-volume weights and orientation convention"

weightedDualCellsObligationRow :
  BTFiniteHodgeStarObligationRow
weightedDualCellsObligationRow =
  mkBTFiniteHodgeRow
    weightedDualCellsRow
    "weighted dual cells for C^{n-k}(K_d^vee)"
    "Maxwell finite exterior chain names Hodge dual two-form boundary"
    "supply dual-cell incidence and reciprocal volume weights"

discreteHodgeStarObligationRow :
  BTFiniteHodgeStarObligationRow
discreteHodgeStarObligationRow =
  mkBTFiniteHodgeRow
    discreteHodgeStarRow
    "* : C^k(K_d) -> C^{n-k}(K_d^vee)"
    "symbolic hodge2Symbolic exists; selected YM lower Hodge algebra exists"
    "construct metric Hodge star from weighted primal/dual BT cells"

hodgeStarSquareLawObligationRow :
  BTFiniteHodgeStarObligationRow
hodgeStarSquareLawObligationRow =
  mkBTFiniteHodgeRow
    hodgeStarSquareLawRow
    "** = +/- 1 with degree/sign convention"
    "selected YM identity/square law exists only for finite lower probe"
    "prove star-square law for BT metric Hodge star"

hodgePairingObligationRow :
  BTFiniteHodgeStarObligationRow
hodgePairingObligationRow =
  mkBTFiniteHodgeRow
    hodgePairingRow
    "<alpha,beta> = integral alpha wedge * beta"
    "Maxwell conservation closure records Hodge/source obligations"
    "construct weighted finite pairing compatible with Hodge star"

finiteIntegrationByPartsObligationRow :
  BTFiniteHodgeStarObligationRow
finiteIntegrationByPartsObligationRow =
  mkBTFiniteHodgeRow
    finiteIntegrationByPartsRow
    "finite IBP / adjointness of d and d* with boundary term"
    "Maxwell finite exterior chain records d*F proof boundary"
    "prove discrete summation-by-parts on finite BT complex"

inhomogeneousDStarFEqualsJObligationRow :
  BTFiniteHodgeStarObligationRow
inhomogeneousDStarFEqualsJObligationRow =
  mkBTFiniteHodgeRow
    inhomogeneousDStarFEqualsJRow
    "d * F = J"
    "Maxwell Hodge/source closure keeps inhomogeneous equation false"
    "identify finite d*F with extracted source-current J"

sourceConservationDJZeroObligationRow :
  BTFiniteHodgeStarObligationRow
sourceConservationDJZeroObligationRow =
  mkBTFiniteHodgeRow
    sourceConservationDJZeroRow
    "d J = 0 follows from d^2 = 0 after J = d * F"
    "Maxwell conservation closure keeps dJ/divJ proof blocked"
    "prove current conservation for the selected finite current convention"

empiricalObservableBoundaryObligationRow :
  BTFiniteHodgeStarObligationRow
empiricalObservableBoundaryObligationRow =
  mkBTFiniteHodgeRow
    empiricalObservableBoundaryRow
    "BT finite Hodge field/source observable map"
    "Maxwell chain requires empirical observable authority"
    "bind observable to authority/covariance/calibration receipt"

maxwellPromotionGuardObligationRow :
  BTFiniteHodgeStarObligationRow
maxwellPromotionGuardObligationRow =
  mkBTFiniteHodgeRow
    maxwellPromotionGuardRow
    "Maxwell field-equation promotion remains false"
    "canonical Maxwell promotion guard is still blocked"
    "close all BT Hodge, source, conservation, calibration, and empirical rows"

canonicalBTFiniteHodgeStarRows :
  List BTFiniteHodgeStarObligationRow
canonicalBTFiniteHodgeStarRows =
  finiteDepthBTCellComplexObligationRow
  ∷ weightedPrimalCellsObligationRow
  ∷ weightedDualCellsObligationRow
  ∷ discreteHodgeStarObligationRow
  ∷ hodgeStarSquareLawObligationRow
  ∷ hodgePairingObligationRow
  ∷ finiteIntegrationByPartsObligationRow
  ∷ inhomogeneousDStarFEqualsJObligationRow
  ∷ sourceConservationDJZeroObligationRow
  ∷ empiricalObservableBoundaryObligationRow
  ∷ maxwellPromotionGuardObligationRow
  ∷ []

canonicalBTFiniteHodgeExactBlockers :
  List BTFiniteHodgeBlocker
canonicalBTFiniteHodgeExactBlockers =
  finiteBTBuildingCarrierMissing
  ∷ weightedPrimalDualMetricMissing
  ∷ discreteHodgeStarConstructionMissing
  ∷ hodgeStarSquareProofMissing
  ∷ hodgePairingConstructionMissing
  ∷ finiteIntegrationByPartsProofMissing
  ∷ dStarFEqualsJProofMissing
  ∷ sourceConservationProofMissing
  ∷ empiricalObservableAuthorityMissing
  ∷ maxwellPromotionGuardClosed
  ∷ []

record BTFiniteHodgeStarObligation : Set₁ where
  field
    sourceMaxwellExteriorCalculusAdapter :
      Exterior.MaxwellExteriorCalculusAdapter
    sourceMaxwellFiniteExteriorChain :
      Chain.MaxwellFiniteExteriorChainStrengthening
    sourceMaxwellHodgeSourceConservationClosure :
      Conservation.MaxwellHodgeSourceConservationClosure
    sourceYMSelectedHodgeAlgebra :
      YMHodge.StrictSelectedHodgeAlgebraLaws

    btDepth : BTDepthIndex
    btCellComplex : BTCellComplexCarrier
    selectedPrimalCell : BTPrimalCellCarrier
    selectedDualCell : BTDualCellCarrier
    selectedCellWeight : BTCellWeight

    symbolicCurvature :
      Exterior.TwoForm
    symbolicCurvatureIsCanonical :
      symbolicCurvature ≡ Exterior.canonicalCurvatureTwoForm

    symbolicHodgeStar :
      Exterior.TwoForm → Exterior.TwoForm
    symbolicHodgeStarIsAdapterHodge :
      symbolicHodgeStar ≡ Exterior.hodge2Symbolic

    symbolicStarF :
      Exterior.TwoForm
    symbolicStarFIsHodgeOfCurvature :
      symbolicStarF ≡ symbolicHodgeStar symbolicCurvature

    symbolicDStarF :
      Exterior.ThreeForm
    symbolicDStarFIsExteriorDOfStarF :
      symbolicDStarF ≡ Exterior.d2 symbolicStarF

    symbolicSourceCurrent :
      Exterior.ThreeForm
    symbolicSourceCurrentIsCanonical :
      symbolicSourceCurrent ≡ Exterior.sourceCurrentThreeForm

    symbolicDSourceCurrent :
      Exterior.FourForm
    symbolicDSourceCurrentIsD3 :
      symbolicDSourceCurrent ≡ Exterior.d3 symbolicSourceCurrent

    finitePairingTarget :
      BTFinitePairingCarrier
    finiteIBPTarget :
      BTFiniteIBPTarget

    rows :
      List BTFiniteHodgeStarObligationRow
    rowsAreCanonical :
      rows ≡ canonicalBTFiniteHodgeStarRows
    rowCount :
      Nat
    rowCountIs11 :
      rowCount ≡ 11

    exactBlockers :
      List BTFiniteHodgeBlocker
    exactBlockersAreCanonical :
      exactBlockers ≡ canonicalBTFiniteHodgeExactBlockers
    exactBlockerCount :
      Nat
    exactBlockerCountIs10 :
      exactBlockerCount ≡ 10

    consumedMaxwellExteriorConstructedEquationCount :
      Nat
    consumedMaxwellExteriorConstructedEquationCountIs1 :
      consumedMaxwellExteriorConstructedEquationCount ≡ 1

    consumedMaxwellConservationObligationCount :
      Nat
    consumedMaxwellConservationObligationCountIs10 :
      consumedMaxwellConservationObligationCount ≡ 10

    consumedSelectedYMHodgeAlgebraRowCount :
      Nat
    consumedSelectedYMHodgeAlgebraRowCountIs8 :
      consumedSelectedYMHodgeAlgebraRowCount ≡ 8

    finiteExteriorDerivativeAvailable :
      Bool
    finiteExteriorDerivativeAvailableIsTrue :
      finiteExteriorDerivativeAvailable ≡ true

    selectedFiniteYMHodgeProbeAvailable :
      Bool
    selectedFiniteYMHodgeProbeAvailableIsTrue :
      selectedFiniteYMHodgeProbeAvailable ≡ true

    btMetricHodgeStarPromoted :
      Bool
    btMetricHodgeStarPromotedIsFalse :
      btMetricHodgeStarPromoted ≡ false

    hodgeStarSquareLawPromoted :
      Bool
    hodgeStarSquareLawPromotedIsFalse :
      hodgeStarSquareLawPromoted ≡ false

    finitePairingPromoted :
      Bool
    finitePairingPromotedIsFalse :
      finitePairingPromoted ≡ false

    finiteIBPPromoted :
      Bool
    finiteIBPPromotedIsFalse :
      finiteIBPPromoted ≡ false

    dStarFEqualsJPromoted :
      Bool
    dStarFEqualsJPromotedIsFalse :
      dStarFEqualsJPromoted ≡ false

    dJZeroPromoted :
      Bool
    dJZeroPromotedIsFalse :
      dJZeroPromoted ≡ false

    maxwellFieldEquationPromoted :
      Bool
    maxwellFieldEquationPromotedIsFalse :
      maxwellFieldEquationPromoted ≡ false

    yangMillsPromoted :
      Bool
    yangMillsPromotedIsFalse :
      yangMillsPromoted ≡ false

    terminalPromotion :
      Bool
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    obligationBoundary :
      List String

open BTFiniteHodgeStarObligation public

canonicalBTFiniteHodgeStarObligation :
  BTFiniteHodgeStarObligation
canonicalBTFiniteHodgeStarObligation =
  record
    { sourceMaxwellExteriorCalculusAdapter =
        Exterior.canonicalMaxwellExteriorCalculusAdapter
    ; sourceMaxwellFiniteExteriorChain =
        Chain.canonicalMaxwellFiniteExteriorChainStrengthening
    ; sourceMaxwellHodgeSourceConservationClosure =
        Conservation.canonicalMaxwellHodgeSourceConservationClosure
    ; sourceYMSelectedHodgeAlgebra =
        YMHodge.canonicalStrictSelectedHodgeAlgebraLaws
    ; btDepth =
        finiteDepthBTBuildingDepth
    ; btCellComplex =
        finiteDepthBTBuildingCellComplex
    ; selectedPrimalCell =
        weightedBTPrimalCell
    ; selectedDualCell =
        weightedBTDualCell
    ; selectedCellWeight =
        selectedPositiveCellWeight
    ; symbolicCurvature =
        Exterior.canonicalCurvatureTwoForm
    ; symbolicCurvatureIsCanonical =
        refl
    ; symbolicHodgeStar =
        btSymbolicHodgeStar
    ; symbolicHodgeStarIsAdapterHodge =
        refl
    ; symbolicStarF =
        btSymbolicHodgeStar Exterior.canonicalCurvatureTwoForm
    ; symbolicStarFIsHodgeOfCurvature =
        refl
    ; symbolicDStarF =
        btSymbolicDStarF Exterior.canonicalCurvatureTwoForm
    ; symbolicDStarFIsExteriorDOfStarF =
        refl
    ; symbolicSourceCurrent =
        btSymbolicSourceCurrent
    ; symbolicSourceCurrentIsCanonical =
        refl
    ; symbolicDSourceCurrent =
        btSymbolicDCurrent
    ; symbolicDSourceCurrentIsD3 =
        refl
    ; finitePairingTarget =
        btFinitePairingTarget
          Exterior.canonicalCurvatureTwoForm
          (btSymbolicHodgeStar Exterior.canonicalCurvatureTwoForm)
    ; finiteIBPTarget =
        btFiniteIBPTarget
          Exterior.canonicalPotentialOneForm
          Exterior.canonicalCurvatureTwoForm
          (btSymbolicDStarF Exterior.canonicalCurvatureTwoForm)
    ; rows =
        canonicalBTFiniteHodgeStarRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        11
    ; rowCountIs11 =
        refl
    ; exactBlockers =
        canonicalBTFiniteHodgeExactBlockers
    ; exactBlockersAreCanonical =
        refl
    ; exactBlockerCount =
        10
    ; exactBlockerCountIs10 =
        refl
    ; consumedMaxwellExteriorConstructedEquationCount =
        Exterior.MaxwellExteriorCalculusAdapter.constructedEquationCount
          Exterior.canonicalMaxwellExteriorCalculusAdapter
    ; consumedMaxwellExteriorConstructedEquationCountIs1 =
        refl
    ; consumedMaxwellConservationObligationCount =
        Conservation.MaxwellHodgeSourceConservationClosure.totalObligationCount
          Conservation.canonicalMaxwellHodgeSourceConservationClosure
    ; consumedMaxwellConservationObligationCountIs10 =
        refl
    ; consumedSelectedYMHodgeAlgebraRowCount =
        YMHodge.StrictSelectedHodgeAlgebraLaws.rowCount
          YMHodge.canonicalStrictSelectedHodgeAlgebraLaws
    ; consumedSelectedYMHodgeAlgebraRowCountIs8 =
        refl
    ; finiteExteriorDerivativeAvailable =
        true
    ; finiteExteriorDerivativeAvailableIsTrue =
        refl
    ; selectedFiniteYMHodgeProbeAvailable =
        YMHodge.StrictSelectedHodgeAlgebraLaws.selectedFiniteAlgebraCalculated
          YMHodge.canonicalStrictSelectedHodgeAlgebraLaws
    ; selectedFiniteYMHodgeProbeAvailableIsTrue =
        refl
    ; btMetricHodgeStarPromoted =
        false
    ; btMetricHodgeStarPromotedIsFalse =
        refl
    ; hodgeStarSquareLawPromoted =
        false
    ; hodgeStarSquareLawPromotedIsFalse =
        refl
    ; finitePairingPromoted =
        false
    ; finitePairingPromotedIsFalse =
        refl
    ; finiteIBPPromoted =
        false
    ; finiteIBPPromotedIsFalse =
        refl
    ; dStarFEqualsJPromoted =
        false
    ; dStarFEqualsJPromotedIsFalse =
        refl
    ; dJZeroPromoted =
        false
    ; dJZeroPromotedIsFalse =
        refl
    ; maxwellFieldEquationPromoted =
        false
    ; maxwellFieldEquationPromotedIsFalse =
        refl
    ; yangMillsPromoted =
        false
    ; yangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; obligationBoundary =
        "BTFiniteHodgeStar is a finite-depth clopen/BT-building theorem target, not a Maxwell promotion"
        ∷ "Existing Maxwell exterior calculus supplies symbolic forms and dF = 0 only"
        ∷ "Existing Maxwell Hodge/source closure records metric, source, d*F=J, dJ=0, calibration, and empirical blockers"
        ∷ "Existing selected YM Hodge algebra supplies an identity lower probe and selected current law, not a metric Hodge star"
        ∷ "Promotion requires weighted primal/dual cells, Hodge star, ** law, pairing, IBP, d*F=J, dJ=0, and empirical authority"
        ∷ []
    }

canonicalBTFiniteHodgeStarRowCountIs11 :
  listLength canonicalBTFiniteHodgeStarRows ≡ 11
canonicalBTFiniteHodgeStarRowCountIs11 =
  refl

canonicalBTFiniteHodgeExactBlockerCountIs10 :
  listLength canonicalBTFiniteHodgeExactBlockers ≡ 10
canonicalBTFiniteHodgeExactBlockerCountIs10 =
  refl

canonicalBTFiniteHodgeExteriorDerivativeAvailable :
  BTFiniteHodgeStarObligation.finiteExteriorDerivativeAvailable
    canonicalBTFiniteHodgeStarObligation
  ≡
  true
canonicalBTFiniteHodgeExteriorDerivativeAvailable =
  refl

canonicalBTFiniteHodgeMetricPromotionFalse :
  BTFiniteHodgeStarObligation.btMetricHodgeStarPromoted
    canonicalBTFiniteHodgeStarObligation
  ≡
  false
canonicalBTFiniteHodgeMetricPromotionFalse =
  refl

canonicalBTFiniteHodgeMaxwellPromotionFalse :
  BTFiniteHodgeStarObligation.maxwellFieldEquationPromoted
    canonicalBTFiniteHodgeStarObligation
  ≡
  false
canonicalBTFiniteHodgeMaxwellPromotionFalse =
  refl

canonicalBTFiniteHodgeTerminalPromotionFalse :
  BTFiniteHodgeStarObligation.terminalPromotion
    canonicalBTFiniteHodgeStarObligation
  ≡
  false
canonicalBTFiniteHodgeTerminalPromotionFalse =
  refl
