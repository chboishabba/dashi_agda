module DASHI.Physics.Closure.BTFiniteHodgeEffectiveActionTheoremBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMConditionalMatterAuthorityToRealDStarF as Conditional
import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Spatial
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMRealSourcedDStarFEquationBoundary as Real
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as Pairing
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- BT finite Hodge effective-action theorem boundary.
--
-- This module packages the finite-depth clopen/BT effective-action target
-- using only stable repo surfaces: the Gate-B support interface, the
-- spatial-only bridge, the strict selected Hodge variation pairing, and the
-- conditional matter-authority to real D * F wrapper.  It names the finite
-- theorem boundary:
--
--   finite complex + finite gauge field + selected Hodge star
--   + finite action variation / IBP
--   -> Euler-Lagrange target D_A^* F_A = J
--
-- The target remains a finite selected boundary.  Physical matter authority,
-- real D * F = J, Maxwell/Yang-Mills promotion, Clay promotion, and terminal
-- promotion all stay false.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data BTFiniteHodgeEffectiveActionBoundaryStatus : Set where
  finiteBTEffectiveActionBoundaryNamedPhysicalPromotionBlocked :
    BTFiniteHodgeEffectiveActionBoundaryStatus

data BTFiniteHodgeEffectiveActionBoundaryRow : Set where
  gateBSupportInterfaceConsumedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  spatialOnlyBridgeConsumedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  strictSelectedHodgePairingConsumedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  conditionalMatterToRealDStarFConsumedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  finiteDepthBTComplexCarrierNamedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  finiteGaugeFieldCarrierNamedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  finiteHodgeStarCarrierNamedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  finiteActionSumCarrierNamedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  eulerLagrangeDStarFEqualsJTargetNamedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  currentConservationTargetNamedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  matterCurrentAuthorityStillBlockedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  realDStarFEqualsJLawStillBlockedRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

  promotionGuardsFalseRow :
    BTFiniteHodgeEffectiveActionBoundaryRow

canonicalBTFiniteHodgeEffectiveActionBoundaryRows :
  List BTFiniteHodgeEffectiveActionBoundaryRow
canonicalBTFiniteHodgeEffectiveActionBoundaryRows =
  gateBSupportInterfaceConsumedRow
  ∷ spatialOnlyBridgeConsumedRow
  ∷ strictSelectedHodgePairingConsumedRow
  ∷ conditionalMatterToRealDStarFConsumedRow
  ∷ finiteDepthBTComplexCarrierNamedRow
  ∷ finiteGaugeFieldCarrierNamedRow
  ∷ finiteHodgeStarCarrierNamedRow
  ∷ finiteActionSumCarrierNamedRow
  ∷ eulerLagrangeDStarFEqualsJTargetNamedRow
  ∷ currentConservationTargetNamedRow
  ∷ matterCurrentAuthorityStillBlockedRow
  ∷ realDStarFEqualsJLawStillBlockedRow
  ∷ promotionGuardsFalseRow
  ∷ []

data BTFiniteDepthComplexCarrier : Set₂ where
  btFiniteDepthComplexFromSpatialSupport :
    BTFiniteDepthComplexCarrier

data BTFiniteGaugeFieldCarrier : Set where
  btFiniteGaugeFieldFromSelectedConnection :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    BTFiniteGaugeFieldCarrier

data BTFiniteHodgeStarCarrier : Set where
  btFiniteHodgeStarFromSelectedPairing :
    BTFiniteHodgeStarCarrier

data BTFiniteEffectiveActionSum : Set where
  btFiniteEffectiveActionSumFromSelectedVariation :
    YMObs.YMSFGCUserSuppliedActionScalarCarrier →
    BTFiniteEffectiveActionSum

data BTFiniteEulerLagrangeDStarFEqualsJTarget : Set where
  btFiniteEulerLagrangeTargetFromConditionalRealBoundary :
    Conditional.ConditionalRealDStarFEqualsJTarget →
    BTFiniteEulerLagrangeDStarFEqualsJTarget

data BTFiniteCurrentConservationTarget : Set where
  btFiniteCurrentConservationTargetFromSelectedCurrent :
    YMObs.YMSFGCUserSuppliedCurrentCarrier →
    BTFiniteCurrentConservationTarget

canonicalBTFiniteDepthComplex :
  BTFiniteDepthComplexCarrier
canonicalBTFiniteDepthComplex =
  btFiniteDepthComplexFromSpatialSupport

canonicalBTFiniteGaugeField :
  BTFiniteGaugeFieldCarrier
canonicalBTFiniteGaugeField =
  btFiniteGaugeFieldFromSelectedConnection
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

canonicalBTFiniteHodgeStar :
  BTFiniteHodgeStarCarrier
canonicalBTFiniteHodgeStar =
  btFiniteHodgeStarFromSelectedPairing

canonicalBTFiniteEffectiveActionSum :
  BTFiniteEffectiveActionSum
canonicalBTFiniteEffectiveActionSum =
  btFiniteEffectiveActionSumFromSelectedVariation
    (Pairing.strictSelectedActionVariation
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
      (YMObs.ymSFGCUserSuppliedVariationFromGaugeField
        SFGC.vacuumGaugeField))

canonicalBTFiniteEulerLagrangeTarget :
  BTFiniteEulerLagrangeDStarFEqualsJTarget
canonicalBTFiniteEulerLagrangeTarget =
  btFiniteEulerLagrangeTargetFromConditionalRealBoundary
    Conditional.canonicalConditionalRealDStarFEqualsJTarget

canonicalBTFiniteCurrentConservationTarget :
  BTFiniteCurrentConservationTarget
canonicalBTFiniteCurrentConservationTarget =
  btFiniteCurrentConservationTargetFromSelectedCurrent
    (Pairing.strictSelectedCurrentFromDerivative
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
      Pairing.strictReferenceDualCurvature)

btFiniteSelectedIBPLaw :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (variation : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  Pairing.strictSelectedActionVariation connection variation
  ≡
  Pairing.strictActionScalarCombine
    (Pairing.strictSelectedHodgeVariationPairing connection variation)
    (Pairing.strictSelectedBoundaryTerm connection variation)
btFiniteSelectedIBPLaw =
  Pairing.strictSelectedDiscreteIBPLaw

record BTFiniteHodgeEffectiveActionTheoremBoundary : Set₂ where
  field
    status :
      BTFiniteHodgeEffectiveActionBoundaryStatus

    consumedSupportInterface :
      Support.GateBSupportInterfaceBoundary

    consumedSupportInterfaceIsCanonical :
      consumedSupportInterface
      ≡
      Support.gateBSupportInterfaceBoundary

    consumedSpatialOnlyBridge :
      Spatial.GateBSpatialOnlyBridgeBoundary

    consumedSpatialOnlyBridgeIsCanonical :
      consumedSpatialOnlyBridge
      ≡
      Spatial.gateBSpatialOnlyBridgeBoundary

    consumedStrictSelectedHodgePairing :
      Pairing.StrictSelectedHodgeVariationPairingCalculation

    consumedStrictSelectedHodgePairingIsCanonical :
      consumedStrictSelectedHodgePairing
      ≡
      Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation

    consumedConditionalMatterToRealDStarF :
      Conditional.YMConditionalMatterAuthorityToRealDStarF

    consumedConditionalMatterToRealDStarFIsCanonical :
      consumedConditionalMatterToRealDStarF
      ≡
      Conditional.canonicalYMConditionalMatterAuthorityToRealDStarF

    finiteDepthBTComplex :
      BTFiniteDepthComplexCarrier

    finiteDepthBTComplexIsCanonical :
      finiteDepthBTComplex ≡ canonicalBTFiniteDepthComplex

    finiteGaugeField :
      BTFiniteGaugeFieldCarrier

    finiteGaugeFieldIsCanonical :
      finiteGaugeField ≡ canonicalBTFiniteGaugeField

    finiteHodgeStar :
      BTFiniteHodgeStarCarrier

    finiteHodgeStarIsCanonical :
      finiteHodgeStar ≡ canonicalBTFiniteHodgeStar

    finiteEffectiveActionSum :
      BTFiniteEffectiveActionSum

    finiteEffectiveActionSumIsCanonical :
      finiteEffectiveActionSum ≡ canonicalBTFiniteEffectiveActionSum

    eulerLagrangeTarget :
      BTFiniteEulerLagrangeDStarFEqualsJTarget

    eulerLagrangeTargetIsCanonical :
      eulerLagrangeTarget ≡ canonicalBTFiniteEulerLagrangeTarget

    currentConservationTarget :
      BTFiniteCurrentConservationTarget

    currentConservationTargetIsCanonical :
      currentConservationTarget
      ≡
      canonicalBTFiniteCurrentConservationTarget

    selectedFiniteVariationIBPLaw :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (variation : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      Pairing.strictSelectedActionVariation connection variation
      ≡
      Pairing.strictActionScalarCombine
        (Pairing.strictSelectedHodgeVariationPairing connection variation)
        (Pairing.strictSelectedBoundaryTerm connection variation)

    selectedFiniteVariationIBPLawIsCanonical :
      selectedFiniteVariationIBPLaw ≡ btFiniteSelectedIBPLaw

    finiteEffectiveActionBoundaryNamed :
      Bool

    finiteEffectiveActionBoundaryNamedIsTrue :
      finiteEffectiveActionBoundaryNamed ≡ true

    eulerLagrangeDStarFEqualsJTargetNamed :
      Bool

    eulerLagrangeDStarFEqualsJTargetNamedIsTrue :
      eulerLagrangeDStarFEqualsJTargetNamed ≡ true

    currentConservationTargetNamed :
      Bool

    currentConservationTargetNamedIsTrue :
      currentConservationTargetNamed ≡ true

    exactMatterCouplingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter :
      exactMatterCouplingBlocker
      ≡
      YMObs.missingCurrentSourceCouplingToMatter

    exactRealDStarFEqualsJBlocker :
      YMObs.YangMillsFieldEquationMissingPrerequisite

    exactRealDStarFEqualsJBlockerIsMissingDStarFEqualsJLaw :
      exactRealDStarFEqualsJBlocker
      ≡
      YMObs.missingDStarFEqualsJLaw

    physicalMatterCurrentAuthorityAccepted :
      Bool

    physicalMatterCurrentAuthorityAcceptedIsFalse :
      physicalMatterCurrentAuthorityAccepted ≡ false

    realDStarFEqualsJLawPromoted :
      Bool

    realDStarFEqualsJLawPromotedIsFalse :
      realDStarFEqualsJLawPromoted ≡ false

    maxwellPromoted :
      Bool

    maxwellPromotedIsFalse :
      maxwellPromoted ≡ false

    yangMillsPromoted :
      Bool

    yangMillsPromotedIsFalse :
      yangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    rows :
      List BTFiniteHodgeEffectiveActionBoundaryRow

    rowsAreCanonical :
      rows ≡ canonicalBTFiniteHodgeEffectiveActionBoundaryRows

    rowCount :
      Nat

    rowCountIs13 :
      rowCount ≡ 13

    theoremBoundary :
      List String

open BTFiniteHodgeEffectiveActionTheoremBoundary public

canonicalBTFiniteHodgeEffectiveActionTheoremBoundary :
  BTFiniteHodgeEffectiveActionTheoremBoundary
canonicalBTFiniteHodgeEffectiveActionTheoremBoundary =
  record
    { status =
        finiteBTEffectiveActionBoundaryNamedPhysicalPromotionBlocked
    ; consumedSupportInterface =
        Support.gateBSupportInterfaceBoundary
    ; consumedSupportInterfaceIsCanonical =
        refl
    ; consumedSpatialOnlyBridge =
        Spatial.gateBSpatialOnlyBridgeBoundary
    ; consumedSpatialOnlyBridgeIsCanonical =
        refl
    ; consumedStrictSelectedHodgePairing =
        Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; consumedStrictSelectedHodgePairingIsCanonical =
        refl
    ; consumedConditionalMatterToRealDStarF =
        Conditional.canonicalYMConditionalMatterAuthorityToRealDStarF
    ; consumedConditionalMatterToRealDStarFIsCanonical =
        refl
    ; finiteDepthBTComplex =
        canonicalBTFiniteDepthComplex
    ; finiteDepthBTComplexIsCanonical =
        refl
    ; finiteGaugeField =
        canonicalBTFiniteGaugeField
    ; finiteGaugeFieldIsCanonical =
        refl
    ; finiteHodgeStar =
        canonicalBTFiniteHodgeStar
    ; finiteHodgeStarIsCanonical =
        refl
    ; finiteEffectiveActionSum =
        canonicalBTFiniteEffectiveActionSum
    ; finiteEffectiveActionSumIsCanonical =
        refl
    ; eulerLagrangeTarget =
        canonicalBTFiniteEulerLagrangeTarget
    ; eulerLagrangeTargetIsCanonical =
        refl
    ; currentConservationTarget =
        canonicalBTFiniteCurrentConservationTarget
    ; currentConservationTargetIsCanonical =
        refl
    ; selectedFiniteVariationIBPLaw =
        btFiniteSelectedIBPLaw
    ; selectedFiniteVariationIBPLawIsCanonical =
        refl
    ; finiteEffectiveActionBoundaryNamed =
        true
    ; finiteEffectiveActionBoundaryNamedIsTrue =
        refl
    ; eulerLagrangeDStarFEqualsJTargetNamed =
        true
    ; eulerLagrangeDStarFEqualsJTargetNamedIsTrue =
        refl
    ; currentConservationTargetNamed =
        true
    ; currentConservationTargetNamedIsTrue =
        refl
    ; exactMatterCouplingBlocker =
        YMObs.missingCurrentSourceCouplingToMatter
    ; exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter =
        refl
    ; exactRealDStarFEqualsJBlocker =
        YMObs.missingDStarFEqualsJLaw
    ; exactRealDStarFEqualsJBlockerIsMissingDStarFEqualsJLaw =
        refl
    ; physicalMatterCurrentAuthorityAccepted =
        false
    ; physicalMatterCurrentAuthorityAcceptedIsFalse =
        refl
    ; realDStarFEqualsJLawPromoted =
        false
    ; realDStarFEqualsJLawPromotedIsFalse =
        refl
    ; maxwellPromoted =
        false
    ; maxwellPromotedIsFalse =
        refl
    ; yangMillsPromoted =
        false
    ; yangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; rows =
        canonicalBTFiniteHodgeEffectiveActionBoundaryRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        13
    ; rowCountIs13 =
        refl
    ; theoremBoundary =
        "Consumes the Gate-B support interface and spatial-only bridge as finite-depth BT/clopen complex support"
        ∷ "Consumes the strict selected Hodge variation pairing as the finite Hodge/action variation calculation"
        ∷ "Consumes the conditional matter-authority to real D * F wrapper as the Euler-Lagrange target boundary"
        ∷ "Names finite complex, finite gauge field, finite Hodge star, finite action sum, Euler-Lagrange D_A^* F_A = J target, and current-conservation target"
        ∷ "The selected finite IBP law is available; it is not a promoted physical sourced Yang-Mills equation"
        ∷ "The exact physical matter-current blocker remains missingCurrentSourceCouplingToMatter"
        ∷ "The exact real sourced equation blocker remains missingDStarFEqualsJLaw"
        ∷ "Maxwell, Yang-Mills, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalBTFiniteHodgeEffectiveActionBoundaryRowCountIs13 :
  listCount canonicalBTFiniteHodgeEffectiveActionBoundaryRows ≡ 13
canonicalBTFiniteHodgeEffectiveActionBoundaryRowCountIs13 =
  refl

canonicalBTFiniteHodgeEffectiveActionBoundaryNamed :
  finiteEffectiveActionBoundaryNamed
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  true
canonicalBTFiniteHodgeEffectiveActionBoundaryNamed =
  refl

canonicalBTFiniteHodgeEffectiveActionEulerTargetNamed :
  eulerLagrangeDStarFEqualsJTargetNamed
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  true
canonicalBTFiniteHodgeEffectiveActionEulerTargetNamed =
  refl

canonicalBTFiniteHodgeEffectiveActionCurrentConservationNamed :
  currentConservationTargetNamed
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  true
canonicalBTFiniteHodgeEffectiveActionCurrentConservationNamed =
  refl

canonicalBTFiniteHodgeEffectiveActionMatterBlockerExact :
  exactMatterCouplingBlocker
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  YMObs.missingCurrentSourceCouplingToMatter
canonicalBTFiniteHodgeEffectiveActionMatterBlockerExact =
  refl

canonicalBTFiniteHodgeEffectiveActionRealEquationBlockerExact :
  exactRealDStarFEqualsJBlocker
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  YMObs.missingDStarFEqualsJLaw
canonicalBTFiniteHodgeEffectiveActionRealEquationBlockerExact =
  refl

canonicalBTFiniteHodgeEffectiveActionMaxwellFalse :
  maxwellPromoted
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  false
canonicalBTFiniteHodgeEffectiveActionMaxwellFalse =
  refl

canonicalBTFiniteHodgeEffectiveActionYMFalse :
  yangMillsPromoted
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  false
canonicalBTFiniteHodgeEffectiveActionYMFalse =
  refl

canonicalBTFiniteHodgeEffectiveActionClayYMFalse :
  clayYangMillsPromoted
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  false
canonicalBTFiniteHodgeEffectiveActionClayYMFalse =
  refl

canonicalBTFiniteHodgeEffectiveActionTerminalFalse :
  terminalPromotion
    canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
  ≡
  false
canonicalBTFiniteHodgeEffectiveActionTerminalFalse =
  refl
