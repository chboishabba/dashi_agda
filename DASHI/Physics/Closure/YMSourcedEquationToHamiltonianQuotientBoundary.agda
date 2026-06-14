module DASHI.Physics.Closure.YMSourcedEquationToHamiltonianQuotientBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.PressureBelow15SpectralNatWitnessSlice as NatSlice
import DASHI.Physics.Closure.PressureBelow15SpectralTheoremObstruction as S8
import DASHI.Physics.Closure.YMFiniteSelectedPairingToRealCarrierBoundary as FiniteBoundary
import DASHI.Physics.Closure.YMRealSourcedDStarFEquationBoundary as RealSourced
import DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure as Sprint129
import DASHI.Physics.Closure.YMStrictSelectedSourceCurrentCoupling as Source

------------------------------------------------------------------------
-- Boundary from a real sourced YM equation to the Hamiltonian quotient.
--
-- The selected finite package now has a source-current carrier law and a
-- finite-to-real boundary.  This module records the exact next dependency: an
-- honest real sourced equation would feed the carrier-quotient Hamiltonian
-- theorem interface, but the first real-carrier blocker is still the missing
-- self-adjoint Yang-Mills Hamiltonian on the carrier quotient.  Sprint129 is
-- consumed only as existing DASHI-native transport context; it is not promoted
-- by this boundary to a real sourced equation, Clay, or terminal theorem.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data YMSourcedEquationToHamiltonianBoundaryStatus : Set where
  sourcedEquationFeedsHamiltonianBoundarySelfAdjointQuotientBlocked :
    YMSourcedEquationToHamiltonianBoundaryStatus

data YMSourcedEquationToHamiltonianBoundaryRow : Set where
  selectedSourceCurrentCouplingConsumedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  finiteSelectedPairingBoundaryConsumedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  realSourcedDStarFBoundaryConsumedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  boundedNatToRealTransitionConsumedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  lower6HamiltonianBlockerConsumedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  conditionalFiniteSpectralWiringConsumedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  sprint129TransportContextReferencedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  sourcedEquationWouldFeedCarrierHamiltonianRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  hamiltonianQuotientPrerequisiteBundleExposedRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  exactSelfAdjointHamiltonianBlockerRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  spectralGapAndClayHeldFalseRow :
    YMSourcedEquationToHamiltonianBoundaryRow

  terminalPromotionHeldFalseRow :
    YMSourcedEquationToHamiltonianBoundaryRow

canonicalYMSourcedEquationToHamiltonianBoundaryRows :
  List YMSourcedEquationToHamiltonianBoundaryRow
canonicalYMSourcedEquationToHamiltonianBoundaryRows =
  selectedSourceCurrentCouplingConsumedRow
  ∷ finiteSelectedPairingBoundaryConsumedRow
  ∷ realSourcedDStarFBoundaryConsumedRow
  ∷ boundedNatToRealTransitionConsumedRow
  ∷ lower6HamiltonianBlockerConsumedRow
  ∷ conditionalFiniteSpectralWiringConsumedRow
  ∷ sprint129TransportContextReferencedRow
  ∷ sourcedEquationWouldFeedCarrierHamiltonianRow
  ∷ hamiltonianQuotientPrerequisiteBundleExposedRow
  ∷ exactSelfAdjointHamiltonianBlockerRow
  ∷ spectralGapAndClayHeldFalseRow
  ∷ terminalPromotionHeldFalseRow
  ∷ []

data YMSourcedEquationToHamiltonianFeed : Set where
  selectedFiniteDStarFEqualsCurrentFeedsSourcedEquation :
    YMSourcedEquationToHamiltonianFeed

  sourcedEquationTargetsRealCarrierQuotientHamiltonian :
    YMSourcedEquationToHamiltonianFeed

  realHamiltonianRequiresSelfAdjointQuotientTheorem :
    YMSourcedEquationToHamiltonianFeed

  selfAdjointQuotientTheoremFeedsSpectralGapOnlyAfterTransport :
    YMSourcedEquationToHamiltonianFeed

canonicalYMSourcedEquationToHamiltonianFeeds :
  List YMSourcedEquationToHamiltonianFeed
canonicalYMSourcedEquationToHamiltonianFeeds =
  selectedFiniteDStarFEqualsCurrentFeedsSourcedEquation
  ∷ sourcedEquationTargetsRealCarrierQuotientHamiltonian
  ∷ realHamiltonianRequiresSelfAdjointQuotientTheorem
  ∷ selfAdjointQuotientTheoremFeedsSpectralGapOnlyAfterTransport
  ∷ []

data YMHamiltonianQuotientPrerequisiteBlocker : Set where
  realSourcedDStarFEquationStillBoundary :
    YMHamiltonianQuotientPrerequisiteBlocker

  missingRealGaugeOrbitEquivalenceForCarrierQuotient :
    YMHamiltonianQuotientPrerequisiteBlocker

  missingRealHamiltonianOperatorAndDenseDomain :
    YMHamiltonianQuotientPrerequisiteBlocker

  missingSymmetricDenseHamiltonianAndSelfAdjointExtension :
    YMHamiltonianQuotientPrerequisiteBlocker

  missingFiniteCarrierBoundTransportToRealYM :
    YMHamiltonianQuotientPrerequisiteBlocker

canonicalYMHamiltonianQuotientPrerequisiteBlockers :
  List YMHamiltonianQuotientPrerequisiteBlocker
canonicalYMHamiltonianQuotientPrerequisiteBlockers =
  realSourcedDStarFEquationStillBoundary
  ∷ missingRealGaugeOrbitEquivalenceForCarrierQuotient
  ∷ missingRealHamiltonianOperatorAndDenseDomain
  ∷ missingSymmetricDenseHamiltonianAndSelfAdjointExtension
  ∷ missingFiniteCarrierBoundTransportToRealYM
  ∷ []

record YMHamiltonianQuotientPrerequisiteBundle : Setω where
  field
    realSourcedDStarFBoundary :
      RealSourced.YMRealSourcedDStarFEquationBoundary

    realSourcedDStarFBoundaryIsCanonical :
      realSourcedDStarFBoundary
      ≡
      RealSourced.canonicalYMRealSourcedDStarFEquationBoundary

    finiteSelectedDStarFCurrentLawConsumed :
      Bool

    finiteSelectedDStarFCurrentLawConsumedIsTrue :
      finiteSelectedDStarFCurrentLawConsumed ≡ true

    realBoundaryEquationTargetTyped :
      Bool

    realBoundaryEquationTargetTypedIsTrue :
      realBoundaryEquationTargetTyped ≡ true

    physicalRealDStarFEqualsJPromoted :
      Bool

    physicalRealDStarFEqualsJPromotedIsFalse :
      physicalRealDStarFEqualsJPromoted ≡ false

    quotientNextBlockerSurface :
      S8.U1RealYMQuotientHamiltonianNextBlockerSurface

    quotientNextBlockerSurfaceCanonical :
      Bool

    quotientNextBlockerSurfaceCanonicalIsTrue :
      quotientNextBlockerSurfaceCanonical ≡ true

    firstLocalQuotientBlocker :
      S8.U1RealYMQuotientHamiltonianNextBlocker

    firstLocalQuotientBlockerIsGaugeOrbitEquivalence :
      firstLocalQuotientBlocker
      ≡
      S8.missingRealGaugeOrbitEquivalence

    realGaugeOrbitEquivalenceConstructed :
      Bool

    realGaugeOrbitEquivalenceConstructedIsFalse :
      realGaugeOrbitEquivalenceConstructed ≡ false

    denseDomainConstructed :
      Bool

    denseDomainConstructedIsFalse :
      denseDomainConstructed ≡ false

    symmetricOnDenseDomainConstructed :
      Bool

    symmetricOnDenseDomainConstructedIsFalse :
      symmetricOnDenseDomainConstructed ≡ false

    selfAdjointExtensionConstructed :
      Bool

    selfAdjointExtensionConstructedIsFalse :
      selfAdjointExtensionConstructed ≡ false

    finiteCarrierBoundTransportedToRealYM :
      Bool

    finiteCarrierBoundTransportedToRealYMIsFalse :
      finiteCarrierBoundTransportedToRealYM ≡ false

    firstGlobalCarrierBlocker :
      S8.S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstGlobalCarrierBlockerIsSelfAdjointYangMillsHamiltonian :
      firstGlobalCarrierBlocker
      ≡
      S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    orderedPrerequisiteBlockers :
      List YMHamiltonianQuotientPrerequisiteBlocker

    orderedPrerequisiteBlockersAreCanonical :
      orderedPrerequisiteBlockers
      ≡
      canonicalYMHamiltonianQuotientPrerequisiteBlockers

    orderedPrerequisiteBlockerCount :
      Nat

    orderedPrerequisiteBlockerCountIs5 :
      orderedPrerequisiteBlockerCount ≡ 5

open YMHamiltonianQuotientPrerequisiteBundle public

canonicalYMHamiltonianQuotientPrerequisiteBundle :
  YMHamiltonianQuotientPrerequisiteBundle
canonicalYMHamiltonianQuotientPrerequisiteBundle =
  record
    { realSourcedDStarFBoundary =
        RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; realSourcedDStarFBoundaryIsCanonical =
        refl
    ; finiteSelectedDStarFCurrentLawConsumed =
        RealSourced.finiteSelectedDStarFCurrentLawConsumed
          RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; finiteSelectedDStarFCurrentLawConsumedIsTrue =
        RealSourced.finiteSelectedDStarFCurrentLawConsumedIsTrue
          RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; realBoundaryEquationTargetTyped =
        RealSourced.realBoundaryEquationTargetTyped
          RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; realBoundaryEquationTargetTypedIsTrue =
        RealSourced.realBoundaryEquationTargetTypedIsTrue
          RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; physicalRealDStarFEqualsJPromoted =
        RealSourced.physicalRealDStarFEqualsJPromoted
          RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; physicalRealDStarFEqualsJPromotedIsFalse =
        RealSourced.physicalRealDStarFEqualsJPromotedIsFalse
          RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; quotientNextBlockerSurface =
        S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; quotientNextBlockerSurfaceCanonical =
        true
    ; quotientNextBlockerSurfaceCanonicalIsTrue =
        refl
    ; firstLocalQuotientBlocker =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.firstBlocker
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; firstLocalQuotientBlockerIsGaugeOrbitEquivalence =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.firstBlockerIsRealGaugeOrbitEquivalence
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; realGaugeOrbitEquivalenceConstructed =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.realGaugeOrbitEquivalenceConstructed
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; realGaugeOrbitEquivalenceConstructedIsFalse =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.realGaugeOrbitEquivalenceConstructedIsFalse
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; denseDomainConstructed =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.denseDomainConstructed
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; denseDomainConstructedIsFalse =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.denseDomainConstructedIsFalse
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; symmetricOnDenseDomainConstructed =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.symmetricOnDenseDomainConstructed
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; symmetricOnDenseDomainConstructedIsFalse =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.symmetricOnDenseDomainConstructedIsFalse
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; selfAdjointExtensionConstructed =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.selfAdjointExtensionConstructed
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; selfAdjointExtensionConstructedIsFalse =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.selfAdjointExtensionConstructedIsFalse
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; finiteCarrierBoundTransportedToRealYM =
        NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYM
          NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; finiteCarrierBoundTransportedToRealYMIsFalse =
        NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYMIsFalse
          NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; firstGlobalCarrierBlocker =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.firstGlobalCarrierMissing
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; firstGlobalCarrierBlockerIsSelfAdjointYangMillsHamiltonian =
        S8.U1RealYMQuotientHamiltonianNextBlockerSurface.firstGlobalCarrierMissingIsSelfAdjointYangMillsHamiltonian
          S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; orderedPrerequisiteBlockers =
        canonicalYMHamiltonianQuotientPrerequisiteBlockers
    ; orderedPrerequisiteBlockersAreCanonical =
        refl
    ; orderedPrerequisiteBlockerCount =
        5
    ; orderedPrerequisiteBlockerCountIs5 =
        refl
    }

record YMSourcedEquationToHamiltonianQuotientBoundary : Setω where
  field
    status :
      YMSourcedEquationToHamiltonianBoundaryStatus

    selectedSourceCurrentCoupling :
      Source.StrictSelectedSourceCurrentCouplingReceipt

    selectedSourceCurrentCouplingIsCanonical :
      selectedSourceCurrentCoupling
      ≡
      Source.canonicalStrictSelectedSourceCurrentCouplingReceipt

    finiteSelectedBoundary :
      FiniteBoundary.YMFiniteSelectedPairingToRealCarrierBoundary

    finiteSelectedBoundaryIsCanonical :
      finiteSelectedBoundary
      ≡
      FiniteBoundary.canonicalYMFiniteSelectedPairingToRealCarrierBoundary

    realSourcedDStarFBoundary :
      RealSourced.YMRealSourcedDStarFEquationBoundary

    realSourcedDStarFBoundaryIsCanonical :
      realSourcedDStarFBoundary
      ≡
      RealSourced.canonicalYMRealSourcedDStarFEquationBoundary

    boundedNatTransition :
      NatSlice.S8NatToRealPhysicalCarrierTransitionReceipt

    boundedNatTransitionCanonical :
      Bool

    boundedNatTransitionCanonicalIsTrue :
      boundedNatTransitionCanonical ≡ true

    lower6HamiltonianBlocker :
      NatSlice.S8Lower6RealCarrierAndHamiltonianBlockerReceipt

    lower6HamiltonianBlockerCanonical :
      Bool

    lower6HamiltonianBlockerCanonicalIsTrue :
      lower6HamiltonianBlockerCanonical ≡ true

    conditionalFiniteSpectralWiring :
      NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt

    conditionalFiniteSpectralWiringCanonical :
      Bool

    conditionalFiniteSpectralWiringCanonicalIsTrue :
      conditionalFiniteSpectralWiringCanonical ≡ true

    sprint129TransportContext :
      Sprint129.YMSprint129SpectralGapTransportClosureReceipt

    sprint129TransportContextCanonical :
      Bool

    sprint129TransportContextCanonicalIsTrue :
      sprint129TransportContextCanonical ≡ true

    sprint129DashiNativeTransportClosed :
      Bool

    sprint129DashiNativeTransportClosedIsTrue :
      sprint129DashiNativeTransportClosed ≡ true

    selectedFiniteSourcedEquationAvailable :
      Bool

    selectedFiniteSourcedEquationAvailableIsTrue :
      selectedFiniteSourcedEquationAvailable ≡ true

    physicalSourcedYangMillsEquationPromoted :
      Bool

    physicalSourcedYangMillsEquationPromotedIsFalse :
      physicalSourcedYangMillsEquationPromoted ≡ false

    sourcedEquationWouldFeedHamiltonianQuotient :
      Bool

    sourcedEquationWouldFeedHamiltonianQuotientIsTrue :
      sourcedEquationWouldFeedHamiltonianQuotient ≡ true

    hamiltonianQuotientPrerequisites :
      YMHamiltonianQuotientPrerequisiteBundle

    hamiltonianQuotientPrerequisitesAreCanonical :
      hamiltonianQuotientPrerequisites
      ≡
      canonicalYMHamiltonianQuotientPrerequisiteBundle

    prerequisiteFirstLocalBlocker :
      YMHamiltonianQuotientPrerequisiteBlocker

    prerequisiteFirstLocalBlockerIsRealSourcedBoundary :
      prerequisiteFirstLocalBlocker
      ≡
      realSourcedDStarFEquationStillBoundary

    realCarrierTheoremConstructed :
      Bool

    realCarrierTheoremConstructedIsFalse :
      realCarrierTheoremConstructed ≡ false

    finiteCarrierBoundTransportedToRealYM :
      Bool

    finiteCarrierBoundTransportedToRealYMIsFalse :
      finiteCarrierBoundTransportedToRealYM ≡ false

    firstRealCarrierBlocker :
      S8.S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstRealCarrierBlockerIsSelfAdjointYangMillsHamiltonian :
      firstRealCarrierBlocker
      ≡
      S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    firstRealCarrierTheoremField :
      S8.S8GlobalYangMillsHamiltonianCarrierTheoremField

    firstRealCarrierTheoremFieldIsSelfAdjointHamiltonian :
      firstRealCarrierTheoremField
      ≡
      S8.s8SelfAdjointHamiltonianOnCarrierQuotientField

    hardExternalHalt :
      S8.S8RealCarrierHardExternalHalt

    hardExternalHaltIsUniformBalabanOrAgawa :
      hardExternalHalt
      ≡
      S8.uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    feeds :
      List YMSourcedEquationToHamiltonianFeed

    feedsAreCanonical :
      feeds ≡ canonicalYMSourcedEquationToHamiltonianFeeds

    feedCount :
      Nat

    feedCountIs4 :
      feedCount ≡ 4

    rows :
      List YMSourcedEquationToHamiltonianBoundaryRow

    rowsAreCanonical :
      rows ≡ canonicalYMSourcedEquationToHamiltonianBoundaryRows

    rowCount :
      Nat

    rowCountIs12 :
      rowCount ≡ 12

    hamiltonianTheoremPromoted :
      Bool

    hamiltonianTheoremPromotedIsFalse :
      hamiltonianTheoremPromoted ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    boundary :
      List String

open YMSourcedEquationToHamiltonianQuotientBoundary public

canonicalYMSourcedEquationToHamiltonianQuotientBoundary :
  YMSourcedEquationToHamiltonianQuotientBoundary
canonicalYMSourcedEquationToHamiltonianQuotientBoundary =
  record
    { status =
        sourcedEquationFeedsHamiltonianBoundarySelfAdjointQuotientBlocked
    ; selectedSourceCurrentCoupling =
        Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; selectedSourceCurrentCouplingIsCanonical =
        refl
    ; finiteSelectedBoundary =
        FiniteBoundary.canonicalYMFiniteSelectedPairingToRealCarrierBoundary
    ; finiteSelectedBoundaryIsCanonical =
        refl
    ; realSourcedDStarFBoundary =
        RealSourced.canonicalYMRealSourcedDStarFEquationBoundary
    ; realSourcedDStarFBoundaryIsCanonical =
        refl
    ; boundedNatTransition =
        NatSlice.canonicalS8NatToRealPhysicalCarrierTransitionReceipt
    ; boundedNatTransitionCanonical =
        true
    ; boundedNatTransitionCanonicalIsTrue =
        refl
    ; lower6HamiltonianBlocker =
        NatSlice.canonicalS8Lower6RealCarrierAndHamiltonianBlockerReceipt
    ; lower6HamiltonianBlockerCanonical =
        true
    ; lower6HamiltonianBlockerCanonicalIsTrue =
        refl
    ; conditionalFiniteSpectralWiring =
        NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; conditionalFiniteSpectralWiringCanonical =
        true
    ; conditionalFiniteSpectralWiringCanonicalIsTrue =
        refl
    ; sprint129TransportContext =
        Sprint129.canonicalYMSprint129SpectralGapTransportClosureReceipt
    ; sprint129TransportContextCanonical =
        true
    ; sprint129TransportContextCanonicalIsTrue =
        refl
    ; sprint129DashiNativeTransportClosed =
        Sprint129.spectralGapTransportClosedHere
    ; sprint129DashiNativeTransportClosedIsTrue =
        Sprint129.spectralGapTransportClosedHereIsTrue
    ; selectedFiniteSourcedEquationAvailable =
        Source.StrictSelectedSourceCurrentCouplingReceipt.finiteSourceCurrentCoupled
          Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; selectedFiniteSourcedEquationAvailableIsTrue =
        Source.StrictSelectedSourceCurrentCouplingReceipt.finiteSourceCurrentCoupledIsTrue
          Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; physicalSourcedYangMillsEquationPromoted =
        Source.StrictSelectedSourceCurrentCouplingReceipt.physicalSourcedYangMillsPromoted
          Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; physicalSourcedYangMillsEquationPromotedIsFalse =
        Source.StrictSelectedSourceCurrentCouplingReceipt.physicalSourcedYangMillsPromotedIsFalse
          Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; sourcedEquationWouldFeedHamiltonianQuotient =
        true
    ; sourcedEquationWouldFeedHamiltonianQuotientIsTrue =
        refl
    ; hamiltonianQuotientPrerequisites =
        canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; hamiltonianQuotientPrerequisitesAreCanonical =
        refl
    ; prerequisiteFirstLocalBlocker =
        realSourcedDStarFEquationStillBoundary
    ; prerequisiteFirstLocalBlockerIsRealSourcedBoundary =
        refl
    ; realCarrierTheoremConstructed =
        NatSlice.S8Lower6RealCarrierAndHamiltonianBlockerReceipt.realCarrierTheoremConstructed
          NatSlice.canonicalS8Lower6RealCarrierAndHamiltonianBlockerReceipt
    ; realCarrierTheoremConstructedIsFalse =
        NatSlice.S8Lower6RealCarrierAndHamiltonianBlockerReceipt.realCarrierTheoremConstructedIsFalse
          NatSlice.canonicalS8Lower6RealCarrierAndHamiltonianBlockerReceipt
    ; finiteCarrierBoundTransportedToRealYM =
        NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYM
          NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; finiteCarrierBoundTransportedToRealYMIsFalse =
        NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYMIsFalse
          NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; firstRealCarrierBlocker =
        S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstRealCarrierBlockerIsSelfAdjointYangMillsHamiltonian =
        refl
    ; firstRealCarrierTheoremField =
        S8.s8SelfAdjointHamiltonianOnCarrierQuotientField
    ; firstRealCarrierTheoremFieldIsSelfAdjointHamiltonian =
        refl
    ; hardExternalHalt =
        S8.uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; hardExternalHaltIsUniformBalabanOrAgawa =
        refl
    ; feeds =
        canonicalYMSourcedEquationToHamiltonianFeeds
    ; feedsAreCanonical =
        refl
    ; feedCount =
        4
    ; feedCountIs4 =
        refl
    ; rows =
        canonicalYMSourcedEquationToHamiltonianBoundaryRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        12
    ; rowCountIs12 =
        refl
    ; hamiltonianTheoremPromoted =
        false
    ; hamiltonianTheoremPromotedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; boundary =
        "The selected finite source-current coupling supplies only a finite D * F equals selected-current carrier law"
        ∷ "The real sourced D * F boundary package is consumed as a typed boundary wrapper, with physical real D * F = J still false"
        ∷ "A real sourced Yang-Mills equation would feed the carrier-quotient Hamiltonian interface"
        ∷ "The prerequisite bundle exposes the ordered local blockers: sourced boundary, gauge-orbit equivalence, operator/domain, symmetry/self-adjoint extension, and finite-to-real transport"
        ∷ "The bounded Nat carrier theorem is already inhabited, but the Nat-to-real transition keeps the real physical carrier theorem false"
        ∷ "Sprint129 transport is referenced as DASHI-native context only and is not a proof of this sourced-equation-to-Hamiltonian boundary"
        ∷ "The exact first real-carrier blocker remains missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "The first missing theorem field remains s8SelfAdjointHamiltonianOnCarrierQuotientField"
        ∷ "No Hamiltonian theorem, spectral gap, Clay Yang-Mills, or terminal promotion is constructed here"
        ∷ []
    }

canonicalYMSourcedEquationToHamiltonianBoundaryRowCountIs12 :
  listCount canonicalYMSourcedEquationToHamiltonianBoundaryRows ≡ 12
canonicalYMSourcedEquationToHamiltonianBoundaryRowCountIs12 =
  refl

canonicalYMHamiltonianQuotientPrerequisiteBlockerCountIs5 :
  listCount canonicalYMHamiltonianQuotientPrerequisiteBlockers ≡ 5
canonicalYMHamiltonianQuotientPrerequisiteBlockerCountIs5 =
  refl

canonicalYMSourcedEquationToHamiltonianFeedCountIs4 :
  listCount canonicalYMSourcedEquationToHamiltonianFeeds ≡ 4
canonicalYMSourcedEquationToHamiltonianFeedCountIs4 =
  refl

canonicalYMSourcedEquationToHamiltonianFirstBlockerIsSelfAdjointHamiltonian :
  firstRealCarrierBlocker
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
canonicalYMSourcedEquationToHamiltonianFirstBlockerIsSelfAdjointHamiltonian =
  refl

canonicalYMSourcedEquationToHamiltonianFirstFieldIsSelfAdjointHamiltonian :
  firstRealCarrierTheoremField
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  S8.s8SelfAdjointHamiltonianOnCarrierQuotientField
canonicalYMSourcedEquationToHamiltonianFirstFieldIsSelfAdjointHamiltonian =
  refl

canonicalYMSourcedEquationToHamiltonianFiniteSourceAvailable :
  selectedFiniteSourcedEquationAvailable
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  true
canonicalYMSourcedEquationToHamiltonianFiniteSourceAvailable =
  refl

canonicalYMSourcedEquationToHamiltonianRealSourcedBoundaryTyped :
  YMHamiltonianQuotientPrerequisiteBundle.realBoundaryEquationTargetTyped
    canonicalYMHamiltonianQuotientPrerequisiteBundle
  ≡
  true
canonicalYMSourcedEquationToHamiltonianRealSourcedBoundaryTyped =
  refl

canonicalYMSourcedEquationToHamiltonianPhysicalRealDStarFFalse :
  YMHamiltonianQuotientPrerequisiteBundle.physicalRealDStarFEqualsJPromoted
    canonicalYMHamiltonianQuotientPrerequisiteBundle
  ≡
  false
canonicalYMSourcedEquationToHamiltonianPhysicalRealDStarFFalse =
  refl

canonicalYMSourcedEquationToHamiltonianFirstLocalQuotientBlocker :
  YMHamiltonianQuotientPrerequisiteBundle.firstLocalQuotientBlocker
    canonicalYMHamiltonianQuotientPrerequisiteBundle
  ≡
  S8.missingRealGaugeOrbitEquivalence
canonicalYMSourcedEquationToHamiltonianFirstLocalQuotientBlocker =
  refl

canonicalYMSourcedEquationToHamiltonianPrerequisiteGlobalBlocker :
  YMHamiltonianQuotientPrerequisiteBundle.firstGlobalCarrierBlocker
    canonicalYMHamiltonianQuotientPrerequisiteBundle
  ≡
  S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
canonicalYMSourcedEquationToHamiltonianPrerequisiteGlobalBlocker =
  refl

canonicalYMSourcedEquationToHamiltonianRealCarrierTheoremFalse :
  realCarrierTheoremConstructed
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  false
canonicalYMSourcedEquationToHamiltonianRealCarrierTheoremFalse =
  refl

canonicalYMSourcedEquationToHamiltonianFiniteBoundNotTransported :
  finiteCarrierBoundTransportedToRealYM
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  false
canonicalYMSourcedEquationToHamiltonianFiniteBoundNotTransported =
  refl

canonicalYMSourcedEquationToHamiltonianHamiltonianTheoremFalse :
  hamiltonianTheoremPromoted
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  false
canonicalYMSourcedEquationToHamiltonianHamiltonianTheoremFalse =
  refl

canonicalYMSourcedEquationToHamiltonianSpectralGapFalse :
  spectralGapPromoted
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  false
canonicalYMSourcedEquationToHamiltonianSpectralGapFalse =
  refl

canonicalYMSourcedEquationToHamiltonianClayFalse :
  continuumClayMassGapPromoted
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  false
canonicalYMSourcedEquationToHamiltonianClayFalse =
  refl

canonicalYMSourcedEquationToHamiltonianTerminalFalse :
  terminalPromotion
    canonicalYMSourcedEquationToHamiltonianQuotientBoundary
  ≡
  false
canonicalYMSourcedEquationToHamiltonianTerminalFalse =
  refl
