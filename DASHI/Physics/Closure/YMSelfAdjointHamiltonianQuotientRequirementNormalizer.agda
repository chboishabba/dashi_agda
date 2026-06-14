module DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientRequirementNormalizer where

-- Requirement normalizer for the real Yang-Mills Hamiltonian quotient.
--
-- The sourced-equation boundary, Nat/real staging receipts, Stone bridge, and
-- pressure-below-15 obstruction already name the same halt:
-- missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient.  This module
-- normalizes those existing surfaces into one checked requirement index.  It
-- does not construct a self-adjoint Hamiltonian and does not promote the
-- spectral gap, Clay Yang-Mills, or terminal claims.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.PressureBelow15SpectralNatWitnessSlice as NatSlice
import DASHI.Physics.Closure.PressureBelow15SpectralTheoremObstruction as S8
import DASHI.Physics.Closure.SelfAdjointYangMillsHamiltonianOnCarrierQuotient as Hamiltonian
import DASHI.Physics.Closure.YMSourcedEquationToHamiltonianQuotientBoundary as Sourced

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data YMSelfAdjointHamiltonianRequirementNormalizerStatus : Set where
  requirementsNormalizedSelfAdjointHamiltonianStillMissing :
    YMSelfAdjointHamiltonianRequirementNormalizerStatus

data YMSelfAdjointHamiltonianRequirementRow : Set where
  sourcedEquationBoundaryConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  sourcedDStarFBoundaryPackageConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  hamiltonianQuotientPrerequisitesConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  natToRealTransitionConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  lower6RealCarrierBlockerConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  conditionalFiniteSpectralWiringConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  s8RealNonNatCarrierStagingConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  s8SelfAdjointBlockerReceiptConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  s8RealYMCarrierQuotientAuditConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  l6RealCarrierQuotientFailClosedConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  stoneHamiltonianGapBridgeConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  selectedCarrierLowerBoundReceiptConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  gate2ColimitGapLiftReceiptConsumedRow :
    YMSelfAdjointHamiltonianRequirementRow

  firstLocalQuotientBlockerNarrowedRow :
    YMSelfAdjointHamiltonianRequirementRow

  exactSelfAdjointHamiltonianBlockerNormalizedRow :
    YMSelfAdjointHamiltonianRequirementRow

  exactSelfAdjointHamiltonianTheoremFieldNormalizedRow :
    YMSelfAdjointHamiltonianRequirementRow

  promotionGuardsHeldFalseRow :
    YMSelfAdjointHamiltonianRequirementRow

canonicalYMSelfAdjointHamiltonianRequirementRows :
  List YMSelfAdjointHamiltonianRequirementRow
canonicalYMSelfAdjointHamiltonianRequirementRows =
  sourcedEquationBoundaryConsumedRow
  ∷ sourcedDStarFBoundaryPackageConsumedRow
  ∷ hamiltonianQuotientPrerequisitesConsumedRow
  ∷ natToRealTransitionConsumedRow
  ∷ lower6RealCarrierBlockerConsumedRow
  ∷ conditionalFiniteSpectralWiringConsumedRow
  ∷ s8RealNonNatCarrierStagingConsumedRow
  ∷ s8SelfAdjointBlockerReceiptConsumedRow
  ∷ s8RealYMCarrierQuotientAuditConsumedRow
  ∷ l6RealCarrierQuotientFailClosedConsumedRow
  ∷ stoneHamiltonianGapBridgeConsumedRow
  ∷ selectedCarrierLowerBoundReceiptConsumedRow
  ∷ gate2ColimitGapLiftReceiptConsumedRow
  ∷ firstLocalQuotientBlockerNarrowedRow
  ∷ exactSelfAdjointHamiltonianBlockerNormalizedRow
  ∷ exactSelfAdjointHamiltonianTheoremFieldNormalizedRow
  ∷ promotionGuardsHeldFalseRow
  ∷ []

data YMSelfAdjointHamiltonianNormalizedBlocker : Set where
  sourcedDStarFPackageStillBoundaryBlocker :
    YMSelfAdjointHamiltonianNormalizedBlocker

  realGaugeOrbitEquivalenceStillMissingBlocker :
    YMSelfAdjointHamiltonianNormalizedBlocker

  denseHamiltonianDomainStillMissingBlocker :
    YMSelfAdjointHamiltonianNormalizedBlocker

  symmetricSelfAdjointExtensionStillMissingBlocker :
    YMSelfAdjointHamiltonianNormalizedBlocker

  finiteLowerBoundTransportStillMissingBlocker :
    YMSelfAdjointHamiltonianNormalizedBlocker

  globalSelfAdjointHamiltonianQuotientStillMissingBlocker :
    YMSelfAdjointHamiltonianNormalizedBlocker

canonicalYMSelfAdjointHamiltonianNormalizedBlockers :
  List YMSelfAdjointHamiltonianNormalizedBlocker
canonicalYMSelfAdjointHamiltonianNormalizedBlockers =
  sourcedDStarFPackageStillBoundaryBlocker
  ∷ realGaugeOrbitEquivalenceStillMissingBlocker
  ∷ denseHamiltonianDomainStillMissingBlocker
  ∷ symmetricSelfAdjointExtensionStillMissingBlocker
  ∷ finiteLowerBoundTransportStillMissingBlocker
  ∷ globalSelfAdjointHamiltonianQuotientStillMissingBlocker
  ∷ []

normalizePrerequisiteBlocker :
  Sourced.YMHamiltonianQuotientPrerequisiteBlocker →
  YMSelfAdjointHamiltonianNormalizedBlocker
normalizePrerequisiteBlocker
  Sourced.realSourcedDStarFEquationStillBoundary =
  sourcedDStarFPackageStillBoundaryBlocker
normalizePrerequisiteBlocker
  Sourced.missingRealGaugeOrbitEquivalenceForCarrierQuotient =
  realGaugeOrbitEquivalenceStillMissingBlocker
normalizePrerequisiteBlocker
  Sourced.missingRealHamiltonianOperatorAndDenseDomain =
  denseHamiltonianDomainStillMissingBlocker
normalizePrerequisiteBlocker
  Sourced.missingSymmetricDenseHamiltonianAndSelfAdjointExtension =
  symmetricSelfAdjointExtensionStillMissingBlocker
normalizePrerequisiteBlocker
  Sourced.missingFiniteCarrierBoundTransportToRealYM =
  finiteLowerBoundTransportStillMissingBlocker

data YMSelfAdjointHamiltonianRequirementClass : Set where
  carrierQuotientAndGaugeEquivalenceRequired :
    YMSelfAdjointHamiltonianRequirementClass

  hamiltonianOperatorAndDenseDomainRequired :
    YMSelfAdjointHamiltonianRequirementClass

  symmetryAndSelfAdjointExtensionRequired :
    YMSelfAdjointHamiltonianRequirementClass

  stoneEvolutionCompatibilityRequired :
    YMSelfAdjointHamiltonianRequirementClass

  finiteLowerBoundTransportToRealYMRequired :
    YMSelfAdjointHamiltonianRequirementClass

canonicalYMSelfAdjointHamiltonianRequirementClasses :
  List YMSelfAdjointHamiltonianRequirementClass
canonicalYMSelfAdjointHamiltonianRequirementClasses =
  carrierQuotientAndGaugeEquivalenceRequired
  ∷ hamiltonianOperatorAndDenseDomainRequired
  ∷ symmetryAndSelfAdjointExtensionRequired
  ∷ stoneEvolutionCompatibilityRequired
  ∷ finiteLowerBoundTransportToRealYMRequired
  ∷ []

record YMSelfAdjointHamiltonianQuotientRequirementNormalizer : Setω where
  field
    status :
      YMSelfAdjointHamiltonianRequirementNormalizerStatus

    sourcedEquationBoundary :
      Sourced.YMSourcedEquationToHamiltonianQuotientBoundary

    sourcedEquationBoundaryCanonical :
      Bool

    sourcedEquationBoundaryCanonicalIsTrue :
      sourcedEquationBoundaryCanonical ≡ true

    sourcedHamiltonianPrerequisites :
      Sourced.YMHamiltonianQuotientPrerequisiteBundle

    sourcedHamiltonianPrerequisitesCanonical :
      Bool

    sourcedHamiltonianPrerequisitesCanonicalIsTrue :
      sourcedHamiltonianPrerequisitesCanonical ≡ true

    sourcedDStarFBoundaryTyped :
      Bool

    sourcedDStarFBoundaryTypedIsTrue :
      sourcedDStarFBoundaryTyped ≡ true

    physicalRealDStarFEqualsJPromoted :
      Bool

    physicalRealDStarFEqualsJPromotedIsFalse :
      physicalRealDStarFEqualsJPromoted ≡ false

    firstLocalPrerequisiteBlocker :
      Sourced.YMHamiltonianQuotientPrerequisiteBlocker

    firstLocalPrerequisiteBlockerIsSourcedBoundary :
      firstLocalPrerequisiteBlocker
      ≡
      Sourced.realSourcedDStarFEquationStillBoundary

    normalizedFirstLocalPrerequisiteBlocker :
      YMSelfAdjointHamiltonianNormalizedBlocker

    normalizedFirstLocalPrerequisiteBlockerIsSourcedDStarFBoundary :
      normalizedFirstLocalPrerequisiteBlocker
      ≡
      sourcedDStarFPackageStillBoundaryBlocker

    quotientGaugeOrbitEquivalenceConstructed :
      Bool

    quotientGaugeOrbitEquivalenceConstructedIsFalse :
      quotientGaugeOrbitEquivalenceConstructed ≡ false

    quotientDenseDomainConstructed :
      Bool

    quotientDenseDomainConstructedIsFalse :
      quotientDenseDomainConstructed ≡ false

    quotientSymmetricOnDenseDomainConstructed :
      Bool

    quotientSymmetricOnDenseDomainConstructedIsFalse :
      quotientSymmetricOnDenseDomainConstructed ≡ false

    quotientSelfAdjointExtensionConstructed :
      Bool

    quotientSelfAdjointExtensionConstructedIsFalse :
      quotientSelfAdjointExtensionConstructed ≡ false

    natToRealTransition :
      NatSlice.S8NatToRealPhysicalCarrierTransitionReceipt

    natToRealTransitionCanonical :
      Bool

    natToRealTransitionCanonicalIsTrue :
      natToRealTransitionCanonical ≡ true

    lower6RealCarrierBlocker :
      NatSlice.S8Lower6RealCarrierAndHamiltonianBlockerReceipt

    lower6RealCarrierBlockerCanonical :
      Bool

    lower6RealCarrierBlockerCanonicalIsTrue :
      lower6RealCarrierBlockerCanonical ≡ true

    conditionalFiniteCarrierWiring :
      NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt

    conditionalFiniteCarrierWiringCanonical :
      Bool

    conditionalFiniteCarrierWiringCanonicalIsTrue :
      conditionalFiniteCarrierWiringCanonical ≡ true

    realNonNatCarrierStaging :
      S8.S8RealNonNatCarrierStagingReceipt

    realNonNatCarrierStagingCanonical :
      Bool

    realNonNatCarrierStagingCanonicalIsTrue :
      realNonNatCarrierStagingCanonical ≡ true

    selfAdjointBlockerReceipt :
      S8.S8SelfAdjointHamiltonianBlockerReceipt

    selfAdjointBlockerReceiptCanonical :
      Bool

    selfAdjointBlockerReceiptCanonicalIsTrue :
      selfAdjointBlockerReceiptCanonical ≡ true

    realYMCarrierQuotientAudit :
      S8.S8RealYMCarrierQuotientImplementationAudit

    realYMCarrierQuotientAuditCanonical :
      Bool

    realYMCarrierQuotientAuditCanonicalIsTrue :
      realYMCarrierQuotientAuditCanonical ≡ true

    l6RealCarrierQuotientFailClosed :
      S8.L6RealCarrierQuotientFailClosedReceipt

    l6RealCarrierQuotientFailClosedCanonical :
      Bool

    l6RealCarrierQuotientFailClosedCanonicalIsTrue :
      l6RealCarrierQuotientFailClosedCanonical ≡ true

    stoneHamiltonianGapBridge :
      Hamiltonian.Gate8Term4StoneYMHamiltonianGapBridgeReceipt

    stoneHamiltonianGapBridgeCanonical :
      Bool

    stoneHamiltonianGapBridgeCanonicalIsTrue :
      stoneHamiltonianGapBridgeCanonical ≡ true

    selectedCarrierLowerBound :
      Hamiltonian.SelectedCarrierSpectralLowerBoundReceipt

    selectedCarrierLowerBoundCanonical :
      Bool

    selectedCarrierLowerBoundCanonicalIsTrue :
      selectedCarrierLowerBoundCanonical ≡ true

    gate2ColimitGapLift :
      Hamiltonian.Gate2ColimitGapLiftReceipt

    gate2ColimitGapLiftCanonical :
      Bool

    gate2ColimitGapLiftCanonicalIsTrue :
      gate2ColimitGapLiftCanonical ≡ true

    boundedNatCarrierTheoremAvailable :
      Bool

    boundedNatCarrierTheoremAvailableIsTrue :
      boundedNatCarrierTheoremAvailable ≡ true

    realCarrierTheoremConstructed :
      Bool

    realCarrierTheoremConstructedIsFalse :
      realCarrierTheoremConstructed ≡ false

    realYMCarrierQuotientConstructed :
      Bool

    realYMCarrierQuotientConstructedIsFalse :
      realYMCarrierQuotientConstructed ≡ false

    selfAdjointYangMillsHamiltonianConstructed :
      Bool

    selfAdjointYangMillsHamiltonianConstructedIsFalse :
      selfAdjointYangMillsHamiltonianConstructed ≡ false

    stoneGeneratorIdentifiedWithPhysicalYMHamiltonian :
      Bool

    stoneGeneratorIdentifiedWithPhysicalYMHamiltonianIsFalse :
      stoneGeneratorIdentifiedWithPhysicalYMHamiltonian ≡ false

    finiteCarrierBoundTransportedToRealYM :
      Bool

    finiteCarrierBoundTransportedToRealYMIsFalse :
      finiteCarrierBoundTransportedToRealYM ≡ false

    exactFirstBlocker :
      S8.S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    exactFirstBlockerIsMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
      exactFirstBlocker
      ≡
      S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    exactFirstTheoremField :
      S8.S8GlobalYangMillsHamiltonianCarrierTheoremField

    exactFirstTheoremFieldIsSelfAdjointHamiltonian :
      exactFirstTheoremField
      ≡
      S8.s8SelfAdjointHamiltonianOnCarrierQuotientField

    exactHardExternalHalt :
      S8.S8RealCarrierHardExternalHalt

    exactHardExternalHaltIsUniformBalabanOrAgawa :
      exactHardExternalHalt
      ≡
      S8.uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    normalizedRequirementClasses :
      List YMSelfAdjointHamiltonianRequirementClass

    normalizedRequirementClassesAreCanonical :
      normalizedRequirementClasses
      ≡
      canonicalYMSelfAdjointHamiltonianRequirementClasses

    normalizedRequirementClassCount :
      Nat

    normalizedRequirementClassCountIs5 :
      normalizedRequirementClassCount ≡ 5

    normalizedBlockers :
      List YMSelfAdjointHamiltonianNormalizedBlocker

    normalizedBlockersAreCanonical :
      normalizedBlockers
      ≡
      canonicalYMSelfAdjointHamiltonianNormalizedBlockers

    normalizedBlockerCount :
      Nat

    normalizedBlockerCountIs6 :
      normalizedBlockerCount ≡ 6

    rows :
      List YMSelfAdjointHamiltonianRequirementRow

    rowsAreCanonical :
      rows ≡ canonicalYMSelfAdjointHamiltonianRequirementRows

    rowCount :
      Nat

    rowCountIs17 :
      rowCount ≡ 17

    hamiltonianTheoremPromoted :
      Bool

    hamiltonianTheoremPromotedIsFalse :
      hamiltonianTheoremPromoted ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    normalizedBoundary :
      List String

open YMSelfAdjointHamiltonianQuotientRequirementNormalizer public

canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer :
  YMSelfAdjointHamiltonianQuotientRequirementNormalizer
canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer =
  record
    { status =
        requirementsNormalizedSelfAdjointHamiltonianStillMissing
    ; sourcedEquationBoundary =
        Sourced.canonicalYMSourcedEquationToHamiltonianQuotientBoundary
    ; sourcedEquationBoundaryCanonical =
        true
    ; sourcedEquationBoundaryCanonicalIsTrue =
        refl
    ; sourcedHamiltonianPrerequisites =
        Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; sourcedHamiltonianPrerequisitesCanonical =
        true
    ; sourcedHamiltonianPrerequisitesCanonicalIsTrue =
        refl
    ; sourcedDStarFBoundaryTyped =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.realBoundaryEquationTargetTyped
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; sourcedDStarFBoundaryTypedIsTrue =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.realBoundaryEquationTargetTypedIsTrue
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; physicalRealDStarFEqualsJPromoted =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.physicalRealDStarFEqualsJPromoted
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; physicalRealDStarFEqualsJPromotedIsFalse =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.physicalRealDStarFEqualsJPromotedIsFalse
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; firstLocalPrerequisiteBlocker =
        Sourced.prerequisiteFirstLocalBlocker
          Sourced.canonicalYMSourcedEquationToHamiltonianQuotientBoundary
    ; firstLocalPrerequisiteBlockerIsSourcedBoundary =
        Sourced.prerequisiteFirstLocalBlockerIsRealSourcedBoundary
          Sourced.canonicalYMSourcedEquationToHamiltonianQuotientBoundary
    ; normalizedFirstLocalPrerequisiteBlocker =
        normalizePrerequisiteBlocker
          (Sourced.prerequisiteFirstLocalBlocker
            Sourced.canonicalYMSourcedEquationToHamiltonianQuotientBoundary)
    ; normalizedFirstLocalPrerequisiteBlockerIsSourcedDStarFBoundary =
        refl
    ; quotientGaugeOrbitEquivalenceConstructed =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.realGaugeOrbitEquivalenceConstructed
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; quotientGaugeOrbitEquivalenceConstructedIsFalse =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.realGaugeOrbitEquivalenceConstructedIsFalse
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; quotientDenseDomainConstructed =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.denseDomainConstructed
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; quotientDenseDomainConstructedIsFalse =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.denseDomainConstructedIsFalse
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; quotientSymmetricOnDenseDomainConstructed =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.symmetricOnDenseDomainConstructed
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; quotientSymmetricOnDenseDomainConstructedIsFalse =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.symmetricOnDenseDomainConstructedIsFalse
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; quotientSelfAdjointExtensionConstructed =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.selfAdjointExtensionConstructed
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; quotientSelfAdjointExtensionConstructedIsFalse =
        Sourced.YMHamiltonianQuotientPrerequisiteBundle.selfAdjointExtensionConstructedIsFalse
          Sourced.canonicalYMHamiltonianQuotientPrerequisiteBundle
    ; natToRealTransition =
        NatSlice.canonicalS8NatToRealPhysicalCarrierTransitionReceipt
    ; natToRealTransitionCanonical =
        true
    ; natToRealTransitionCanonicalIsTrue =
        refl
    ; lower6RealCarrierBlocker =
        NatSlice.canonicalS8Lower6RealCarrierAndHamiltonianBlockerReceipt
    ; lower6RealCarrierBlockerCanonical =
        true
    ; lower6RealCarrierBlockerCanonicalIsTrue =
        refl
    ; conditionalFiniteCarrierWiring =
        NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; conditionalFiniteCarrierWiringCanonical =
        true
    ; conditionalFiniteCarrierWiringCanonicalIsTrue =
        refl
    ; realNonNatCarrierStaging =
        S8.canonicalS8RealNonNatCarrierStagingReceipt
    ; realNonNatCarrierStagingCanonical =
        true
    ; realNonNatCarrierStagingCanonicalIsTrue =
        refl
    ; selfAdjointBlockerReceipt =
        S8.canonicalS8SelfAdjointHamiltonianBlockerReceipt
    ; selfAdjointBlockerReceiptCanonical =
        true
    ; selfAdjointBlockerReceiptCanonicalIsTrue =
        refl
    ; realYMCarrierQuotientAudit =
        S8.canonicalS8RealYMCarrierQuotientImplementationAudit
    ; realYMCarrierQuotientAuditCanonical =
        true
    ; realYMCarrierQuotientAuditCanonicalIsTrue =
        refl
    ; l6RealCarrierQuotientFailClosed =
        S8.canonicalL6RealCarrierQuotientFailClosedReceipt
    ; l6RealCarrierQuotientFailClosedCanonical =
        true
    ; l6RealCarrierQuotientFailClosedCanonicalIsTrue =
        refl
    ; stoneHamiltonianGapBridge =
        Hamiltonian.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; stoneHamiltonianGapBridgeCanonical =
        true
    ; stoneHamiltonianGapBridgeCanonicalIsTrue =
        refl
    ; selectedCarrierLowerBound =
        Hamiltonian.canonicalSelectedCarrierSpectralLowerBoundReceipt
    ; selectedCarrierLowerBoundCanonical =
        true
    ; selectedCarrierLowerBoundCanonicalIsTrue =
        refl
    ; gate2ColimitGapLift =
        Hamiltonian.canonicalGate2ColimitGapLiftReceipt
    ; gate2ColimitGapLiftCanonical =
        true
    ; gate2ColimitGapLiftCanonicalIsTrue =
        refl
    ; boundedNatCarrierTheoremAvailable =
        true
    ; boundedNatCarrierTheoremAvailableIsTrue =
        refl
    ; realCarrierTheoremConstructed =
        NatSlice.S8Lower6RealCarrierAndHamiltonianBlockerReceipt.realCarrierTheoremConstructed
          NatSlice.canonicalS8Lower6RealCarrierAndHamiltonianBlockerReceipt
    ; realCarrierTheoremConstructedIsFalse =
        NatSlice.S8Lower6RealCarrierAndHamiltonianBlockerReceipt.realCarrierTheoremConstructedIsFalse
          NatSlice.canonicalS8Lower6RealCarrierAndHamiltonianBlockerReceipt
    ; realYMCarrierQuotientConstructed =
        S8.L6RealCarrierQuotientFailClosedReceipt.realCarrierQuotientConstructed
          S8.canonicalL6RealCarrierQuotientFailClosedReceipt
    ; realYMCarrierQuotientConstructedIsFalse =
        S8.L6RealCarrierQuotientFailClosedReceipt.realCarrierQuotientConstructedIsFalse
          S8.canonicalL6RealCarrierQuotientFailClosedReceipt
    ; selfAdjointYangMillsHamiltonianConstructed =
        S8.L6RealCarrierQuotientFailClosedReceipt.selfAdjointYangMillsHamiltonianConstructed
          S8.canonicalL6RealCarrierQuotientFailClosedReceipt
    ; selfAdjointYangMillsHamiltonianConstructedIsFalse =
        S8.L6RealCarrierQuotientFailClosedReceipt.selfAdjointYangMillsHamiltonianConstructedIsFalse
          S8.canonicalL6RealCarrierQuotientFailClosedReceipt
    ; stoneGeneratorIdentifiedWithPhysicalYMHamiltonian =
        Hamiltonian.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.stoneGeneratorIsPhysicalYMHamiltonian
          Hamiltonian.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; stoneGeneratorIdentifiedWithPhysicalYMHamiltonianIsFalse =
        Hamiltonian.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.stoneGeneratorIsPhysicalYMHamiltonianIsFalse
          Hamiltonian.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; finiteCarrierBoundTransportedToRealYM =
        NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYM
          NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; finiteCarrierBoundTransportedToRealYMIsFalse =
        NatSlice.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYMIsFalse
          NatSlice.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; exactFirstBlocker =
        S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; exactFirstBlockerIsMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient =
        refl
    ; exactFirstTheoremField =
        S8.s8SelfAdjointHamiltonianOnCarrierQuotientField
    ; exactFirstTheoremFieldIsSelfAdjointHamiltonian =
        refl
    ; exactHardExternalHalt =
        S8.uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; exactHardExternalHaltIsUniformBalabanOrAgawa =
        refl
    ; normalizedRequirementClasses =
        canonicalYMSelfAdjointHamiltonianRequirementClasses
    ; normalizedRequirementClassesAreCanonical =
        refl
    ; normalizedRequirementClassCount =
        5
    ; normalizedRequirementClassCountIs5 =
        refl
    ; normalizedBlockers =
        canonicalYMSelfAdjointHamiltonianNormalizedBlockers
    ; normalizedBlockersAreCanonical =
        refl
    ; normalizedBlockerCount =
        6
    ; normalizedBlockerCountIs6 =
        refl
    ; rows =
        canonicalYMSelfAdjointHamiltonianRequirementRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        17
    ; rowCountIs17 =
        refl
    ; hamiltonianTheoremPromoted =
        false
    ; hamiltonianTheoremPromotedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; normalizedBoundary =
        "The sourced-equation boundary feeds the Hamiltonian quotient interface but does not construct it"
        ∷ "The consumed real sourced D * F boundary package has a typed boundary target, while physical real D * F = J remains false"
        ∷ "The prerequisite bundle narrows the first local blocker to sourced D * F still being a boundary package before quotient/domain/self-adjointness transport"
        ∷ "Gauge-orbit equivalence, dense domain, symmetric dense Hamiltonian, and self-adjoint extension are exposed as concrete false prerequisite fields"
        ∷ "The bounded Nat carrier theorem is available only as bounded Nat evidence"
        ∷ "The Nat-to-real transition and lower6 blocker keep the real carrier theorem false"
        ∷ "The Stone bridge records finite/local generator and selected lower-bound surfaces without identifying them with H_YM"
        ∷ "The real quotient implementation audit still lacks YMConnectionCarrier modulo gauge, operator, dense domain, symmetry, and self-adjointness data"
        ∷ "The normalized first blocker is missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "The normalized first theorem field is s8SelfAdjointHamiltonianOnCarrierQuotientField"
        ∷ "No Hamiltonian theorem, spectral gap, Clay Yang-Mills, or terminal promotion is constructed"
        ∷ []
    }

canonicalYMSelfAdjointHamiltonianRequirementRowCountIs17 :
  listCount canonicalYMSelfAdjointHamiltonianRequirementRows ≡ 17
canonicalYMSelfAdjointHamiltonianRequirementRowCountIs17 =
  refl

canonicalYMSelfAdjointHamiltonianRequirementClassCountIs5 :
  listCount canonicalYMSelfAdjointHamiltonianRequirementClasses ≡ 5
canonicalYMSelfAdjointHamiltonianRequirementClassCountIs5 =
  refl

canonicalYMSelfAdjointHamiltonianNormalizedBlockerCountIs6 :
  listCount canonicalYMSelfAdjointHamiltonianNormalizedBlockers ≡ 6
canonicalYMSelfAdjointHamiltonianNormalizedBlockerCountIs6 =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerSourcedDStarFTyped :
  sourcedDStarFBoundaryTyped
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  true
canonicalYMSelfAdjointHamiltonianNormalizerSourcedDStarFTyped =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerPhysicalRealDStarFFalse :
  physicalRealDStarFEqualsJPromoted
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerPhysicalRealDStarFFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerFirstLocalBlocker :
  normalizedFirstLocalPrerequisiteBlocker
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  sourcedDStarFPackageStillBoundaryBlocker
canonicalYMSelfAdjointHamiltonianNormalizerFirstLocalBlocker =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerGaugeOrbitFalse :
  quotientGaugeOrbitEquivalenceConstructed
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerGaugeOrbitFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerDenseDomainFalse :
  quotientDenseDomainConstructed
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerDenseDomainFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerSelfAdjointExtensionFalse :
  quotientSelfAdjointExtensionConstructed
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerSelfAdjointExtensionFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerFirstBlocker :
  exactFirstBlocker
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
canonicalYMSelfAdjointHamiltonianNormalizerFirstBlocker =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerFirstTheoremField :
  exactFirstTheoremField
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  S8.s8SelfAdjointHamiltonianOnCarrierQuotientField
canonicalYMSelfAdjointHamiltonianNormalizerFirstTheoremField =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerHardHalt :
  exactHardExternalHalt
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  S8.uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
canonicalYMSelfAdjointHamiltonianNormalizerHardHalt =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerRealCarrierTheoremFalse :
  realCarrierTheoremConstructed
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerRealCarrierTheoremFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerRealQuotientFalse :
  realYMCarrierQuotientConstructed
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerRealQuotientFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerSelfAdjointHamiltonianFalse :
  selfAdjointYangMillsHamiltonianConstructed
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerSelfAdjointHamiltonianFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerFiniteBoundNotTransported :
  finiteCarrierBoundTransportedToRealYM
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerFiniteBoundNotTransported =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerHamiltonianTheoremFalse :
  hamiltonianTheoremPromoted
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerHamiltonianTheoremFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerSpectralGapFalse :
  spectralGapPromoted
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerSpectralGapFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerClayFalse :
  clayYangMillsPromoted
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerClayFalse =
  refl

canonicalYMSelfAdjointHamiltonianNormalizerTerminalFalse :
  terminalPromotion
    canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
  ≡
  false
canonicalYMSelfAdjointHamiltonianNormalizerTerminalFalse =
  refl
