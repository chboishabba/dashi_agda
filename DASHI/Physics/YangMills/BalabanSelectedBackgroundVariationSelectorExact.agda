module DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories". DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Replace the vague instruction "use the Euler--Lagrange equation" by the
-- exact local selector interface needed by Gate I.  A selector must produce a
-- gauge-admissible, constraint-tangent, local physical test variation whose
-- first variation extracts the literal four-singleton Wilson part plus a
-- classified spillover.  The reducer proves that a spillover budget of
-- 55/18874368 times the cross charge gives the sharp singleton lower bound.
--
-- This module does not fabricate the selector.  It connects any actual
-- construction to the already closed pair/deep estimates, physical W-local,
-- and the existing terminal coercivity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact as Split
import DASHI.Physics.YangMills.BalabanP33PhysicalPairDeepLowerExact as FiniteAtoms
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact as Coeff
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as Instantiation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Coercivity
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

remainingSingletonCoefficient : ℚ
remainingSingletonCoefficient = + 55 / 18874368

remainingPlusPairIsCorrelated :
  remainingSingletonCoefficient + Coeff.rho * (+ 1 / 256)
  ≡ Wilson.rhoOverThirtySix
remainingPlusPairIsCorrelated = ℚRing.solve []

record SingletonExtractionWitness
    (background : Physical.RationalSU2Background4)
    (fieldValue : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₁ where
  field
    FineVariation : Set
    variation : FineVariation

    GaugeAdmissible : FineVariation → Set
    ConstraintTangent : FineVariation → Set
    SupportedNearPlaquette : FineVariation → Set

    gaugeAdmissible : GaugeAdmissible variation
    constraintTangent : ConstraintTangent variation
    localSupport : SupportedNearPlaquette variation

    variationNormSq : FineVariation → ℚ
    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant
    variationChargeBound :
      variationNormSq variation
      ≤ selectorConstant * Wilson.plaquetteCrossCharge fieldValue plaquette

    firstVariation : FineVariation → ℚ
    extractionSpillover : ℚ

    selectedEulerLagrangeStationary : firstVariation variation ≡ 0ℚ
    extractsLiteralSingleton :
      firstVariation variation
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background fieldValue plaquette
        + extractionSpillover

    spilloverUpper :
      extractionSpillover
      ≤ remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge fieldValue plaquette

open SingletonExtractionWitness public

sumZeroImpliesLeftIsNegativeRight : ∀ left right →
  left + right ≡ 0ℚ → left ≡ - right
sumZeroImpliesLeftIsNegativeRight left right sumZero =
  trans
    (sym (ℚRing.solve-∀ left right))
    (trans
      (cong (λ value → value - right) sumZero)
      (ℚRing.solve-∀ right))

selectedBackgroundSingletonCurvatureLower :
  ∀ {background fieldValue plaquette} →
  SingletonExtractionWitness background fieldValue plaquette →
  - (remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge fieldValue plaquette)
  ≤ Partition.physicalPlaquetteWilsonLinearPart
      background fieldValue plaquette
selectedBackgroundSingletonCurvatureLower {background} {fieldValue} {plaquette} witness =
  let
    singleton = Partition.physicalPlaquetteWilsonLinearPart
      background fieldValue plaquette
    spill = extractionSpillover witness
    balance : singleton + spill ≡ 0ℚ
    balance = trans
      (sym (extractsLiteralSingleton witness))
      (selectedEulerLagrangeStationary witness)
    singletonExact : singleton ≡ - spill
    singletonExact = sumZeroImpliesLeftIsNegativeRight singleton spill balance
    reflected = ℚP.neg-mono-≤ (spilloverUpper witness)
  in
  subst
    (λ upper →
      - (remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge fieldValue plaquette)
      ≤ upper)
    (sym singletonExact)
    reflected

physicalCorrelatedIsSingletonPlusPair : ∀ background fieldValue plaquette →
  Partition.physicalPlaquetteWilsonLinearPart background fieldValue plaquette
    + FiniteAtoms.physicalPlaquettePairWilsonPart background fieldValue plaquette
  ≡ Split.physicalPlaquetteCorrelatedWilsonPart background fieldValue plaquette
physicalCorrelatedIsSingletonPlusPair background fieldValue plaquette =
  sym (Partition.sumMapPointwiseAdd
    Placement.plaquetteSecondVariationPlacements4
    (Partition.placementLinearWilsonPart background fieldValue plaquette)
    (FiniteAtoms.placementPairWilsonPart background fieldValue plaquette))

casePlaquettePairLower :
  ∀ background fieldValue plaquette →
  Radius.RelaxedInverseLinkRadius background →
  - ((Coeff.rho * (+ 1 / 256))
      * Wilson.plaquetteCrossCharge fieldValue plaquette)
  ≤ FiniteAtoms.physicalPlaquettePairWilsonPart background fieldValue plaquette
casePlaquettePairLower background fieldValue (pair site axes) radius =
  subst
    (λ lower → lower ≤
      FiniteAtoms.physicalPlaquettePairWilsonPart
        background fieldValue (pair site axes))
    (ℚRing.solve-∀ Coeff.rho
      (Wilson.plaquetteCrossCharge fieldValue (pair site axes)))
    (FiniteAtoms.physicalPairWilsonLower background fieldValue site axes radius)

selectedBackgroundCorrelatedWilsonLower :
  ∀ {background fieldValue plaquette} →
  Radius.RelaxedInverseLinkRadius background →
  SingletonExtractionWitness background fieldValue plaquette →
  - (Wilson.rhoOverThirtySix
      * Wilson.plaquetteCrossCharge fieldValue plaquette)
  ≤ Split.physicalPlaquetteCorrelatedWilsonPart background fieldValue plaquette
selectedBackgroundCorrelatedWilsonLower {background} {fieldValue} {plaquette}
    radius witness =
  let
    singletonLower = selectedBackgroundSingletonCurvatureLower witness
    pairLower = casePlaquettePairLower background fieldValue plaquette radius
    summed = ℚP.+-mono-≤ singletonLower pairLower
    lowerExact :
      - (remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge fieldValue plaquette)
      + - ((Coeff.rho * (+ 1 / 256))
          * Wilson.plaquetteCrossCharge fieldValue plaquette)
      ≡ - (Wilson.rhoOverThirtySix
          * Wilson.plaquetteCrossCharge fieldValue plaquette)
    lowerExact = ℚRing.solve-∀
      (Wilson.plaquetteCrossCharge fieldValue plaquette)
  in
  subst
    (λ lower → lower ≤
      Split.physicalPlaquetteCorrelatedWilsonPart background fieldValue plaquette)
    lowerExact
    (subst
      (λ upper →
        - (remainingSingletonCoefficient
            * Wilson.plaquetteCrossCharge fieldValue plaquette)
        + - ((Coeff.rho * (+ 1 / 256))
            * Wilson.plaquetteCrossCharge fieldValue plaquette)
        ≤ upper)
      (physicalCorrelatedIsSingletonPlusPair background fieldValue plaquette)
      summed)

record SelectedBackgroundVariationSelector
    (background : Physical.RationalSU2Background4)
    (fieldValue : Coordinates.PhysicalSU2BondField4) : Set₁ where
  field
    select : ∀ plaquette →
      SingletonExtractionWitness background fieldValue plaquette

open SelectedBackgroundVariationSelector public

selectorAndRadiusGiveRefinedBounds :
  ∀ {background fieldValue} →
  Radius.RelaxedInverseLinkRadius background →
  SelectedBackgroundVariationSelector background fieldValue →
  Split.RefinedCanonicalPhysicalWilsonBounds background fieldValue
selectorAndRadiusGiveRefinedBounds {background} {fieldValue} radius selector = record
  { Split.RefinedCanonicalPhysicalWilsonBounds.correlatedLower =
      λ plaquette →
        selectedBackgroundCorrelatedWilsonLower radius (select selector plaquette)
  ; Split.RefinedCanonicalPhysicalWilsonBounds.deepRemainderLower =
      λ { (pair site axes) →
        FiniteAtoms.physicalDeepWilsonRemainderLower
          background fieldValue site axes radius }
  }

selectorAndRadiusGivePhysicalWLocal :
  ∀ {background fieldValue} →
  Radius.RelaxedInverseLinkRadius background →
  SelectedBackgroundVariationSelector background fieldValue →
  Wilson.PhysicalWilsonSignedLocal background fieldValue
selectorAndRadiusGivePhysicalWLocal radius selector =
  Split.refinedBoundsImplyWLocal
    (selectorAndRadiusGiveRefinedBounds radius selector)

selectedVariationalSelectorOneThirtySecond :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : Instantiation.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (Instantiation.bridge inputs)) coarse}
    (family : Instantiation.SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h →
  SelectedBackgroundVariationSelector
    (Coercivity.backgroundOf (Instantiation.model family) h)
    (Coercivity.physicalFieldOf (Instantiation.model family) h) →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation
        (Instantiation.model family) h)
selectedVariationalSelectorOneThirtySecond family h selector =
  Split.selectedVariationalRefinedOneThirtySecond
    family h
    (selectorAndRadiusGiveRefinedBounds
      (Instantiation.selectedVariationalRadiusAt family h)
      selector)

record VariationSelectorBoundary : Set where
  constructor variationSelectorBoundary
  field
    selectorReducerConnectedToLiteralSingleton : Bool
    selectorReducerConnectedToLiteralSingletonIsTrue :
      selectorReducerConnectedToLiteralSingleton ≡ true

    pairAndDeepFiniteChannelsClosed : Bool
    pairAndDeepFiniteChannelsClosedIsTrue :
      pairAndDeepFiniteChannelsClosed ≡ true

    actualSelectedPlaquetteVariationConstructed : Bool
    actualSelectedPlaquetteVariationConstructedIsFalse :
      actualSelectedPlaquetteVariationConstructed ≡ false

    selectedEulerLagrangeSpilloverBoundProved : Bool
    selectedEulerLagrangeSpilloverBoundProvedIsFalse :
      selectedEulerLagrangeSpilloverBoundProved ≡ false

canonicalVariationSelectorBoundary : VariationSelectorBoundary
canonicalVariationSelectorBoundary =
  variationSelectorBoundary true refl true refl false refl false refl

variationSelectorReducerLevel : ProofLevel
variationSelectorReducerLevel = machineChecked

actualSelectedVariationLevel : ProofLevel
actualSelectedVariationLevel = conditional
