module DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiveHessianDominationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
-- Relationship: background covariant Hessian and propagator perturbations.
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042
-- Relationship: nonlinear block-average derivative and path transport.
--
-- DASHI contribution: the five global remainder estimates are reduced below to
-- finite local pointwise bounds plus literal four-dimensional incidence maps.
------------------------------------------------------------------------

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ values) = value + sumℚ values

record LocalRemainderFamily (Background State Cell : Set) : Set₁ where
  field
    cells : Background → List Cell
    localRemainder localNormCharge :
      Background → State → Cell → ℚ
    radius globalNormSq localCoefficient : Background → State → ℚ

    globalRemainder : Background → State → ℚ
    globalRemainderDefinition : ∀ background state →
      globalRemainder background state
      ≡ sumℚ
          (mapLocalRemainder background state (cells background))

    mapLocalRemainder : Background → State → List Cell → List ℚ
    mapLocalRemainderEmpty : ∀ background state →
      mapLocalRemainder background state [] ≡ []
    mapLocalRemainderStep : ∀ background state cell rest →
      mapLocalRemainder background state (cell ∷ rest)
      ≡ localRemainder background state cell
        ∷ mapLocalRemainder background state rest

    mapLocalNorm : Background → State → List Cell → List ℚ
    mapLocalNormEmpty : ∀ background state →
      mapLocalNorm background state [] ≡ []
    mapLocalNormStep : ∀ background state cell rest →
      mapLocalNorm background state (cell ∷ rest)
      ≡ localNormCharge background state cell
        ∷ mapLocalNorm background state rest

    pointwiseLocalBound : ∀ background state cell →
      localRemainder background state cell
      ≤ localCoefficient background state
        * radius background state
        * localNormCharge background state cell

    finiteSumPointwiseBound : ∀ background state →
      sumℚ (mapLocalRemainder background state (cells background))
      ≤ localCoefficient background state
        * radius background state
        * sumℚ (mapLocalNorm background state (cells background))

    incidenceNormBound : ∀ background state →
      sumℚ (mapLocalNorm background state (cells background))
      ≤ globalNormSq background state

    coefficientTimesIncidenceMonotone : ∀ background state →
      sumℚ (mapLocalNorm background state (cells background))
      ≤ globalNormSq background state →
      localCoefficient background state * radius background state
        * sumℚ (mapLocalNorm background state (cells background))
      ≤ localCoefficient background state * radius background state
        * globalNormSq background state

    transitive : ∀ {left middle right : ℚ} →
      left ≤ middle → middle ≤ right → left ≤ right

open LocalRemainderFamily public

localRemainderGlobalBound :
  ∀ {Background State Cell}
    (dataSet : LocalRemainderFamily Background State Cell)
    background state →
  globalRemainder dataSet background state
  ≤ localCoefficient dataSet background state
      * radius dataSet background state
      * globalNormSq dataSet background state
localRemainderGlobalBound dataSet background state =
  subst
    (λ lower → lower
      ≤ localCoefficient dataSet background state
        * radius dataSet background state
        * globalNormSq dataSet background state)
    (globalRemainderDefinition dataSet background state)
    (transitive dataSet
      (finiteSumPointwiseBound dataSet background state)
      (coefficientTimesIncidenceMonotone dataSet background state
        (incidenceNormBound dataSet background state)))

record LiteralFiveHessianLocalData
    (Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell : Set) : Set₁ where
  field
    BackgroundInConfiguredRadius : Background → Set
    configuredRadius normSq : Background → State → ℚ

    curvature : LocalRemainderFamily Background State CurvatureCell
    transport : LocalRemainderFamily Background State TransportCell
    chart : LocalRemainderFamily Background State ChartCell
    gauge : LocalRemainderFamily Background State GaugeCell
    constraint : LocalRemainderFamily Background State ConstraintCell

    commonRadiusCurvature : ∀ background state →
      radius curvature background state ≡ configuredRadius background state
    commonRadiusTransport : ∀ background state →
      radius transport background state ≡ configuredRadius background state
    commonRadiusChart : ∀ background state →
      radius chart background state ≡ configuredRadius background state
    commonRadiusGauge : ∀ background state →
      radius gauge background state ≡ configuredRadius background state
    commonRadiusConstraint : ∀ background state →
      radius constraint background state ≡ configuredRadius background state

    commonNormCurvature : ∀ background state →
      globalNormSq curvature background state ≡ normSq background state
    commonNormTransport : ∀ background state →
      globalNormSq transport background state ≡ normSq background state
    commonNormChart : ∀ background state →
      globalNormSq chart background state ≡ normSq background state
    commonNormGauge : ∀ background state →
      globalNormSq gauge background state ≡ normSq background state
    commonNormConstraint : ∀ background state →
      globalNormSq constraint background state ≡ normSq background state

    curvatureCoefficientExact : ∀ background state →
      localCoefficient curvature background state
      ≡ Constants.configuredCurvatureCoefficient
    transportCoefficientExact : ∀ background state →
      localCoefficient transport background state
      ≡ Constants.configuredTransportCoefficient
    chartCoefficientExact : ∀ background state →
      localCoefficient chart background state
      ≡ Constants.configuredChartCoefficient
    gaugeCoefficientExact : ∀ background state →
      localCoefficient gauge background state
      ≡ Constants.configuredGaugeCoefficient
    constraintCoefficientExact : ∀ background state →
      localCoefficient constraint background state
      ≡ Constants.configuredConstraintCoefficient

    totalRemainder : Background → State → ℚ
    totalRemainderDefinition : ∀ background state →
      totalRemainder background state
      ≡ globalRemainder curvature background state
        + (globalRemainder transport background state
        + (globalRemainder chart background state
        + (globalRemainder gauge background state
        + globalRemainder constraint background state)))

    addMonotone : ∀ {a b c d : ℚ} → a ≤ b → c ≤ d → a + c ≤ b + d

    configuredUpperSumExact : ∀ background state →
      Constants.configuredCurvatureCoefficient * configuredRadius background state
        * normSq background state
      + (Constants.configuredTransportCoefficient * configuredRadius background state
        * normSq background state
      + (Constants.configuredChartCoefficient * configuredRadius background state
        * normSq background state
      + (Constants.configuredGaugeCoefficient * configuredRadius background state
        * normSq background state
      + Constants.configuredConstraintCoefficient * configuredRadius background state
        * normSq background state)))
      ≡ Constants.configuredTotalCoefficient * configuredRadius background state
        * normSq background state

open LiteralFiveHessianLocalData public

curvatureRemainderPointwiseBoundLiteral = pointwiseLocalBound ∘ curvature
  where open import Function using (_∘_)
transportedDifferenceMinusDifferenceBoundLiteral = pointwiseLocalBound ∘ transport
  where open import Function using (_∘_)
chartMetricDifferenceQuadraticBoundLiteral = pointwiseLocalBound ∘ chart
  where open import Function using (_∘_)
covariantDivergencePerturbationBoundLiteral = pointwiseLocalBound ∘ gauge
  where open import Function using (_∘_)
blockDerivativeDifferencePointwiseBoundLiteral = pointwiseLocalBound ∘ constraint
  where open import Function using (_∘_)

asConfiguredFiveRemainderDomination :
  ∀ {Background State CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell} →
  LiteralFiveHessianLocalData Background State CurvatureCell TransportCell
    ChartCell GaugeCell ConstraintCell →
  Constants.ConfiguredFiveRemainderDomination Background State
asConfiguredFiveRemainderDomination dataSet = record
  { radius = configuredRadius dataSet
  ; normSq = normSq dataSet
  ; curvatureRemainder = globalRemainder (curvature dataSet)
  ; transportRemainder = globalRemainder (transport dataSet)
  ; chartRemainder = globalRemainder (chart dataSet)
  ; gaugeRemainder = globalRemainder (gauge dataSet)
  ; constraintRemainder = globalRemainder (constraint dataSet)
  ; BackgroundInConfiguredRadius = BackgroundInConfiguredRadius dataSet
  ; curvatureDominated = λ background state inRadius →
      subst
        (λ coefficient → globalRemainder (curvature dataSet) background state
          ≤ coefficient * configuredRadius dataSet background state
            * normSq dataSet background state)
        (curvatureCoefficientExact dataSet background state)
        (subst
          (λ radiusValue → globalRemainder (curvature dataSet) background state
            ≤ localCoefficient (curvature dataSet) background state
              * radiusValue * normSq dataSet background state)
          (commonRadiusCurvature dataSet background state)
          (subst
            (λ normValue → globalRemainder (curvature dataSet) background state
              ≤ localCoefficient (curvature dataSet) background state
                * radius (curvature dataSet) background state * normValue)
            (commonNormCurvature dataSet background state)
            (localRemainderGlobalBound (curvature dataSet) background state)))
  ; transportDominated = λ background state inRadius →
      subst
        (λ coefficient → globalRemainder (transport dataSet) background state
          ≤ coefficient * configuredRadius dataSet background state
            * normSq dataSet background state)
        (transportCoefficientExact dataSet background state)
        (subst
          (λ radiusValue → globalRemainder (transport dataSet) background state
            ≤ localCoefficient (transport dataSet) background state
              * radiusValue * normSq dataSet background state)
          (commonRadiusTransport dataSet background state)
          (subst
            (λ normValue → globalRemainder (transport dataSet) background state
              ≤ localCoefficient (transport dataSet) background state
                * radius (transport dataSet) background state * normValue)
            (commonNormTransport dataSet background state)
            (localRemainderGlobalBound (transport dataSet) background state)))
  ; chartDominated = λ background state inRadius →
      subst
        (λ coefficient → globalRemainder (chart dataSet) background state
          ≤ coefficient * configuredRadius dataSet background state
            * normSq dataSet background state)
        (chartCoefficientExact dataSet background state)
        (subst
          (λ radiusValue → globalRemainder (chart dataSet) background state
            ≤ localCoefficient (chart dataSet) background state
              * radiusValue * normSq dataSet background state)
          (commonRadiusChart dataSet background state)
          (subst
            (λ normValue → globalRemainder (chart dataSet) background state
              ≤ localCoefficient (chart dataSet) background state
                * radius (chart dataSet) background state * normValue)
            (commonNormChart dataSet background state)
            (localRemainderGlobalBound (chart dataSet) background state)))
  ; gaugeDominated = λ background state inRadius →
      subst
        (λ coefficient → globalRemainder (gauge dataSet) background state
          ≤ coefficient * configuredRadius dataSet background state
            * normSq dataSet background state)
        (gaugeCoefficientExact dataSet background state)
        (subst
          (λ radiusValue → globalRemainder (gauge dataSet) background state
            ≤ localCoefficient (gauge dataSet) background state
              * radiusValue * normSq dataSet background state)
          (commonRadiusGauge dataSet background state)
          (subst
            (λ normValue → globalRemainder (gauge dataSet) background state
              ≤ localCoefficient (gauge dataSet) background state
                * radius (gauge dataSet) background state * normValue)
            (commonNormGauge dataSet background state)
            (localRemainderGlobalBound (gauge dataSet) background state)))
  ; constraintDominated = λ background state inRadius →
      subst
        (λ coefficient → globalRemainder (constraint dataSet) background state
          ≤ coefficient * configuredRadius dataSet background state
            * normSq dataSet background state)
        (constraintCoefficientExact dataSet background state)
        (subst
          (λ radiusValue → globalRemainder (constraint dataSet) background state
            ≤ localCoefficient (constraint dataSet) background state
              * radiusValue * normSq dataSet background state)
          (commonRadiusConstraint dataSet background state)
          (subst
            (λ normValue → globalRemainder (constraint dataSet) background state
              ≤ localCoefficient (constraint dataSet) background state
                * radius (constraint dataSet) background state * normValue)
            (commonNormConstraint dataSet background state)
            (localRemainderGlobalBound (constraint dataSet) background state)))
  ; totalRemainder = totalRemainder dataSet
  ; totalRemainderDefinition = totalRemainderDefinition dataSet
  ; addMonotone = addMonotone dataSet
  ; configuredUpperSumExact = configuredUpperSumExact dataSet
  }

localToGlobalRemainderReductionLevel : ProofLevel
localToGlobalRemainderReductionLevel = machineChecked

fiveConfiguredDominationAdapterLevel : ProofLevel
fiveConfiguredDominationAdapterLevel = machineChecked

literalLocalPointwiseAndIncidenceInputsLevel : ProofLevel
literalLocalPointwiseAndIncidenceInputsLevel = conditional
