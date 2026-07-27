module DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042
--
-- Timothy D. Barfoot, "State Estimation for Robotics", Cambridge University
-- Press (2017). DOI: 10.1017/9781316671528
--
-- Relationship: the source papers motivate the five geometric mechanisms.  The
-- allocation below is deliberately conservative: it allows the plaquette and
-- divergence incidence counts, Young inequalities and length-four block paths
-- to be charged before the physical estimate is compared with the budget.
------------------------------------------------------------------------

twoℚ fourℚ sixℚ eightℚ sixteenℚ thirtyTwoℚ sixtyFourℚ : ℚ
twoℚ = 1ℚ + 1ℚ
fourℚ = twoℚ + twoℚ
sixℚ = fourℚ + twoℚ
eightℚ = fourℚ + fourℚ
sixteenℚ = eightℚ + eightℚ
thirtyTwoℚ = sixteenℚ + sixteenℚ
sixtyFourℚ = thirtyTwoℚ + thirtyTwoℚ

oneHundredTwentyEightℚ twoHundredFiftySixℚ : ℚ
oneHundredTwentyEightℚ = sixtyFourℚ + sixtyFourℚ
twoHundredFiftySixℚ = oneHundredTwentyEightℚ + oneHundredTwentyEightℚ

configuredCurvatureCoefficient : ℚ
configuredCurvatureCoefficient = thirtyTwoℚ

configuredTransportCoefficient : ℚ
configuredTransportCoefficient = sixtyFourℚ

configuredChartCoefficient : ℚ
configuredChartCoefficient = thirtyTwoℚ

configuredGaugeCoefficient : ℚ
configuredGaugeCoefficient = sixtyFourℚ

configuredConstraintCoefficient : ℚ
configuredConstraintCoefficient = sixtyFourℚ

configuredTotalCoefficient : ℚ
configuredTotalCoefficient =
  configuredCurvatureCoefficient
  + (configuredTransportCoefficient
  + (configuredChartCoefficient
  + (configuredGaugeCoefficient
  + configuredConstraintCoefficient)))

configuredTotalCoefficientExact :
  configuredTotalCoefficient ≡ twoHundredFiftySixℚ
configuredTotalCoefficientExact = ℚRing.solve

------------------------------------------------------------------------
-- Literal four-dimensional incidence data.
------------------------------------------------------------------------

oneN twoN fourN sixN eightN sixteenN : Nat
oneN = suc zero
twoN = suc oneN
fourN = suc (suc twoN)
sixN = suc (suc fourN)
eightN = suc (suc sixN)
sixteenN = suc (suc (suc (suc (suc (suc (suc (suc eightN)))))))

-- Each positive-axis edge belongs to two plaquettes with each of the other
-- three axes: 2(4-1)=6.
plaquettesPerPositiveEdge4D : Nat
plaquettesPerPositiveEdge4D = sixN

-- Four incoming and four outgoing oriented bonds meet a site.
orientedEdgesPerSite4D : Nat
orientedEdgesPerSite4D = eightN

-- A monotone path across the Boolean 4-cell flips at most four coordinates.
boolean4CanonicalPathLength : Nat
boolean4CanonicalPathLength = fourN

-- The Boolean 4-cell has sixteen sites and four positive bond components.
boolean4SiteCount : Nat
boolean4SiteCount = sixteenN

bondComponentsPerBoolean4Block : Nat
bondComponentsPerBoolean4Block = fourN

------------------------------------------------------------------------
-- Physical domination record.
------------------------------------------------------------------------

record ConfiguredFiveRemainderDomination
    (Background State : Set) : Set₁ where
  field
    radius normSq : Background → State → ℚ
    curvatureRemainder transportRemainder chartRemainder
      gaugeRemainder constraintRemainder : Background → State → ℚ

    BackgroundInConfiguredRadius : Background → Set

    curvatureDominated : ∀ background state →
      BackgroundInConfiguredRadius background →
      curvatureRemainder background state
      ≤ configuredCurvatureCoefficient * radius background state
        * normSq background state

    transportDominated : ∀ background state →
      BackgroundInConfiguredRadius background →
      transportRemainder background state
      ≤ configuredTransportCoefficient * radius background state
        * normSq background state

    chartDominated : ∀ background state →
      BackgroundInConfiguredRadius background →
      chartRemainder background state
      ≤ configuredChartCoefficient * radius background state
        * normSq background state

    gaugeDominated : ∀ background state →
      BackgroundInConfiguredRadius background →
      gaugeRemainder background state
      ≤ configuredGaugeCoefficient * radius background state
        * normSq background state

    constraintDominated : ∀ background state →
      BackgroundInConfiguredRadius background →
      constraintRemainder background state
      ≤ configuredConstraintCoefficient * radius background state
        * normSq background state

    totalRemainder : Background → State → ℚ
    totalRemainderDefinition : ∀ background state →
      totalRemainder background state
      ≡ curvatureRemainder background state
        + (transportRemainder background state
        + (chartRemainder background state
        + (gaugeRemainder background state
        + constraintRemainder background state)))

    addMonotone : ∀ {a b c d : ℚ} → a ≤ b → c ≤ d → a + c ≤ b + d

    configuredUpperSumExact : ∀ background state →
      configuredCurvatureCoefficient * radius background state * normSq background state
      + (configuredTransportCoefficient * radius background state * normSq background state
      + (configuredChartCoefficient * radius background state * normSq background state
      + (configuredGaugeCoefficient * radius background state * normSq background state
      + configuredConstraintCoefficient * radius background state * normSq background state)))
      ≡ configuredTotalCoefficient * radius background state * normSq background state

open ConfiguredFiveRemainderDomination public

configuredFiveRemainderSumBound :
  ∀ {Background State}
    (dataSet : ConfiguredFiveRemainderDomination Background State)
    background state →
  BackgroundInConfiguredRadius dataSet background →
  totalRemainder dataSet background state
  ≤ configuredTotalCoefficient
      * radius dataSet background state
      * normSq dataSet background state
configuredFiveRemainderSumBound dataSet background state inRadius =
  subst
    (λ value → totalRemainder dataSet background state ≤ value)
    (configuredUpperSumExact dataSet background state)
    (subst
      (λ value → value
        ≤ configuredCurvatureCoefficient
            * radius dataSet background state
            * normSq dataSet background state
          + (configuredTransportCoefficient
              * radius dataSet background state
              * normSq dataSet background state
          + (configuredChartCoefficient
              * radius dataSet background state
              * normSq dataSet background state
          + (configuredGaugeCoefficient
              * radius dataSet background state
              * normSq dataSet background state
          + configuredConstraintCoefficient
              * radius dataSet background state
              * normSq dataSet background state))))
      (totalRemainderDefinition dataSet background state)
      (addMonotone dataSet
        (curvatureDominated dataSet background state inRadius)
        (addMonotone dataSet
          (transportDominated dataSet background state inRadius)
          (addMonotone dataSet
            (chartDominated dataSet background state inRadius)
            (addMonotone dataSet
              (gaugeDominated dataSet background state inRadius)
              (constraintDominated dataSet background state inRadius))))))

configuredIncidenceDataLevel : ProofLevel
configuredIncidenceDataLevel = machineChecked

configuredCoefficientArithmeticLevel : ProofLevel
configuredCoefficientArithmeticLevel = machineChecked

literalConfiguredRemainderDominationInputsLevel : ProofLevel
literalConfiguredRemainderDominationInputsLevel = conditional
