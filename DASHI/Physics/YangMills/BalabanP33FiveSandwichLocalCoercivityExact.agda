module DASHI.Physics.YangMills.BalabanP33FiveSandwichLocalCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Assemble five physically factorized local operator channels directly into
-- the P33 coercivity theorem.  Each local function is the actual sandwich
--
--   R_i,c(A,v) = <u_i,c,E_i,c(A)u_i,c> q_i,c(v),
--
-- with its signed estimate derived from the operator norm and its incidence
-- estimate carried by the literal local charge.  The exact coefficient and
-- radius identifications then yield the 1/32 floor without passing through an
-- unnamed global remainder premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33SandwichLocalFamilyExact as Local
import DASHI.Physics.YangMills.BalabanP33FiniteSignedRemainderSummationExact as Signed
import DASHI.Physics.YangMills.BalabanP33FiveChannelPath4CoercivityExact as Five
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge

record FiveSandwichLocalData
    (CurvatureOperator CurvatureLocalState CurvatureCell
      TransportOperator TransportLocalState TransportCell
      ChartOperator ChartLocalState ChartCell
      GaugeOperator GaugeLocalState GaugeCell
      ConstraintOperator ConstraintLocalState ConstraintCell
      Background : Set) : Set₂ where
  field
    curvature : Local.SandwichLocalFamilyData
      CurvatureOperator CurvatureLocalState Background
      Hodge.RationalBondField4 CurvatureCell
    transport : Local.SandwichLocalFamilyData
      TransportOperator TransportLocalState Background
      Hodge.RationalBondField4 TransportCell
    chart : Local.SandwichLocalFamilyData
      ChartOperator ChartLocalState Background
      Hodge.RationalBondField4 ChartCell
    gauge : Local.SandwichLocalFamilyData
      GaugeOperator GaugeLocalState Background
      Hodge.RationalBondField4 GaugeCell
    constraint : Local.SandwichLocalFamilyData
      ConstraintOperator ConstraintLocalState Background
      Hodge.RationalBondField4 ConstraintCell

    sharedRadius : Background → Hodge.RationalBondField4 → ℚ

    curvatureCoefficientExact :
      Local.coefficient curvature ≡ Constants.configuredCurvatureCoefficient
    transportCoefficientExact :
      Local.coefficient transport ≡ Constants.configuredTransportCoefficient
    chartCoefficientExact :
      Local.coefficient chart ≡ Constants.configuredChartCoefficient
    gaugeCoefficientExact :
      Local.coefficient gauge ≡ Constants.configuredGaugeCoefficient
    constraintCoefficientExact :
      Local.coefficient constraint ≡ Constants.configuredConstraintCoefficient

    curvatureRadiusExact : ∀ background state →
      Local.radius curvature background state ≡ sharedRadius background state
    transportRadiusExact : ∀ background state →
      Local.radius transport background state ≡ sharedRadius background state
    chartRadiusExact : ∀ background state →
      Local.radius chart background state ≡ sharedRadius background state
    gaugeRadiusExact : ∀ background state →
      Local.radius gauge background state ≡ sharedRadius background state
    constraintRadiusExact : ∀ background state →
      Local.radius constraint background state ≡ sharedRadius background state

    curvatureNormExact : ∀ background state →
      Local.globalNormSq curvature background state ≡ Hodge.bondNormSq state
    transportNormExact : ∀ background state →
      Local.globalNormSq transport background state ≡ Hodge.bondNormSq state
    chartNormExact : ∀ background state →
      Local.globalNormSq chart background state ≡ Hodge.bondNormSq state
    gaugeNormExact : ∀ background state →
      Local.globalNormSq gauge background state ≡ Hodge.bondNormSq state
    constraintNormExact : ∀ background state →
      Local.globalNormSq constraint background state ≡ Hodge.bondNormSq state

    radiusIsConfigured : ∀ background state →
      sharedRadius background state ≡ P33.p33SmallFieldRadius

open FiveSandwichLocalData public

asFiveChannelPath4Data :
  ∀ {CurvatureOperator CurvatureLocalState CurvatureCell
      TransportOperator TransportLocalState TransportCell
      ChartOperator ChartLocalState ChartCell
      GaugeOperator GaugeLocalState GaugeCell
      ConstraintOperator ConstraintLocalState ConstraintCell Background} →
  FiveSandwichLocalData
    CurvatureOperator CurvatureLocalState CurvatureCell
    TransportOperator TransportLocalState TransportCell
    ChartOperator ChartLocalState ChartCell
    GaugeOperator GaugeLocalState GaugeCell
    ConstraintOperator ConstraintLocalState ConstraintCell
    Background →
  Five.FiveChannelPath4Data
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell
asFiveChannelPath4Data dataSet = record
  { Five.FiveChannelPath4Data.curvature =
      Local.asFiniteSignedRemainderFamily (curvature dataSet)
  ; Five.FiveChannelPath4Data.transport =
      Local.asFiniteSignedRemainderFamily (transport dataSet)
  ; Five.FiveChannelPath4Data.chart =
      Local.asFiniteSignedRemainderFamily (chart dataSet)
  ; Five.FiveChannelPath4Data.gauge =
      Local.asFiniteSignedRemainderFamily (gauge dataSet)
  ; Five.FiveChannelPath4Data.constraint =
      Local.asFiniteSignedRemainderFamily (constraint dataSet)
  ; Five.FiveChannelPath4Data.radius = sharedRadius dataSet
  ; Five.FiveChannelPath4Data.curvatureWeightExact =
      λ background state → cong₂ _*_
        (curvatureCoefficientExact dataSet)
        (curvatureRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.transportWeightExact =
      λ background state → cong₂ _*_
        (transportCoefficientExact dataSet)
        (transportRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.chartWeightExact =
      λ background state → cong₂ _*_
        (chartCoefficientExact dataSet)
        (chartRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.gaugeWeightExact =
      λ background state → cong₂ _*_
        (gaugeCoefficientExact dataSet)
        (gaugeRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.constraintWeightExact =
      λ background state → cong₂ _*_
        (constraintCoefficientExact dataSet)
        (constraintRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.curvatureNormExact =
      curvatureNormExact dataSet
  ; Five.FiveChannelPath4Data.transportNormExact =
      transportNormExact dataSet
  ; Five.FiveChannelPath4Data.chartNormExact =
      chartNormExact dataSet
  ; Five.FiveChannelPath4Data.gaugeNormExact =
      gaugeNormExact dataSet
  ; Five.FiveChannelPath4Data.constraintNormExact =
      constraintNormExact dataSet
  ; Five.FiveChannelPath4Data.radiusIsConfigured =
      radiusIsConfigured dataSet
  }

fiveSandwichLocalChannelsGiveP33Floor :
  ∀ {CurvatureOperator CurvatureLocalState CurvatureCell
      TransportOperator TransportLocalState TransportCell
      ChartOperator ChartLocalState ChartCell
      GaugeOperator GaugeLocalState GaugeCell
      ConstraintOperator ConstraintLocalState ConstraintCell Background}
    (dataSet : FiveSandwichLocalData
      CurvatureOperator CurvatureLocalState CurvatureCell
      TransportOperator TransportLocalState TransportCell
      ChartOperator ChartLocalState ChartCell
      GaugeOperator GaugeLocalState GaugeCell
      ConstraintOperator ConstraintLocalState ConstraintCell
      Background)
    background state gaugeFixingEnergy blockPenaltyEnergy →
  Hodge.BondComponentMeanZero state →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  P33.p33PhysicalFloor * Hodge.bondNormSq state
  ≤ P33.physicalHessianEnergy
      (Hodge.referenceHodgeEnergy
        state gaugeFixingEnergy blockPenaltyEnergy)
      (Five.totalSignedRemainder
        (asFiveChannelPath4Data dataSet) background state)
fiveSandwichLocalChannelsGiveP33Floor
    dataSet background state gaugeFixingEnergy blockPenaltyEnergy
    meanZero gaugeNonnegative blockNonnegative =
  Five.fiveLocalChannelsGivePath4PhysicalCoercivity
    (asFiveChannelPath4Data dataSet)
    background state gaugeFixingEnergy blockPenaltyEnergy
    meanZero gaugeNonnegative blockNonnegative

fiveSandwichLocalAssemblyLevel : ProofLevel
fiveSandwichLocalAssemblyLevel = machineChecked

fiveSandwichLocalToP33FloorLevel : ProofLevel
fiveSandwichLocalToP33FloorLevel = machineChecked
