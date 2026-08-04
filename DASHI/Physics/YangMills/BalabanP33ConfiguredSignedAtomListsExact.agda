module DASHI.Physics.YangMills.BalabanP33ConfiguredSignedAtomListsExact where

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
-- DASHI CONTRIBUTION
--
-- Consume the repository's exact 18/8/4/16/16 atom lists with the signed atom
-- induction.  The output is the same five-channel P33 theorem used by the
-- concrete bond-cell model, but finite summation and sign transport are now
-- derived for the physically named curvature, transport, chart, gauge and
-- block-constraint atom decompositions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiniteAtomListsExact as Atoms
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33SignedFiniteAtomExpansionExact as SignedAtoms
import DASHI.Physics.YangMills.BalabanP33FiniteSignedRemainderSummationExact as Signed
import DASHI.Physics.YangMills.BalabanP33FiveChannelPath4CoercivityExact as Five
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge

record ConfiguredFiveSignedAtomData
    (Background CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell : Set) : Set₂ where
  field
    curvatureLocal : SignedAtoms.SignedFixedAtomExpansion
      Background Hodge.RationalBondField4 CurvatureCell
      Atoms.CurvatureAtom Atoms.curvatureAtoms Atoms.curvatureCoefficient
    transportLocal : SignedAtoms.SignedFixedAtomExpansion
      Background Hodge.RationalBondField4 TransportCell
      Atoms.TransportAtom Atoms.transportAtoms Atoms.transportCoefficient
    chartLocal : SignedAtoms.SignedFixedAtomExpansion
      Background Hodge.RationalBondField4 ChartCell
      Atoms.ChartAtom Atoms.chartAtoms Atoms.chartCoefficient
    gaugeLocal : SignedAtoms.SignedFixedAtomExpansion
      Background Hodge.RationalBondField4 GaugeCell
      Atoms.GaugeAtom Atoms.gaugeAtoms Atoms.gaugeCoefficient
    constraintLocal : SignedAtoms.SignedFixedAtomExpansion
      Background Hodge.RationalBondField4 ConstraintCell
      Atoms.ConstraintAtom Atoms.constraintAtoms Atoms.constraintCoefficient

    curvatureGlobal : SignedAtoms.SignedAtomFamilyGlobalization
      Background Hodge.RationalBondField4 CurvatureCell
      Atoms.CurvatureAtom Atoms.curvatureAtoms Atoms.curvatureCoefficient
      curvatureLocal
    transportGlobal : SignedAtoms.SignedAtomFamilyGlobalization
      Background Hodge.RationalBondField4 TransportCell
      Atoms.TransportAtom Atoms.transportAtoms Atoms.transportCoefficient
      transportLocal
    chartGlobal : SignedAtoms.SignedAtomFamilyGlobalization
      Background Hodge.RationalBondField4 ChartCell
      Atoms.ChartAtom Atoms.chartAtoms Atoms.chartCoefficient
      chartLocal
    gaugeGlobal : SignedAtoms.SignedAtomFamilyGlobalization
      Background Hodge.RationalBondField4 GaugeCell
      Atoms.GaugeAtom Atoms.gaugeAtoms Atoms.gaugeCoefficient
      gaugeLocal
    constraintGlobal : SignedAtoms.SignedAtomFamilyGlobalization
      Background Hodge.RationalBondField4 ConstraintCell
      Atoms.ConstraintAtom Atoms.constraintAtoms Atoms.constraintCoefficient
      constraintLocal

    sharedRadius : Background → Hodge.RationalBondField4 → ℚ

    curvatureRadiusExact : ∀ background state →
      SignedAtoms.commonRadius curvatureGlobal background state
      ≡ sharedRadius background state
    transportRadiusExact : ∀ background state →
      SignedAtoms.commonRadius transportGlobal background state
      ≡ sharedRadius background state
    chartRadiusExact : ∀ background state →
      SignedAtoms.commonRadius chartGlobal background state
      ≡ sharedRadius background state
    gaugeRadiusExact : ∀ background state →
      SignedAtoms.commonRadius gaugeGlobal background state
      ≡ sharedRadius background state
    constraintRadiusExact : ∀ background state →
      SignedAtoms.commonRadius constraintGlobal background state
      ≡ sharedRadius background state

    curvatureNormExact : ∀ background state →
      SignedAtoms.globalNormSq curvatureGlobal background state
      ≡ Hodge.bondNormSq state
    transportNormExact : ∀ background state →
      SignedAtoms.globalNormSq transportGlobal background state
      ≡ Hodge.bondNormSq state
    chartNormExact : ∀ background state →
      SignedAtoms.globalNormSq chartGlobal background state
      ≡ Hodge.bondNormSq state
    gaugeNormExact : ∀ background state →
      SignedAtoms.globalNormSq gaugeGlobal background state
      ≡ Hodge.bondNormSq state
    constraintNormExact : ∀ background state →
      SignedAtoms.globalNormSq constraintGlobal background state
      ≡ Hodge.bondNormSq state

    sharedRadiusIsConfigured : ∀ background state →
      sharedRadius background state ≡ P33.p33SmallFieldRadius

open ConfiguredFiveSignedAtomData public

curvatureFamily :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  ConfiguredFiveSignedAtomData
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Signed.FiniteSignedRemainderFamily
    Background Hodge.RationalBondField4 CurvatureCell
curvatureFamily dataSet =
  SignedAtoms.asFiniteSignedRemainderFamily
    (curvatureGlobal dataSet)

transportFamily :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  ConfiguredFiveSignedAtomData
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Signed.FiniteSignedRemainderFamily
    Background Hodge.RationalBondField4 TransportCell
transportFamily dataSet =
  SignedAtoms.asFiniteSignedRemainderFamily
    (transportGlobal dataSet)

chartFamily :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  ConfiguredFiveSignedAtomData
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Signed.FiniteSignedRemainderFamily
    Background Hodge.RationalBondField4 ChartCell
chartFamily dataSet =
  SignedAtoms.asFiniteSignedRemainderFamily
    (chartGlobal dataSet)

gaugeFamily :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  ConfiguredFiveSignedAtomData
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Signed.FiniteSignedRemainderFamily
    Background Hodge.RationalBondField4 GaugeCell
gaugeFamily dataSet =
  SignedAtoms.asFiniteSignedRemainderFamily
    (gaugeGlobal dataSet)

constraintFamily :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  ConfiguredFiveSignedAtomData
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Signed.FiniteSignedRemainderFamily
    Background Hodge.RationalBondField4 ConstraintCell
constraintFamily dataSet =
  SignedAtoms.asFiniteSignedRemainderFamily
    (constraintGlobal dataSet)

asFiveChannelPath4Data :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  ConfiguredFiveSignedAtomData
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Five.FiveChannelPath4Data
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell
asFiveChannelPath4Data dataSet = record
  { Five.FiveChannelPath4Data.curvature = curvatureFamily dataSet
  ; Five.FiveChannelPath4Data.transport = transportFamily dataSet
  ; Five.FiveChannelPath4Data.chart = chartFamily dataSet
  ; Five.FiveChannelPath4Data.gauge = gaugeFamily dataSet
  ; Five.FiveChannelPath4Data.constraint = constraintFamily dataSet
  ; Five.FiveChannelPath4Data.radius = sharedRadius dataSet
  ; Five.FiveChannelPath4Data.curvatureWeightExact =
      λ background state →
        cong
          (λ selectedRadius →
            Constants.configuredCurvatureCoefficient * selectedRadius)
          (curvatureRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.transportWeightExact =
      λ background state →
        cong
          (λ selectedRadius →
            Constants.configuredTransportCoefficient * selectedRadius)
          (transportRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.chartWeightExact =
      λ background state →
        cong
          (λ selectedRadius →
            Constants.configuredChartCoefficient * selectedRadius)
          (chartRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.gaugeWeightExact =
      λ background state →
        cong
          (λ selectedRadius →
            Constants.configuredGaugeCoefficient * selectedRadius)
          (gaugeRadiusExact dataSet background state)
  ; Five.FiveChannelPath4Data.constraintWeightExact =
      λ background state →
        cong
          (λ selectedRadius →
            Constants.configuredConstraintCoefficient * selectedRadius)
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
      sharedRadiusIsConfigured dataSet
  }

configuredSignedAtomsGivePath4PhysicalCoercivity :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : ConfiguredFiveSignedAtomData
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
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
configuredSignedAtomsGivePath4PhysicalCoercivity
    dataSet background state gaugeFixingEnergy blockPenaltyEnergy
    meanZero gaugeNonnegative blockNonnegative =
  Five.fiveLocalChannelsGivePath4PhysicalCoercivity
    (asFiveChannelPath4Data dataSet)
    background state gaugeFixingEnergy blockPenaltyEnergy
    meanZero gaugeNonnegative blockNonnegative

configuredSignedAtomListLevel : ProofLevel
configuredSignedAtomListLevel = machineChecked

configuredFiveSignedAtomAssemblyLevel : ProofLevel
configuredFiveSignedAtomAssemblyLevel = machineChecked

configuredSignedAtomsToP33FloorLevel : ProofLevel
configuredSignedAtomsToP33FloorLevel = machineChecked
