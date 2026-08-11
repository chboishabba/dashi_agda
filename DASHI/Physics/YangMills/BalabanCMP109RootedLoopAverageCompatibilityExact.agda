module DASHI.Physics.YangMills.BalabanCMP109RootedLoopAverageCompatibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Prove the first genuinely source-exact nonlinear compatibility between the
-- constructed rooted gauge section and Bałaban's group-valued averaging.
--
-- On a single coarse periodic block every coarse contour is a loop based at
-- the unique coarse/root site.  For a fine field U, use the already-constructed
-- rooted gauge
--
--     g_U(x) = transport_U(base -> x).
--
-- The path-gauge theorem gives g_U(base)=1.  Literal path transport covariance
-- gives, for each based loop p,
--
--     hol_{U^{g_U}}(p)
--       = g_U(base) hol_U(p) g_U(base)^-1.
--
-- Bałaban's bi-translation law for the CMP109 group average then yields
--
--     M({hol_{U^{g_U}}(p)}) = M({hol_U(p)}).
--
-- Thus root evaluation really is the coarse restriction on the source-exact
-- equation-(0.11) contour average in the one-block setting; it is no longer an
-- arbitrary `restrictGauge` socket.  The remaining nonlinear compatibility is
-- the propagation of this contour identity through the full equation-(0.12)
-- transported-log/exponential block map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using (LatticePath4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact as Average

record RootedLoopAverageData
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (rootedPaths : Rooted.RootedPathSystem base)
    (Lie Scalar : Set)
    (averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar)
    : Set₁ where
  field
    loops : List (LatticePath4 {N} base base)

    loopHolonomiesSmallDiameter :
      ∀ gaugeField →
      Average.SmallDiameter averageAxioms
        (Average.mapList
          (λ path →
            Covariance.directedPathTransport group gaugeField path)
          loops)

open RootedLoopAverageData public

rootedLoopGaugeFamily :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (rootedPaths : Rooted.RootedPathSystem base)
    {Lie Scalar : Set}
    {averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar} →
  RootedLoopAverageData group rootedPaths Lie Scalar averageAxioms →
  Average.GaugeCovariantPathFamily
    (Covariance.DirectedGaugeField4 N group)
    (LatticePath4 {N} base base)
    (Transport.Carrier group) Lie Scalar averageAxioms
rootedLoopGaugeFamily group {base = base} rootedPaths dataSet = record
  { Average.GaugeCovariantPathFamily.paths = loops dataSet
  ; Average.GaugeCovariantPathFamily.holonomy =
      λ gaugeField path →
        Covariance.directedPathTransport group gaugeField path
  ; Average.GaugeCovariantPathFamily.transformedHolonomy =
      λ gaugeField path →
        let gauge = Rooted.rootedGaugeFunction group rootedPaths gaugeField in
        Covariance.directedPathTransport group
          (Covariance.gaugeTransformBond group gauge gaugeField) path
  ; Average.GaugeCovariantPathFamily.leftGauge =
      λ gaugeField →
        Rooted.rootedGaugeFunction group rootedPaths gaugeField base
  ; Average.GaugeCovariantPathFamily.rightGauge =
      λ gaugeField →
        Transport.inverse group
          (Rooted.rootedGaugeFunction group rootedPaths gaugeField base)
  ; Average.GaugeCovariantPathFamily.transformedHolonomyGaugeCovariant =
      λ gaugeField path →
        Covariance.pathTransportGaugeCovariant
          group
          (Rooted.rootedGaugeFunction group rootedPaths gaugeField)
          gaugeField path
  ; Average.GaugeCovariantPathFamily.pathFamilySmallDiameter =
      loopHolonomiesSmallDiameter dataSet
  }

rootedLoopAverage :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (rootedPaths : Rooted.RootedPathSystem base)
    {Lie Scalar : Set}
    {averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar} →
  RootedLoopAverageData group rootedPaths Lie Scalar averageAxioms →
  Covariance.DirectedGaugeField4 N group → Transport.Carrier group
rootedLoopAverage group rootedPaths dataSet =
  Average.averagedContour (rootedLoopGaugeFamily group rootedPaths dataSet)

rootedTransformedLoopAverage :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (rootedPaths : Rooted.RootedPathSystem base)
    {Lie Scalar : Set}
    {averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar} →
  RootedLoopAverageData group rootedPaths Lie Scalar averageAxioms →
  Covariance.DirectedGaugeField4 N group → Transport.Carrier group
rootedTransformedLoopAverage group rootedPaths dataSet =
  Average.transformedAveragedContour
    (rootedLoopGaugeFamily group rootedPaths dataSet)

inverseUnitExact :
  ∀ (group : Transport.GroupStructure) →
  Transport.inverse group (Transport.unit group) ≡ Transport.unit group
inverseUnitExact group =
  trans
    (sym (Transport.unitRight group (Transport.inverse group (Transport.unit group))))
    (Transport.inverseLeft group (Transport.unit group))

rootedLoopAveragePreserved :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (rootedPaths : Rooted.RootedPathSystem base)
    {Lie Scalar : Set}
    {averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar}
    (dataSet : RootedLoopAverageData
      group rootedPaths Lie Scalar averageAxioms)
    (gaugeField : Covariance.DirectedGaugeField4 N group) →
  rootedTransformedLoopAverage group rootedPaths dataSet gaugeField
  ≡ rootedLoopAverage group rootedPaths dataSet gaugeField
rootedLoopAveragePreserved
    group {base = base} rootedPaths
    {averageAxioms = averageAxioms} dataSet gaugeField =
  let
    family = rootedLoopGaugeFamily group rootedPaths dataSet
    gauge = Rooted.rootedGaugeFunction group rootedPaths gaugeField
    based : gauge base ≡ Transport.unit group
    based = Rooted.rootedGaugeFunctionBased group rootedPaths gaugeField
    averageValue = rootedLoopAverage group rootedPaths dataSet gaugeField

    covariance = Average.averagedContourGaugeCovariant family gaugeField

    leftExact : Average.leftGauge family gaugeField ≡ Transport.unit group
    leftExact = based

    rightExact : Average.rightGauge family gaugeField ≡ Transport.unit group
    rightExact =
      trans
        (cong (Transport.inverse group) based)
        (inverseUnitExact group)
  in
  trans covariance
    (trans
      (cong
        (λ leftValue →
          Transport.multiply group leftValue
            (Transport.multiply group averageValue
              (Average.rightGauge family gaugeField)))
        leftExact)
      (trans
        (cong
          (Transport.multiply group (Transport.unit group))
          (cong
            (Transport.multiply group averageValue)
            rightExact))
        (trans
          (Transport.unitLeft group
            (Transport.multiply group averageValue (Transport.unit group)))
          (Transport.unitRight group averageValue))))

cmp109RootedLoopPathCovarianceLevel : ProofLevel
cmp109RootedLoopPathCovarianceLevel = machineChecked

cmp109RootedLoopAverageCompatibilityLevel : ProofLevel
cmp109RootedLoopAverageCompatibilityLevel = machineChecked

cmp109Equation012RootedCompatibilityStillRequiredLevel : ProofLevel
cmp109Equation012RootedCompatibilityStillRequiredLevel = conditional
