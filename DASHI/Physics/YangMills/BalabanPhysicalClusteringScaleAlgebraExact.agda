module DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Discharge the dimensional algebra hidden by the old `exponentConversion`
-- field. Let a be the physical lattice spacing, aInv its reciprocal, mu the
-- dimensionless lattice localization exponent and m the target physical mass.
-- From
--
--       a * aInv = 1,
--       m <= aInv * mu,
--
-- exact ordered rational algebra gives
--
--       m * a <= mu.
--
-- If latticeDistance = aInv * physicalDistance, then for every nonnegative
-- physical distance d,
--
--       m*d <= mu*latticeDistance.
--
-- Thus a lattice bound exp(-mu*d_lattice) has at least physical decay rate m;
-- the only remaining analytic step is the standard antitonicity of exp(-x).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record PhysicalScaleData : Set₁ where
  field
    latticeSpacing inverseSpacing latticeExponent physicalMass : ℚ

    spacingNonnegative : 0ℚ ≤ latticeSpacing
    inverseSpacingNonnegative : 0ℚ ≤ inverseSpacing
    latticeExponentNonnegative : 0ℚ ≤ latticeExponent
    physicalMassNonnegative : 0ℚ ≤ physicalMass

    spacingInverseExact : latticeSpacing * inverseSpacing ≡ 1ℚ
    physicalMassFloor :
      physicalMass ≤ inverseSpacing * latticeExponent

open PhysicalScaleData public

physicalMassTimesSpacingBelowLatticeExponent :
  (dataSet : PhysicalScaleData) →
  physicalMass dataSet * latticeSpacing dataSet
  ≤ latticeExponent dataSet
physicalMassTimesSpacingBelowLatticeExponent dataSet =
  let
    a = latticeSpacing dataSet
    aInv = inverseSpacing dataSet
    mu = latticeExponent dataSet
    mass = physicalMass dataSet

    scaled : a * mass ≤ a * (aInv * mu)
    scaled = Norm.scaleNonnegative
      a (spacingNonnegative dataSet) (physicalMassFloor dataSet)

    leftCommutes : a * mass ≡ mass * a
    leftCommutes = ℚP.*-comm a mass

    reassociate : a * (aInv * mu) ≡ (a * aInv) * mu
    reassociate = ℚRing.solve-∀ a aInv mu

    reciprocalCollapse : (a * aInv) * mu ≡ mu
    reciprocalCollapse =
      subst
        (λ product → product * mu ≡ mu)
        (sym (spacingInverseExact dataSet))
        (ℚRing.solve-∀ mu)

    rightCollapses : a * (aInv * mu) ≡ mu
    rightCollapses = trans reassociate reciprocalCollapse
  in
  subst
    (λ lower → lower ≤ mu)
    leftCommutes
    (subst
      (λ upper → a * mass ≤ upper)
      rightCollapses
      scaled)

latticeDistance : PhysicalScaleData → ℚ → ℚ
latticeDistance dataSet physicalDistance =
  inverseSpacing dataSet * physicalDistance

latticeExponentPhysicalDistanceIdentity :
  (dataSet : PhysicalScaleData) physicalDistance →
  latticeExponent dataSet * latticeDistance dataSet physicalDistance
  ≡ (inverseSpacing dataSet * latticeExponent dataSet) * physicalDistance
latticeExponentPhysicalDistanceIdentity dataSet physicalDistance =
  ℚRing.solve-∀
    (inverseSpacing dataSet)
    (latticeExponent dataSet)
    physicalDistance

physicalExponentDominatedByLatticeExponent :
  (dataSet : PhysicalScaleData) physicalDistance →
  0ℚ ≤ physicalDistance →
  physicalMass dataSet * physicalDistance
  ≤ latticeExponent dataSet * latticeDistance dataSet physicalDistance
physicalExponentDominatedByLatticeExponent dataSet physicalDistance distanceNN =
  let
    coefficientBound = physicalMassFloor dataSet
    scaled :
      physicalDistance * physicalMass dataSet
      ≤ physicalDistance
          * (inverseSpacing dataSet * latticeExponent dataSet)
    scaled = Norm.scaleNonnegative physicalDistance distanceNN coefficientBound

    leftCommutes :
      physicalDistance * physicalMass dataSet
      ≡ physicalMass dataSet * physicalDistance
    leftCommutes = ℚP.*-comm physicalDistance (physicalMass dataSet)

    rightCommutes :
      physicalDistance
        * (inverseSpacing dataSet * latticeExponent dataSet)
      ≡ (inverseSpacing dataSet * latticeExponent dataSet)
        * physicalDistance
    rightCommutes = ℚP.*-comm
      physicalDistance
      (inverseSpacing dataSet * latticeExponent dataSet)

    latticeIdentity =
      latticeExponentPhysicalDistanceIdentity dataSet physicalDistance
  in
  subst
    (λ lower → lower
      ≤ latticeExponent dataSet * latticeDistance dataSet physicalDistance)
    leftCommutes
    (subst
      (λ upper →
        physicalDistance * physicalMass dataSet ≤ upper)
      (sym latticeIdentity)
      (subst
        (λ upper →
          physicalDistance * physicalMass dataSet ≤ upper)
        rightCommutes
        scaled))

physicalClusteringSpacingConversionLevel : ProofLevel
physicalClusteringSpacingConversionLevel = machineChecked

physicalClusteringExponentConversionLevel : ProofLevel
physicalClusteringExponentConversionLevel = machineChecked
