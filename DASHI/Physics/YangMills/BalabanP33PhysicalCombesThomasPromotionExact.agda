module DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Attach the generic Combes--Thomas conjugation calculus to the repository's
-- literal 3072-coordinate side-four SU(2) carrier.  The module proves two
-- concrete promotions.
--
-- First, a support-graph shell theorem plus one scalar distortion budget gives
-- the literal tilted-Hessian row estimate
--
--   sum_y |(D H D^-1-H)(x,y)| <= 1/64.
--
-- The proof treats zero Hessian entries separately, so shell control is needed
-- only on the actual stencil support.
--
-- Second, a bounded tilted inverse gives the physical Green-kernel estimate
--
--   |G(root,target)| <= 64 * t^d(root,target).
--
-- where t is the reciprocal geometric base.  The inverse relation of H and G
-- is transported exactly through the diagonal conjugation.  No collar M=21,
-- support count N=3072, or local-parametrix residual is used in this route.
--
-- The remaining physical producers are stated honestly in the records below:
-- a support-graph description of the literal Hessian stencil, its absolute row
-- mass, and the norm-to-entry estimate for the tilted inverse obtained from the
-- half-gap coercivity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _-_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact as Tilt
import DASHI.Physics.YangMills.BalabanP33RationalGeometricCombesThomasWeightExact as Geo
import DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact as Survival

Coordinate : Set
Coordinate = Physical.PhysicalSU2Coordinate4

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

------------------------------------------------------------------------
-- Physical support-graph geometry and exact tilt row budget.
------------------------------------------------------------------------

record PhysicalCombesThomasGeometry
    (hessian : PhysicalMatrix) : Set₁ where
  field
    distance : Coordinate → Coordinate → Nat
    root : Coordinate

    base inverseBase distortion rowMass : ℚ

    reciprocalBase : base * inverseBase ≡ + 1 / 1
    rootDistanceZero : distance root root ≡ 0

    inverseBaseNonnegative : 0ℚ ≤ inverseBase
    inverseBaseAbsolute : ∣ inverseBase ∣ ≡ inverseBase
    distortionNonnegative : 0ℚ ≤ distortion
    baseDistortion : ∣ base - (+ 1 / 1) ∣ ≤ distortion
    inverseBaseDistortion :
      ∣ inverseBase - (+ 1 / 1) ∣ ≤ distortion

    supportedShell : ∀ left right →
      (hessian left right ≡ 0ℚ)
      ⊎
      Geo.UnitShellRelation
        (distance root left)
        (distance root right)

    hessianAbsoluteRowMass : ∀ left →
      Tilt.absoluteRowMass
        Physical.physicalSU2Coordinates4 hessian left
      ≤ rowMass

    scalarTiltBudget :
      distortion * rowMass ≤ Tilt.p33HalfGap

open PhysicalCombesThomasGeometry public

physicalWeight :
  ∀ {hessian} →
  PhysicalCombesThomasGeometry hessian → Coordinate → ℚ
physicalWeight geometry =
  Geo.rootedWeight
    (distance geometry)
    (inverseBase geometry)
    (root geometry)

physicalInverseWeight :
  ∀ {hessian} →
  PhysicalCombesThomasGeometry hessian → Coordinate → ℚ
physicalInverseWeight geometry =
  Geo.rootedInverseWeight
    (distance geometry)
    (base geometry)
    (root geometry)

physicalWeightInverseLaw :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    coordinate →
  physicalInverseWeight geometry coordinate
    * physicalWeight geometry coordinate
  ≡ + 1 / 1
physicalWeightInverseLaw geometry coordinate =
  Geo.rootedWeightInverseLaw
    (distance geometry)
    (base geometry)
    (inverseBase geometry)
    (reciprocalBase geometry)
    (root geometry)
    coordinate

physicalWeightInverseLawCommuted :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    coordinate →
  physicalWeight geometry coordinate
    * physicalInverseWeight geometry coordinate
  ≡ + 1 / 1
physicalWeightInverseLawCommuted geometry coordinate =
  trans
    (ℚP.*-comm
      (physicalWeight geometry coordinate)
      (physicalInverseWeight geometry coordinate))
    (physicalWeightInverseLaw geometry coordinate)

physicalInverseWeightAtRoot :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian) →
  physicalInverseWeight geometry (root geometry) ≡ + 1 / 1
physicalInverseWeightAtRoot geometry =
  Geo.rootedInverseAtRoot
    (distance geometry)
    (base geometry)
    (root geometry)
    (rootDistanceZero geometry)

physicalWeightNonnegative :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    coordinate →
  0ℚ ≤ physicalWeight geometry coordinate
physicalWeightNonnegative geometry coordinate =
  Geo.rootedWeightNonnegative
    (distance geometry)
    (inverseBase geometry)
    (inverseBaseNonnegative geometry)
    (root geometry)
    coordinate

physicalWeightAbsolute :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    coordinate →
  ∣ physicalWeight geometry coordinate ∣
  ≡ physicalWeight geometry coordinate
physicalWeightAbsolute geometry coordinate =
  Geo.rootedWeightAbsolute
    (distance geometry)
    (inverseBase geometry)
    (inverseBaseAbsolute geometry)
    (root geometry)
    coordinate

physicalIdentityStable :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    left right →
  CT.diagonalConjugate
    (physicalWeight geometry)
    (physicalInverseWeight geometry)
    Calibration.identityEntry left right
  ≡ Calibration.identityEntry left right
physicalIdentityStable geometry left right
  with Calibration.physicalCoordinateDecidableEquality left right
... | yes refl
  rewrite physicalWeightInverseLawCommuted geometry left =
  ℚRing.solve []
... | no _ = ℚRing.solve []

physicalSupportedRatioBound :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    left right →
  Geo.UnitShellRelation
    (distance geometry (root geometry) left)
    (distance geometry (root geometry) right) →
  ∣ physicalWeight geometry left
      * physicalInverseWeight geometry right
      - (+ 1 / 1) ∣
  ≤ distortion geometry
physicalSupportedRatioBound geometry left right relation =
  Geo.unitShellDistortionBound
    (base geometry)
    (inverseBase geometry)
    (distortion geometry)
    (reciprocalBase geometry)
    (distortionNonnegative geometry)
    (baseDistortion geometry)
    (inverseBaseDistortion geometry)
    relation

physicalTiltDefectEntryBound :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    left right →
  ∣ CT.diagonalTiltDefect
      (physicalWeight geometry)
      (physicalInverseWeight geometry)
      hessian left right ∣
  ≤ distortion geometry * ∣ hessian left right ∣
physicalTiltDefectEntryBound {hessian} geometry left right
  with supportedShell geometry left right
... | inj₁ zeroEntry
  rewrite zeroEntry = ℚP.≤-refl
... | inj₂ shellRelation =
  Tilt.tiltDefectEntryAbsoluteBound
    (physicalWeight geometry)
    (physicalInverseWeight geometry)
    hessian
    (distortion geometry)
    left right
    (physicalSupportedRatioBound
      geometry left right shellRelation)

physicalTiltDefectRowMassBound :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    left →
  Tilt.tiltDefectAbsoluteRowMass
    Physical.physicalSU2Coordinates4
    (physicalWeight geometry)
    (physicalInverseWeight geometry)
    hessian left
  ≤ distortion geometry
      * Tilt.absoluteRowMass
          Physical.physicalSU2Coordinates4 hessian left
physicalTiltDefectRowMassBound {hessian} geometry left =
  subst
    (λ upper →
      Tilt.tiltDefectAbsoluteRowMass
        Physical.physicalSU2Coordinates4
        (physicalWeight geometry)
        (physicalInverseWeight geometry)
        hessian left
      ≤ upper)
    (Tilt.sumScale
      Physical.physicalSU2Coordinates4
      (distortion geometry)
      (λ right → ∣ hessian left right ∣))
    (Tilt.sumPointwiseBelow
      Physical.physicalSU2Coordinates4
      (λ right →
        ∣ CT.diagonalTiltDefect
            (physicalWeight geometry)
            (physicalInverseWeight geometry)
            hessian left right ∣)
      (λ right → distortion geometry * ∣ hessian left right ∣)
      (physicalTiltDefectEntryBound geometry left))

physicalTiltDefectBelowHalfGap :
  ∀ {hessian}
    (geometry : PhysicalCombesThomasGeometry hessian)
    left →
  Tilt.tiltDefectAbsoluteRowMass
    Physical.physicalSU2Coordinates4
    (physicalWeight geometry)
    (physicalInverseWeight geometry)
    hessian left
  ≤ Tilt.p33HalfGap
physicalTiltDefectBelowHalfGap geometry left =
  let
    instance
      distortionNN : NonNegative (distortion geometry)
      distortionNN = ℚ.nonNegative (distortionNonnegative geometry)
  in
  ℚP.≤-trans
    (physicalTiltDefectRowMassBound geometry left)
    (ℚP.≤-trans
      (ℚP.*-monoˡ-≤-nonNeg
        (distortion geometry)
        (hessianAbsoluteRowMass geometry left))
      (scalarTiltBudget geometry))

------------------------------------------------------------------------
-- Exact inverse transport and decay extraction.
------------------------------------------------------------------------

record PhysicalCombesThomasResolvent
    (hessian green : PhysicalMatrix) : Set₁ where
  field
    geometry : PhysicalCombesThomasGeometry hessian

    hessianGreenRightInverse :
      CT.RightInverse
        Physical.physicalSU2Coordinates4
        Calibration.identityEntry
        hessian green

    tiltedGreenEntryBound : ∀ target →
      ∣ CT.diagonalConjugate
          (physicalWeight geometry)
          (physicalInverseWeight geometry)
          green (root geometry) target ∣
      ≤ Survival.p33InverseScale

open PhysicalCombesThomasResolvent public

physicalTiltedRightInverse :
  ∀ {hessian green}
    (resolvent : PhysicalCombesThomasResolvent hessian green) →
  CT.RightInverse
    Physical.physicalSU2Coordinates4
    Calibration.identityEntry
    (CT.diagonalConjugate
      (physicalWeight (geometry resolvent))
      (physicalInverseWeight (geometry resolvent))
      hessian)
    (CT.diagonalConjugate
      (physicalWeight (geometry resolvent))
      (physicalInverseWeight (geometry resolvent))
      green)
physicalTiltedRightInverse {hessian} {green} resolvent =
  CT.conjugatedRightInverseWithStableIdentity
    Physical.physicalSU2Coordinates4
    Calibration.identityEntry
    hessian green
    (physicalWeight (geometry resolvent))
    (physicalInverseWeight (geometry resolvent))
    (physicalWeightInverseLaw (geometry resolvent))
    (hessianGreenRightInverse resolvent)
    (physicalIdentityStable (geometry resolvent))

physicalGreenKernelDecay :
  ∀ {hessian green}
    (resolvent : PhysicalCombesThomasResolvent hessian green)
    target →
  ∣ green (root (geometry resolvent)) target ∣
  ≤ Survival.p33InverseScale
      * physicalWeight (geometry resolvent) target
physicalGreenKernelDecay {green = green} resolvent target =
  CT.combesThomasKernelDecayFromTiltedEntry
    (physicalWeight (geometry resolvent))
    (physicalInverseWeight (geometry resolvent))
    (physicalWeightInverseLaw (geometry resolvent))
    green
    (root (geometry resolvent))
    target
    Survival.p33InverseScale
    (physicalInverseWeightAtRoot (geometry resolvent))
    (physicalWeightNonnegative (geometry resolvent) target)
    (physicalWeightAbsolute (geometry resolvent) target)
    (tiltedGreenEntryBound resolvent target)

physicalCombesThomasTiltBudgetLevel : ProofLevel
physicalCombesThomasTiltBudgetLevel = machineChecked

physicalCombesThomasIdentityStabilityLevel : ProofLevel
physicalCombesThomasIdentityStabilityLevel = machineChecked

physicalCombesThomasInverseTransportLevel : ProofLevel
physicalCombesThomasInverseTransportLevel = machineChecked

physicalCombesThomasKernelDecayLevel : ProofLevel
physicalCombesThomasKernelDecayLevel = machineChecked

physicalTiltedNormToEntryProducerLevel : ProofLevel
physicalTiltedNormToEntryProducerLevel = conditional
