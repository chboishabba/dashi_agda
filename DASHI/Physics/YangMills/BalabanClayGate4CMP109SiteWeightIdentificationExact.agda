module DASHI.Physics.YangMills.BalabanClayGate4CMP109SiteWeightIdentificationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Scale

------------------------------------------------------------------------
-- Exact L^{-4} and contour-cardinality weights for CMP109 equations (0.3)--(0.12).
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- In d=4, the displayed site weight is L^{-4}.  The centred physical block has
-- exactly L^4 sites, so this is the reciprocal-cardinality uniform weight.  The
-- contour average is separate: its weight is the reciprocal of the actual
-- generated family length, which varies with the number of nonzero coordinate
-- displacements and must not be hard-coded as 1/24.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

record FiniteAverageAlgebra (Scalar Value : Set) : Set₁ where
  field
    zero : Value
    add : Value → Value → Value
    scale : Scalar → Value → Value

    natScalar : Nat → Scalar
    inverse : Scalar → Scalar
    fourthPowerScalar : Scalar → Scalar

    natScalarFourthPower : ∀ value →
      natScalar (Centered.fourthPower value)
      ≡ fourthPowerScalar (natScalar value)

open FiniteAverageAlgebra public

finiteSum :
  ∀ {Scalar Value} →
  FiniteAverageAlgebra Scalar Value → List Value → Value
finiteSum algebra [] = zero algebra
finiteSum algebra (value ∷ values) =
  add algebra value (finiteSum algebra values)

weightedAverage :
  ∀ {Index Scalar Value} →
  FiniteAverageAlgebra Scalar Value →
  Scalar → List Index → (Index → Value) → Value
weightedAverage algebra weight indices values =
  scale algebra weight
    (finiteSum algebra (mapList values indices))

weightedAverageWeightCong :
  ∀ {Index Scalar Value}
    (algebra : FiniteAverageAlgebra Scalar Value)
    {left right : Scalar} →
  left ≡ right →
  ∀ indices values →
  weightedAverage algebra left indices values
  ≡ weightedAverage algebra right indices values
weightedAverageWeightCong algebra refl indices values = refl

record CMP109SiteAndContourWeightData
    (radius : Nat) (Path Scalar Value : Set) : Set₁ where
  field
    algebra : FiniteAverageAlgebra Scalar Value

    sideScalar volumeScalar : Scalar
    siteWeight : Scalar

    sideScalarMeaning :
      sideScalar ≡ natScalar algebra (Centered.oddSide radius)

    volumeScalarMeaning :
      volumeScalar
      ≡ natScalar algebra
          (Centered.fourthPower (Centered.oddSide radius))

    siteWeightMeaning :
      siteWeight
      ≡ inverse algebra
          (fourthPowerScalar algebra sideScalar)

    contourWeight : List Path → Scalar
    contourWeightMeaning : ∀ paths →
      contourWeight paths
      ≡ inverse algebra (natScalar algebra (length paths))

open CMP109SiteAndContourWeightData public

siteWeightEqualsInverseBlockCardinality :
  ∀ {radius Path Scalar Value}
    (weights : CMP109SiteAndContourWeightData
      radius Path Scalar Value) →
  siteWeight weights
  ≡ inverse (algebra weights) (volumeScalar weights)
siteWeightEqualsInverseBlockCardinality {radius} weights =
  trans
    (siteWeightMeaning weights)
    (cong (inverse (algebra weights))
      (trans
        (cong
          (fourthPowerScalar (algebra weights))
          (sideScalarMeaning weights))
        (trans
          (sym
            (natScalarFourthPower (algebra weights)
              (Centered.oddSide radius)))
          (sym (volumeScalarMeaning weights)))))

siteAverageEqualsReciprocalCardinalityAverage :
  ∀ {radius Path Scalar Value Index}
    (weights : CMP109SiteAndContourWeightData
      radius Path Scalar Value)
    indices values →
  weightedAverage (algebra weights)
    (siteWeight weights) indices values
  ≡ weightedAverage (algebra weights)
      (inverse (algebra weights) (volumeScalar weights))
      indices values
siteAverageEqualsReciprocalCardinalityAverage weights indices values =
  weightedAverageWeightCong (algebra weights)
    (siteWeightEqualsInverseBlockCardinality weights)
    indices values

contourAverageUsesActualFamilyCardinality :
  ∀ {radius Path Scalar Value}
    (weights : CMP109SiteAndContourWeightData
      radius Path Scalar Value)
    paths values →
  weightedAverage (algebra weights)
    (contourWeight weights paths) paths values
  ≡ weightedAverage (algebra weights)
      (inverse (algebra weights)
        (natScalar (algebra weights) (length paths)))
      paths values
contourAverageUsesActualFamilyCardinality weights paths values =
  weightedAverageWeightCong (algebra weights)
    (contourWeightMeaning weights paths) paths values

record CMP109Equations003To012Identification
    (radius : Nat)
    (FineSite CoarseSite Spacing FineBond CoarseBond Path
      Scalar Value Input Output : Set) : Set₁ where
  field
    geometry : Scale.CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing

    endpoints : Scale.CMP109EndpointBlockIdentification
      {FineBond = FineBond} {CoarseBond = CoarseBond} geometry

    weights : CMP109SiteAndContourWeightData
      radius Path Scalar Value

    sourceContours targetContours : CoarseBond → FineBond → List Path

    executableMap printedEquation012Map printedEquation004Map :
      Input → Output

    Equation003BlockMeaning : Set
    Equation004ExpandedMeaning : Set
    Equation011GroupAverageMeaning : Set
    Equation012CompactMeaning : Set

    equation003BlockMeaning : Equation003BlockMeaning
    equation004ExpandedMeaning : Equation004ExpandedMeaning
    equation011GroupAverageMeaning : Equation011GroupAverageMeaning
    equation012CompactMeaning : Equation012CompactMeaning

    executableEqualsEquation012 :
      executableMap ≡ printedEquation012Map

    equation012ExpandsToEquation004 :
      printedEquation012Map ≡ printedEquation004Map

open CMP109Equations003To012Identification public

executableEqualsPrintedEquation004 :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      Scalar Value Input Output}
    (identification : CMP109Equations003To012Identification
      radius FineSite CoarseSite Spacing FineBond CoarseBond Path
      Scalar Value Input Output) →
  executableMap identification ≡ printedEquation004Map identification
executableEqualsPrintedEquation004 identification =
  trans
    (executableEqualsEquation012 identification)
    (equation012ExpandsToEquation004 identification)

cmp109SiteWeightCardinalityLevel : ProofLevel
cmp109SiteWeightCardinalityLevel = machineChecked

cmp109ContourWeightActualCardinalityLevel : ProofLevel
cmp109ContourWeightActualCardinalityLevel = machineChecked

cmp109Equation004Equation012TransportLevel : ProofLevel
cmp109Equation004Equation012TransportLevel = machineChecked

physicalCMP109SiteWeightMeaningInputsLevel : ProofLevel
physicalCMP109SiteWeightMeaningInputsLevel = conditional

physicalCMP109ContourMultiplicityInputsLevel : ProofLevel
physicalCMP109ContourMultiplicityInputsLevel = conditional

physicalCMP109EquationIdentificationInputsLevel : ProofLevel
physicalCMP109EquationIdentificationInputsLevel = conditional
