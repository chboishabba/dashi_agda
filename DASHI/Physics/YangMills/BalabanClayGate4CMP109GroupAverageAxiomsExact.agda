module DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source-exact group average used in CMP109 equations (0.5)--(0.12).
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- On pages 253--254 Bałaban introduces an analytic group-valued average M for
-- finite sets of sufficiently small diameter.  Equations (0.5)--(0.9) state
-- inverse covariance, bi-translation covariance, permutation invariance,
-- first-order Lie-algebra averaging, and subgroup closure.  Equation (0.10)
-- gives the implicit Federbush characterization
--
--   sum_j (1/i) log(U_j U^{-1}) = 0,
--
-- and equation (0.11) defines the averaged contour variable U(y,x).
--
-- The record below preserves exactly that theorem boundary.  The principal
-- consequence proved here is that averaging a family of path holonomies
-- preserves endpoint gauge covariance automatically; it is not an additional
-- physical axiom for every contour family.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

mapCongPointwise :
  ∀ {A B : Set} {left right : A → B} →
  (∀ value → left value ≡ right value) →
  ∀ values → mapList left values ≡ mapList right values
mapCongPointwise pointwise [] = refl
mapCongPointwise {left = left} pointwise (value ∷ values)
  with pointwise value
... | refl =
  cong (left value ∷_) (mapCongPointwise pointwise values)

data _∈List_ {A : Set} (value : A) : List A → Set where
  here : ∀ {values} → value ∈List (value ∷ values)
  there : ∀ {other values} → value ∈List values →
    value ∈List (other ∷ values)

record CMP109GroupAverageAxioms
    (Group Lie Scalar : Set) : Set₁ where
  field
    identity : Group
    inverse : Group → Group
    multiply : Group → Group → Group

    zeroLie : Lie
    addLie : Lie → Lie → Lie
    scaleLie : Scalar → Lie → Lie
    logarithmCoordinate : Group → Lie
    exponential : Lie → Group

    average : List Group → Group
    SmallDiameter : List Group → Set
    NearIdentity : List Group → Set
    Reordering : List Group → List Group → Set
    ClosedSubgroup : Group → Set

    averageInverse : ∀ values →
      SmallDiameter values →
      average (mapList inverse values) ≡ inverse (average values)

    averageBiTranslate : ∀ left right values →
      SmallDiameter values →
      average
        (mapList (λ value → multiply left (multiply value right)) values)
      ≡ multiply left (multiply (average values) right)

    averagePermutationInvariant : ∀ left right →
      SmallDiameter left → Reordering left right →
      average right ≡ average left

    LinearizationRemainder : List Lie → Lie → Set
    averageNearIdentityLinearization : ∀ lieValues →
      NearIdentity (mapList exponential lieValues) →
      LinearizationRemainder lieValues
        (logarithmCoordinate
          (average (mapList exponential lieValues)))

    averageClosedSubgroup : ∀ values →
      SmallDiameter values →
      (∀ value → value ∈List values → ClosedSubgroup value) →
      ClosedSubgroup (average values)

    logarithmSumRelativeTo : List Group → Group → Lie
    logarithmSumNil : ∀ centre →
      logarithmSumRelativeTo [] centre ≡ zeroLie
    logarithmSumCons : ∀ value values centre →
      logarithmSumRelativeTo (value ∷ values) centre
      ≡ addLie
          (logarithmCoordinate (multiply value (inverse centre)))
          (logarithmSumRelativeTo values centre)

    federbushEquation : ∀ values →
      SmallDiameter values →
      logarithmSumRelativeTo values (average values) ≡ zeroLie

open CMP109GroupAverageAxioms public

record GaugeCovariantPathFamily
    (Field Path Group Lie Scalar : Set)
    (averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar) : Set₁ where
  field
    paths : List Path
    holonomy transformedHolonomy : Field → Path → Group

    leftGauge rightGauge : Field → Group

    transformedHolonomyGaugeCovariant : ∀ fld path →
      transformedHolonomy fld path
      ≡ multiply averageAxioms (leftGauge fld)
          (multiply averageAxioms (holonomy fld path) (rightGauge fld))

    pathFamilySmallDiameter : ∀ fld →
      SmallDiameter averageAxioms
        (mapList (holonomy fld) paths)

open GaugeCovariantPathFamily public

averagedContour :
  ∀ {Field Path Group Lie Scalar}
    {averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar} →
  GaugeCovariantPathFamily
    Field Path Group Lie Scalar averageAxioms →
  Field → Group
averagedContour {averageAxioms = averageAxioms} family field =
  average averageAxioms
    (mapList (holonomy family field) (paths family))

transformedAveragedContour :
  ∀ {Field Path Group Lie Scalar}
    {averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar} →
  GaugeCovariantPathFamily
    Field Path Group Lie Scalar averageAxioms →
  Field → Group
transformedAveragedContour {averageAxioms = averageAxioms} family field =
  average averageAxioms
    (mapList (transformedHolonomy family field) (paths family))

averagedContourGaugeCovariant :
  ∀ {Field Path Group Lie Scalar}
    {averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar}
    (family : GaugeCovariantPathFamily
      Field Path Group Lie Scalar averageAxioms)
    field →
  transformedAveragedContour family field
  ≡ multiply averageAxioms (leftGauge family field)
      (multiply averageAxioms
        (averagedContour family field) (rightGauge family field))
averagedContourGaugeCovariant
    {averageAxioms = averageAxioms} family field =
  trans
    (cong (average averageAxioms)
      (mapCongPointwise
        (transformedHolonomyGaugeCovariant family field)
        (paths family)))
    (averageBiTranslate averageAxioms
      (leftGauge family field)
      (rightGauge family field)
      (mapList (holonomy family field) (paths family))
      (pathFamilySmallDiameter family field))

record ReversedContourFamily
    (Path Group Lie Scalar : Set)
    (averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar) : Set₁ where
  field
    forwardPaths : List Path
    reversePath : Path → Path
    holonomy : Path → Group

    reverseHolonomy : ∀ path →
      holonomy (reversePath path) ≡ inverse averageAxioms (holonomy path)

    forwardSmallDiameter :
      SmallDiameter averageAxioms (mapList holonomy forwardPaths)

open ReversedContourFamily public

forwardContourAverage :
  ∀ {Path Group Lie Scalar}
    {averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar} →
  ReversedContourFamily Path Group Lie Scalar averageAxioms → Group
forwardContourAverage {averageAxioms = averageAxioms} family =
  average averageAxioms
    (mapList (holonomy family) (forwardPaths family))

reverseContourAverage :
  ∀ {Path Group Lie Scalar}
    {averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar} →
  ReversedContourFamily Path Group Lie Scalar averageAxioms → Group
reverseContourAverage {averageAxioms = averageAxioms} family =
  average averageAxioms
    (mapList
      (λ path → holonomy family (reversePath family path))
      (forwardPaths family))

reverseContourAverageIsInverse :
  ∀ {Path Group Lie Scalar}
    {averageAxioms : CMP109GroupAverageAxioms Group Lie Scalar}
    (family : ReversedContourFamily Path Group Lie Scalar averageAxioms) →
  reverseContourAverage family
  ≡ inverse averageAxioms (forwardContourAverage family)
reverseContourAverageIsInverse
    {averageAxioms = averageAxioms} family =
  trans
    (cong (average averageAxioms)
      (mapCongPointwise
        (reverseHolonomy family)
        (forwardPaths family)))
    (averageInverse averageAxioms
      (mapList (holonomy family) (forwardPaths family))
      (forwardSmallDiameter family))

cmp109GroupAverageAxiomSurfaceLevel : ProofLevel
cmp109GroupAverageAxiomSurfaceLevel = standardImported

cmp109AveragedContourGaugeCovarianceLevel : ProofLevel
cmp109AveragedContourGaugeCovarianceLevel = machineChecked

cmp109ReversedContourAverageLevel : ProofLevel
cmp109ReversedContourAverageLevel = machineChecked

physicalCMP109FederbushAverageExistenceInputsLevel : ProofLevel
physicalCMP109FederbushAverageExistenceInputsLevel = conditional

physicalCMP109ContourFamilySmallDiameterInputsLevel : ProofLevel
physicalCMP109ContourFamilySmallDiameterInputsLevel = conditional
