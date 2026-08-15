module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogSourceOperatorDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Keep the preferred G1 estimate at the source operator-norm level rather than
-- forcing the actual inverse-dexp coefficient into a rational matrix entry.
-- In the repository su(2) normalization [X,Y]=2 X cross Y,
--
--   J_-(Y)-I = +(1/2) ad_Y + beta(|Y|) ad_Y^2.
--
-- If |Y|<=t<=1/12, ||ad_Y||<=2t, ||ad_Y^2||<=4t^2 and
-- |beta(t)|<=1/6, then
--
--   ||J_-(Y)-I|| <= t + (2/3)t^2 <= 19/216 < 1/4.
--
-- This is deliberately a MAJORANT theorem.  The actual operator and its
-- Bishop-real coefficient need not have rational entries; a physical caller
-- supplies certified rational upper bounds on their norms.  Consequently G1
-- does not require an exact real-to-rational coefficient identification merely
-- to obtain conditioning.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

oneHalf oneSixth two four twoThirds : ℚ
oneHalf = + 1 / 2
oneSixth = + 1 / 6
two = + 2 / 1
four = + 4 / 1
twoThirds = + 2 / 3

sourceRadius quarter sourceDefectCeiling : ℚ
sourceRadius = + 1 / 12
quarter = + 1 / 4
sourceDefectCeiling = + 19 / 216

record SourceOperatorInverseDexpDefectData : Set where
  field
    radius adNorm adSquareNorm betaNorm jacobianDefectNorm : ℚ

    radiusNonnegative : 0ℚ ≤ radius
    adNormNonnegative : 0ℚ ≤ adNorm
    adSquareNormNonnegative : 0ℚ ≤ adSquareNorm
    betaNormNonnegative : 0ℚ ≤ betaNorm

    radiusInsideSourceChart : radius ≤ sourceRadius
    adNormBound : adNorm ≤ two * radius
    adSquareNormBound : adSquareNorm ≤ four * (radius * radius)
    betaNormBound : betaNorm ≤ oneSixth

    jacobianDefectTriangle :
      jacobianDefectNorm
      ≤ oneHalf * adNorm + betaNorm * adSquareNorm

open SourceOperatorInverseDexpDefectData public

radiusSquareNonnegative : ∀ radius → 0ℚ ≤ radius → 0ℚ ≤ radius * radius
radiusSquareNonnegative radius radiusNN =
  FiniteL2.squareNonnegative radius

radiusSquareMonotone :
  ∀ radius → 0ℚ ≤ radius → radius ≤ sourceRadius →
  radius * radius ≤ sourceRadius * sourceRadius
radiusSquareMonotone radius radiusNN radiusBelow =
  let
    sourceNN : 0ℚ ≤ sourceRadius
    sourceNN = ℚP.nonNegative⁻¹ sourceRadius
    first = Norm.scaleNonnegative radius radiusNN radiusBelow
    second = Norm.scaleNonnegative sourceRadius sourceNN radiusBelow
  in ℚP.≤-trans first second

scaledAdTerm :
  ∀ dataSet →
  oneHalf * adNorm dataSet ≤ radius dataSet
scaledAdTerm dataSet =
  let
    scaled = Norm.scaleNonnegative oneHalf
      (ℚP.nonNegative⁻¹ oneHalf) (adNormBound dataSet)
  in
  subst
    (λ upper → oneHalf * adNorm dataSet ≤ upper)
    (ℚRing.solve-∀ (radius dataSet))
    scaled

scaledQuadraticTerm :
  ∀ dataSet →
  betaNorm dataSet * adSquareNorm dataSet
  ≤ twoThirds * (radius dataSet * radius dataSet)
scaledQuadraticTerm dataSet =
  let
    betaNN = betaNormNonnegative dataSet
    radiusSqNN = radiusSquareNonnegative
      (radius dataSet) (radiusNonnegative dataSet)
    fourRadiusNN = Norm.scaleNonnegative four
      (ℚP.nonNegative⁻¹ four) radiusSqNN

    first :
      betaNorm dataSet * adSquareNorm dataSet
      ≤ betaNorm dataSet * (four * (radius dataSet * radius dataSet))
    first = Norm.scaleNonnegative
      (betaNorm dataSet) betaNN (adSquareNormBound dataSet)

    second :
      betaNorm dataSet * (four * (radius dataSet * radius dataSet))
      ≤ oneSixth * (four * (radius dataSet * radius dataSet))
    second = Norm.scaleNonnegative
      (four * (radius dataSet * radius dataSet))
      fourRadiusNN
      (betaNormBound dataSet)

    combined = ℚP.≤-trans first second
  in
  subst
    (λ upper →
      betaNorm dataSet * adSquareNorm dataSet ≤ upper)
    (ℚRing.solve-∀ (radius dataSet))
    combined

jacobianDefectBelowRadiusEnvelope :
  ∀ dataSet →
  jacobianDefectNorm dataSet
  ≤ radius dataSet + twoThirds * (radius dataSet * radius dataSet)
jacobianDefectBelowRadiusEnvelope dataSet =
  ℚP.≤-trans
    (jacobianDefectTriangle dataSet)
    (ℚP.+-mono-≤
      (scaledAdTerm dataSet)
      (scaledQuadraticTerm dataSet))

radiusEnvelopeBelowSourceCeiling :
  ∀ radius → 0ℚ ≤ radius → radius ≤ sourceRadius →
  radius + twoThirds * (radius * radius) ≤ sourceDefectCeiling
radiusEnvelopeBelowSourceCeiling radius radiusNN radiusBelow =
  let
    squareBelow = radiusSquareMonotone radius radiusNN radiusBelow
    scaledSquare = Norm.scaleNonnegative twoThirds
      (ℚP.nonNegative⁻¹ twoThirds) squareBelow
    summed = ℚP.+-mono-≤ radiusBelow scaledSquare
  in
  subst
    (λ upper →
      radius + twoThirds * (radius * radius) ≤ upper)
    (ℚRing.solve [])
    summed

sourceDefectCeilingBelowQuarter : sourceDefectCeiling ≤ quarter
sourceDefectCeilingBelowQuarter =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹ (quarter - sourceDefectCeiling))

sourceOperatorInverseDexpDefectQuarter :
  ∀ dataSet → jacobianDefectNorm dataSet ≤ quarter
sourceOperatorInverseDexpDefectQuarter dataSet =
  ℚP.≤-trans
    (jacobianDefectBelowRadiusEnvelope dataSet)
    (ℚP.≤-trans
      (radiusEnvelopeBelowSourceCeiling
        (radius dataSet)
        (radiusNonnegative dataSet)
        (radiusInsideSourceChart dataSet))
      sourceDefectCeilingBelowQuarter)

cmp109SourceOperatorInverseDexpEnvelopeLevel : ProofLevel
cmp109SourceOperatorInverseDexpEnvelopeLevel = machineChecked

cmp109SourceOperatorInverseDexpQuarterLevel : ProofLevel
cmp109SourceOperatorInverseDexpQuarterLevel = machineChecked

cmp109SourceOperatorInverseDexpPhysicalNormInputsLevel : ProofLevel
cmp109SourceOperatorInverseDexpPhysicalNormInputsLevel = conditional
