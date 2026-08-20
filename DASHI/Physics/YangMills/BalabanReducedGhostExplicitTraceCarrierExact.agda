module DASHI.Physics.YangMills.BalabanReducedGhostExplicitTraceCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- DASHI CONTRIBUTION
--
-- Construct an explicit coordinate trace on the Round61 reduced ghost space.
-- For each colour a and site x, relative to anchor x0, use
--
--        b_(a,x) = e_(a,x) - e_(a,x0).
--
-- Every such source is colourwise mean-zero.  At x=x0 it is the zero vector,
-- so summing over all 256 sites is exactly the same diagonal sum as the 255
-- non-anchor basis vectors, without requiring a filtered-list proof.
--
-- The resulting trace is executable on the literal side-four carrier and the
-- identity endomorphism has trace
--
--        3 * (256 - 1) = 765.
--
-- Thus the reduced ghost trace appearing in the trace-log jet is no longer an
-- unspecified finite-dimensional trace carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Dec; Empty; yes; no; pair; four; periodicTorus4DecidableEquality)
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as Gauge
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixDimensionExact as Dimension
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact as Reindex
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact as Vector
import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact as Difference
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact as Reduced

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

lieCoordinateDecidableEquality :
  (left right : Coordinates.LieCoordinate3) → Dec (left ≡ right)
lieCoordinateDecidableEquality Coordinates.coordinateX Coordinates.coordinateX = yes refl
lieCoordinateDecidableEquality Coordinates.coordinateX Coordinates.coordinateY = no (λ ())
lieCoordinateDecidableEquality Coordinates.coordinateX Coordinates.coordinateZ = no (λ ())
lieCoordinateDecidableEquality Coordinates.coordinateY Coordinates.coordinateX = no (λ ())
lieCoordinateDecidableEquality Coordinates.coordinateY Coordinates.coordinateY = yes refl
lieCoordinateDecidableEquality Coordinates.coordinateY Coordinates.coordinateZ = no (λ ())
lieCoordinateDecidableEquality Coordinates.coordinateZ Coordinates.coordinateX = no (λ ())
lieCoordinateDecidableEquality Coordinates.coordinateZ Coordinates.coordinateY = no (λ ())
lieCoordinateDecidableEquality Coordinates.coordinateZ Coordinates.coordinateZ = yes refl

coordinateDelta : Coordinates.LieCoordinate3 → Coordinates.LieCoordinate3 → ℚ
coordinateDelta selected observed
  with lieCoordinateDecidableEquality selected observed
... | yes _ = 1ℚ
... | no _ = 0ℚ

reducedGhostBasisSource :
  Block.PhysicalBlockL Path4.side4 →
  Coordinates.LieCoordinate3 → Block.PhysicalBlockL Path4.side4 →
  Gauge.GaugeCoordinate4 → ℚ
reducedGhostBasisSource anchor selectedColour selectedSite (pair colour site) =
  coordinateDelta selectedColour colour
  * (Difference.siteDelta4 selectedSite site - Difference.siteDelta4 anchor site)

sumDifference :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  Sums.sumRational values (λ value → left value - right value)
  ≡ Sums.sumRational values left - Sums.sumRational values right
sumDifference [] left right = ℚRing.solve-∀
sumDifference (value ∷ values) left right
  rewrite sumDifference values left right = ℚRing.solve-∀

siteDeltaSelf : ∀ site → Difference.siteDelta4 site site ≡ 1ℚ
siteDeltaSelf site with periodicTorus4DecidableEquality four site site
... | yes equality = refl
... | no inequality = emptyElim (inequality refl)

siteDeltaSumOne : ∀ center →
  Reindex.siteSum4 (Difference.siteDelta4 center) ≡ 1ℚ
siteDeltaSumOne center =
  trans
    (Vector.siteSum4Cong
      (Difference.siteDelta4 center)
      (λ site → Difference.siteDelta4 center site * 1ℚ)
      (λ site → sym (ℚP.*-identityʳ (Difference.siteDelta4 center site))))
    (Green.siteDeltaConvolutionExact center (λ _ → 1ℚ))

siteDeltaDifferenceSumZero : ∀ selected anchor →
  Reindex.siteSum4
    (λ site → Difference.siteDelta4 selected site - Difference.siteDelta4 anchor site)
  ≡ 0ℚ
siteDeltaDifferenceSumZero selected anchor =
  trans
    (sumDifference
      (Block.physicalBlockSites Path4.side4)
      (Difference.siteDelta4 selected)
      (Difference.siteDelta4 anchor))
    (trans
      (cong
        (λ left → left - Reindex.siteSum4 (Difference.siteDelta4 anchor))
        (siteDeltaSumOne selected))
      (trans
        (cong (1ℚ -_) (siteDeltaSumOne anchor))
        (ℚRing.solve [])))

siteSumZero : Reindex.siteSum4 (λ _ → 0ℚ) ≡ 0ℚ
siteSumZero =
  trans
    (Fibre.sumRationalConstant
      (Block.physicalBlockSites Path4.side4) 0ℚ)
    (ℚRing.solve-∀
      (Sums.natAsRational
        (length (Block.physicalBlockSites Path4.side4))))

zeroColourComponentSum : ∀ selected anchor →
  Reindex.siteSum4
    (λ site → 0ℚ
      * (Difference.siteDelta4 selected site - Difference.siteDelta4 anchor site))
  ≡ 0ℚ
zeroColourComponentSum selected anchor =
  trans
    (Vector.siteSum4Cong _ (λ _ → 0ℚ)
      (λ site → ℚRing.solve-∀
        (Difference.siteDelta4 selected site)
        (Difference.siteDelta4 anchor site)))
    siteSumZero

sameColourComponentSum : ∀ selected anchor →
  Reindex.siteSum4
    (λ site → 1ℚ
      * (Difference.siteDelta4 selected site - Difference.siteDelta4 anchor site))
  ≡ 0ℚ
sameColourComponentSum selected anchor =
  trans
    (Vector.siteSum4Cong _ _ (λ site → ℚRing.solve-∀
      (Difference.siteDelta4 selected site) (Difference.siteDelta4 anchor site)))
    (siteDeltaDifferenceSumZero selected anchor)

reducedGhostBasisMeanZero :
  ∀ anchor selectedColour selectedSite →
  Reduced.ColourwiseMeanZero
    (reducedGhostBasisSource anchor selectedColour selectedSite)
reducedGhostBasisMeanZero anchor Coordinates.coordinateX selectedSite Coordinates.coordinateX =
  sameColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateX selectedSite Coordinates.coordinateY =
  zeroColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateX selectedSite Coordinates.coordinateZ =
  zeroColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateY selectedSite Coordinates.coordinateX =
  zeroColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateY selectedSite Coordinates.coordinateY =
  sameColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateY selectedSite Coordinates.coordinateZ =
  zeroColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateZ selectedSite Coordinates.coordinateX =
  zeroColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateZ selectedSite Coordinates.coordinateY =
  zeroColourComponentSum selectedSite anchor
reducedGhostBasisMeanZero anchor Coordinates.coordinateZ selectedSite Coordinates.coordinateZ =
  sameColourComponentSum selectedSite anchor

GhostLinearMap : Set
GhostLinearMap =
  (Gauge.GaugeCoordinate4 → ℚ) → (Gauge.GaugeCoordinate4 → ℚ)

reducedGhostTrace :
  Block.PhysicalBlockL Path4.side4 → GhostLinearMap → ℚ
reducedGhostTrace anchor operator =
  Sums.sumRational Coordinates.lieCoordinates3
    (λ colour →
      Reindex.siteSum4
        (λ site →
          operator
            (reducedGhostBasisSource anchor colour site)
            (pair colour site)))

identityGhost : GhostLinearMap
identityGhost source = source

siteConstantOneSum :
  Reindex.siteSum4 (λ _ → 1ℚ) ≡ (+ 256 / 1)
siteConstantOneSum =
  trans
    (Fibre.sumRationalConstant
      (Block.physicalBlockSites Path4.side4) 1ℚ)
    (trans
      (cong
        (λ count → Sums.natAsRational count * 1ℚ)
        Dimension.siteCountExact)
      (ℚRing.solve []))

identityBasisDiagonal : ∀ anchor colour site →
  identityGhost (reducedGhostBasisSource anchor colour site) (pair colour site)
  ≡ 1ℚ - Difference.siteDelta4 anchor site
identityBasisDiagonal anchor Coordinates.coordinateX site
  rewrite siteDeltaSelf site = ℚRing.solve-∀ (Difference.siteDelta4 anchor site)
identityBasisDiagonal anchor Coordinates.coordinateY site
  rewrite siteDeltaSelf site = ℚRing.solve-∀ (Difference.siteDelta4 anchor site)
identityBasisDiagonal anchor Coordinates.coordinateZ site
  rewrite siteDeltaSelf site = ℚRing.solve-∀ (Difference.siteDelta4 anchor site)

identityColourTrace255 : ∀ anchor colour →
  Reindex.siteSum4
    (λ site → identityGhost
      (reducedGhostBasisSource anchor colour site) (pair colour site))
  ≡ (+ 255 / 1)
identityColourTrace255 anchor colour =
  trans
    (Vector.siteSum4Cong _ _ (identityBasisDiagonal anchor colour))
    (trans
      (sumDifference
        (Block.physicalBlockSites Path4.side4)
        (λ _ → 1ℚ)
        (Difference.siteDelta4 anchor))
      (trans
        (cong
          (λ total → total - Reindex.siteSum4 (Difference.siteDelta4 anchor))
          siteConstantOneSum)
        (trans
          (cong ((+ 256 / 1) -_) (siteDeltaSumOne anchor))
          (ℚRing.solve []))))

reducedGhostIdentityTrace765 : ∀ anchor →
  reducedGhostTrace anchor identityGhost ≡ (+ 765 / 1)
reducedGhostIdentityTrace765 anchor
  rewrite identityColourTrace255 anchor Coordinates.coordinateX
        | identityColourTrace255 anchor Coordinates.coordinateY
        | identityColourTrace255 anchor Coordinates.coordinateZ =
  ℚRing.solve []

reducedGhostExplicitMeanZeroBasisLevel : ProofLevel
reducedGhostExplicitMeanZeroBasisLevel = machineChecked

reducedGhostExplicitTraceCarrierLevel : ProofLevel
reducedGhostExplicitTraceCarrierLevel = machineChecked

reducedGhostIdentityDimension765Level : ProofLevel
reducedGhostIdentityDimension765Level = machineChecked
