module DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Insert an explicit nontrivial rational Combes--Thomas weight into the
-- literal selected-background residual R_A = G_0 E_A.
--
-- On C4, use the radial one-coordinate profile
--
--   distance : 0 1 2 1
--   w        : 1, 64/65, (64/65)^2, 64/65
--   w^-1     : 1, 65/64, (65/64)^2, 65/64.
--
-- The four-dimensional weight is the product of the four coordinate weights.
-- Thus it is exactly a rational exponential profile in the periodic l1 radius.
-- We prove w*w^-1=1 pointwise, w<=1 and
--
--   w^-1 <= (9/8)^4 = 6561/4096.
--
-- Conjugating the actual R_A by this diagonal weight and using the already
-- proved unweighted row-mass contraction gives
--
--   sup_i sum_j |(D R_A D^-1)(i,j)|
--     <= (6561/4096)(104601/1048576)
--      = 686287161/4294967296
--      < 1/6 < 1/2.
--
-- This closes the *weighted smallness* part of the selected-background Green
-- problem on the configured side-four torus with a large exact margin.  It is
-- not a scale-uniform RG theorem: the global weight-ratio estimate is tied to
-- the finite side-four block and must later be replaced by the local
-- finite-range estimate when uniformity in scale is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (CyclicIndex; four; zeroᵢ; sucᵢ; pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact as Difference
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeConstraintAbsoluteMassExact as FlatMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as PerturbationMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow : Set
GaugeRow = FlatGauge.GaugeCoordinate4

gaugeRows = FlatMass.flatRows

------------------------------------------------------------------------
-- Exact rational radial profile on C4.
------------------------------------------------------------------------

decayBase growthBase decaySquare growthSquare : ℚ
decayBase = + 64 / 65
growthBase = + 65 / 64
decaySquare = + 4096 / 4225
growthSquare = + 4225 / 4096

coordinateDecay : CyclicIndex four → ℚ
coordinateDecay zeroᵢ = 1ℚ
coordinateDecay (sucᵢ zeroᵢ) = decayBase
coordinateDecay (sucᵢ (sucᵢ zeroᵢ)) = decaySquare
coordinateDecay (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = decayBase

coordinateGrowth : CyclicIndex four → ℚ
coordinateGrowth zeroᵢ = 1ℚ
coordinateGrowth (sucᵢ zeroᵢ) = growthBase
coordinateGrowth (sucᵢ (sucᵢ zeroᵢ)) = growthSquare
coordinateGrowth (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = growthBase

coordinateWeightInverseExact : ∀ coordinate →
  coordinateDecay coordinate * coordinateGrowth coordinate ≡ 1ℚ
coordinateWeightInverseExact zeroᵢ = ℚRing.solve []
coordinateWeightInverseExact (sucᵢ zeroᵢ) = ℚRing.solve []
coordinateWeightInverseExact (sucᵢ (sucᵢ zeroᵢ)) = ℚRing.solve []
coordinateWeightInverseExact (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = ℚRing.solve []

coordinateDecayNonnegative : ∀ coordinate → 0ℚ ≤ coordinateDecay coordinate
coordinateDecayNonnegative zeroᵢ = ℚP.nonNegative⁻¹ 1ℚ
coordinateDecayNonnegative (sucᵢ zeroᵢ) = ℚP.nonNegative⁻¹ decayBase
coordinateDecayNonnegative (sucᵢ (sucᵢ zeroᵢ)) = ℚP.nonNegative⁻¹ decaySquare
coordinateDecayNonnegative (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = ℚP.nonNegative⁻¹ decayBase

coordinateGrowthNonnegative : ∀ coordinate → 0ℚ ≤ coordinateGrowth coordinate
coordinateGrowthNonnegative zeroᵢ = ℚP.nonNegative⁻¹ 1ℚ
coordinateGrowthNonnegative (sucᵢ zeroᵢ) = ℚP.nonNegative⁻¹ growthBase
coordinateGrowthNonnegative (sucᵢ (sucᵢ zeroᵢ)) = ℚP.nonNegative⁻¹ growthSquare
coordinateGrowthNonnegative (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = ℚP.nonNegative⁻¹ growthBase

belowFromDifference : ∀ left right difference →
  right - left ≡ difference → 0ℚ ≤ difference → left ≤ right
belowFromDifference left right difference equality nonnegative =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst (λ selected → 0ℚ ≤ selected) (sym equality) nonnegative)

coordinateDecayBelowOne : ∀ coordinate → coordinateDecay coordinate ≤ 1ℚ
coordinateDecayBelowOne zeroᵢ = ℚP.≤-refl
coordinateDecayBelowOne (sucᵢ zeroᵢ) =
  belowFromDifference decayBase 1ℚ (+ 1 / 65) (ℚRing.solve [])
    (ℚP.nonNegative⁻¹ (+ 1 / 65))
coordinateDecayBelowOne (sucᵢ (sucᵢ zeroᵢ)) =
  belowFromDifference decaySquare 1ℚ (+ 129 / 4225) (ℚRing.solve [])
    (ℚP.nonNegative⁻¹ (+ 129 / 4225))
coordinateDecayBelowOne (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) =
  belowFromDifference decayBase 1ℚ (+ 1 / 65) (ℚRing.solve [])
    (ℚP.nonNegative⁻¹ (+ 1 / 65))

coordinateGrowthEnvelope : ℚ
coordinateGrowthEnvelope = + 9 / 8

coordinateGrowthBelowEnvelope : ∀ coordinate →
  coordinateGrowth coordinate ≤ coordinateGrowthEnvelope
coordinateGrowthBelowEnvelope zeroᵢ =
  belowFromDifference 1ℚ coordinateGrowthEnvelope (+ 1 / 8)
    (ℚRing.solve []) (ℚP.nonNegative⁻¹ (+ 1 / 8))
coordinateGrowthBelowEnvelope (sucᵢ zeroᵢ) =
  belowFromDifference growthBase coordinateGrowthEnvelope (+ 7 / 64)
    (ℚRing.solve []) (ℚP.nonNegative⁻¹ (+ 7 / 64))
coordinateGrowthBelowEnvelope (sucᵢ (sucᵢ zeroᵢ)) =
  belowFromDifference growthSquare coordinateGrowthEnvelope (+ 383 / 4096)
    (ℚRing.solve []) (ℚP.nonNegative⁻¹ (+ 383 / 4096))
coordinateGrowthBelowEnvelope (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) =
  belowFromDifference growthBase coordinateGrowthEnvelope (+ 7 / 64)
    (ℚRing.solve []) (ℚP.nonNegative⁻¹ (+ 7 / 64))

multiplyNonnegative : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
multiplyNonnegative left right leftNonnegative rightNonnegative =
  subst
    (λ lower → lower ≤ left * right)
    (sym (ℚRing.solve-∀ left : left * 0ℚ ≡ 0ℚ))
    (Norm.scaleNonnegative left leftNonnegative rightNonnegative)

multiplyBounds : ∀ left leftBound right rightBound →
  0ℚ ≤ left → 0ℚ ≤ leftBound → 0ℚ ≤ right →
  left ≤ leftBound → right ≤ rightBound →
  left * right ≤ leftBound * rightBound
multiplyBounds left leftBound right rightBound
    leftNonnegative leftBoundNonnegative rightNonnegative leftBelow rightBelow =
  ℚP.≤-trans
    (PerturbationMass.rightScaleMonotone
      right left leftBound rightNonnegative leftBelow)
    (Norm.scaleNonnegative leftBound leftBoundNonnegative rightBelow)

------------------------------------------------------------------------
-- Four-dimensional product profile.
------------------------------------------------------------------------

siteDecayWeight : Block.PhysicalBlockL 4 → ℚ
siteDecayWeight (pair (pair x0 x1) (pair x2 x3)) =
  (coordinateDecay x0 * coordinateDecay x1)
    * (coordinateDecay x2 * coordinateDecay x3)

siteGrowthWeight : Block.PhysicalBlockL 4 → ℚ
siteGrowthWeight (pair (pair x0 x1) (pair x2 x3)) =
  (coordinateGrowth x0 * coordinateGrowth x1)
    * (coordinateGrowth x2 * coordinateGrowth x3)

siteWeightInverseExact : ∀ site →
  siteDecayWeight site * siteGrowthWeight site ≡ 1ℚ
siteWeightInverseExact (pair (pair x0 x1) (pair x2 x3)) =
  let
    rearrange :
      ((coordinateDecay x0 * coordinateDecay x1)
        * (coordinateDecay x2 * coordinateDecay x3))
      * ((coordinateGrowth x0 * coordinateGrowth x1)
        * (coordinateGrowth x2 * coordinateGrowth x3))
      ≡ (coordinateDecay x0 * coordinateGrowth x0)
        * (coordinateDecay x1 * coordinateGrowth x1)
        * (coordinateDecay x2 * coordinateGrowth x2)
        * (coordinateDecay x3 * coordinateGrowth x3)
    rearrange = ℚRing.solve []
  in
  trans rearrange
    (subst
      (λ p0 → p0
        * (coordinateDecay x1 * coordinateGrowth x1)
        * (coordinateDecay x2 * coordinateGrowth x2)
        * (coordinateDecay x3 * coordinateGrowth x3) ≡ 1ℚ)
      (sym (coordinateWeightInverseExact x0))
      (subst
        (λ p1 → 1ℚ * p1
          * (coordinateDecay x2 * coordinateGrowth x2)
          * (coordinateDecay x3 * coordinateGrowth x3) ≡ 1ℚ)
        (sym (coordinateWeightInverseExact x1))
        (subst
          (λ p2 → 1ℚ * 1ℚ * p2
            * (coordinateDecay x3 * coordinateGrowth x3) ≡ 1ℚ)
          (sym (coordinateWeightInverseExact x2))
          (subst
            (λ p3 → 1ℚ * 1ℚ * 1ℚ * p3 ≡ 1ℚ)
            (sym (coordinateWeightInverseExact x3))
            (ℚRing.solve [])))))

siteDecayNonnegative : ∀ site → 0ℚ ≤ siteDecayWeight site
siteDecayNonnegative (pair (pair x0 x1) (pair x2 x3)) =
  multiplyNonnegative
    (coordinateDecay x0 * coordinateDecay x1)
    (coordinateDecay x2 * coordinateDecay x3)
    (multiplyNonnegative _ _
      (coordinateDecayNonnegative x0) (coordinateDecayNonnegative x1))
    (multiplyNonnegative _ _
      (coordinateDecayNonnegative x2) (coordinateDecayNonnegative x3))

siteGrowthNonnegative : ∀ site → 0ℚ ≤ siteGrowthWeight site
siteGrowthNonnegative (pair (pair x0 x1) (pair x2 x3)) =
  multiplyNonnegative
    (coordinateGrowth x0 * coordinateGrowth x1)
    (coordinateGrowth x2 * coordinateGrowth x3)
    (multiplyNonnegative _ _
      (coordinateGrowthNonnegative x0) (coordinateGrowthNonnegative x1))
    (multiplyNonnegative _ _
      (coordinateGrowthNonnegative x2) (coordinateGrowthNonnegative x3))

siteDecayBelowOne : ∀ site → siteDecayWeight site ≤ 1ℚ
siteDecayBelowOne (pair (pair x0 x1) (pair x2 x3)) =
  let
    firstPair = multiplyBounds
      (coordinateDecay x0) 1ℚ (coordinateDecay x1) 1ℚ
      (coordinateDecayNonnegative x0) (ℚP.nonNegative⁻¹ 1ℚ)
      (coordinateDecayNonnegative x1)
      (coordinateDecayBelowOne x0) (coordinateDecayBelowOne x1)
    secondPair = multiplyBounds
      (coordinateDecay x2) 1ℚ (coordinateDecay x3) 1ℚ
      (coordinateDecayNonnegative x2) (ℚP.nonNegative⁻¹ 1ℚ)
      (coordinateDecayNonnegative x3)
      (coordinateDecayBelowOne x2) (coordinateDecayBelowOne x3)
    firstPairNonnegative = multiplyNonnegative _ _
      (coordinateDecayNonnegative x0) (coordinateDecayNonnegative x1)
    secondPairNonnegative = multiplyNonnegative _ _
      (coordinateDecayNonnegative x2) (coordinateDecayNonnegative x3)
  in
  subst
    (λ upper → siteDecayWeight (pair (pair x0 x1) (pair x2 x3)) ≤ upper)
    (ℚRing.solve [] : 1ℚ * 1ℚ ≡ 1ℚ)
    (multiplyBounds _ 1ℚ _ 1ℚ
      firstPairNonnegative (ℚP.nonNegative⁻¹ 1ℚ)
      secondPairNonnegative firstPair secondPair)

siteGrowthEnvelope : ℚ
siteGrowthEnvelope = + 6561 / 4096

siteGrowthEnvelopeExact :
  (coordinateGrowthEnvelope * coordinateGrowthEnvelope)
    * (coordinateGrowthEnvelope * coordinateGrowthEnvelope)
  ≡ siteGrowthEnvelope
siteGrowthEnvelopeExact = ℚRing.solve []

siteGrowthBelowEnvelope : ∀ site → siteGrowthWeight site ≤ siteGrowthEnvelope
siteGrowthBelowEnvelope (pair (pair x0 x1) (pair x2 x3)) =
  let
    envelopeNonnegative = ℚP.nonNegative⁻¹ coordinateGrowthEnvelope
    firstPair = multiplyBounds
      (coordinateGrowth x0) coordinateGrowthEnvelope
      (coordinateGrowth x1) coordinateGrowthEnvelope
      (coordinateGrowthNonnegative x0) envelopeNonnegative
      (coordinateGrowthNonnegative x1)
      (coordinateGrowthBelowEnvelope x0) (coordinateGrowthBelowEnvelope x1)
    secondPair = multiplyBounds
      (coordinateGrowth x2) coordinateGrowthEnvelope
      (coordinateGrowth x3) coordinateGrowthEnvelope
      (coordinateGrowthNonnegative x2) envelopeNonnegative
      (coordinateGrowthNonnegative x3)
      (coordinateGrowthBelowEnvelope x2) (coordinateGrowthBelowEnvelope x3)
    firstPairNonnegative = multiplyNonnegative _ _
      (coordinateGrowthNonnegative x0) (coordinateGrowthNonnegative x1)
    secondPairNonnegative = multiplyNonnegative _ _
      (coordinateGrowthNonnegative x2) (coordinateGrowthNonnegative x3)
    pairEnvelope = coordinateGrowthEnvelope * coordinateGrowthEnvelope
    pairEnvelopeNonnegative = multiplyNonnegative _ _ envelopeNonnegative envelopeNonnegative
    combined = multiplyBounds _ pairEnvelope _ pairEnvelope
      firstPairNonnegative pairEnvelopeNonnegative secondPairNonnegative
      firstPair secondPair
  in
  subst
    (λ upper → siteGrowthWeight (pair (pair x0 x1) (pair x2 x3)) ≤ upper)
    siteGrowthEnvelopeExact combined

siteDecayAbsoluteExact : ∀ site → ∣ siteDecayWeight site ∣ ≡ siteDecayWeight site
siteDecayAbsoluteExact site = ℚP.0≤p⇒∣p∣≡p (siteDecayNonnegative site)

siteGrowthAbsoluteExact : ∀ site → ∣ siteGrowthWeight site ∣ ≡ siteGrowthWeight site
siteGrowthAbsoluteExact site = ℚP.0≤p⇒∣p∣≡p (siteGrowthNonnegative site)

------------------------------------------------------------------------
-- Rooted multiplier weight and exact inverse law.
------------------------------------------------------------------------

gaugeWeight : GaugeRow → GaugeRow → ℚ
gaugeWeight (pair rootCoordinate rootSite) (pair coordinate site) =
  siteDecayWeight (Difference.subtractSite4 site rootSite)

gaugeInverseWeight : GaugeRow → GaugeRow → ℚ
gaugeInverseWeight (pair rootCoordinate rootSite) (pair coordinate site) =
  siteGrowthWeight (Difference.subtractSite4 site rootSite)

gaugeWeightInverseExact : ∀ root row →
  gaugeInverseWeight root row * gaugeWeight root row ≡ 1ℚ
gaugeWeightInverseExact
    (pair rootCoordinate rootSite) (pair coordinate site) =
  trans
    (ℚP.*-comm
      (siteGrowthWeight (Difference.subtractSite4 site rootSite))
      (siteDecayWeight (Difference.subtractSite4 site rootSite)))
    (siteWeightInverseExact (Difference.subtractSite4 site rootSite))

gaugeWeightBelowOne : ∀ root row → gaugeWeight root row ≤ 1ℚ
gaugeWeightBelowOne (pair rootCoordinate rootSite) (pair coordinate site) =
  siteDecayBelowOne (Difference.subtractSite4 site rootSite)

gaugeInverseWeightBelowEnvelope : ∀ root row →
  gaugeInverseWeight root row ≤ siteGrowthEnvelope
gaugeInverseWeightBelowEnvelope
    (pair rootCoordinate rootSite) (pair coordinate site) =
  siteGrowthBelowEnvelope (Difference.subtractSite4 site rootSite)

gaugeWeightNonnegative : ∀ root row → 0ℚ ≤ gaugeWeight root row
gaugeWeightNonnegative (pair rootCoordinate rootSite) (pair coordinate site) =
  siteDecayNonnegative (Difference.subtractSite4 site rootSite)

gaugeInverseWeightNonnegative : ∀ root row → 0ℚ ≤ gaugeInverseWeight root row
gaugeInverseWeightNonnegative
    (pair rootCoordinate rootSite) (pair coordinate site) =
  siteGrowthNonnegative (Difference.subtractSite4 site rootSite)

gaugeWeightAbsoluteExact : ∀ root row →
  ∣ gaugeWeight root row ∣ ≡ gaugeWeight root row
gaugeWeightAbsoluteExact root row =
  ℚP.0≤p⇒∣p∣≡p (gaugeWeightNonnegative root row)

gaugeInverseWeightAbsoluteExact : ∀ root row →
  ∣ gaugeInverseWeight root row ∣ ≡ gaugeInverseWeight root row
gaugeInverseWeightAbsoluteExact root row =
  ℚP.0≤p⇒∣p∣≡p (gaugeInverseWeightNonnegative root row)

gaugeRootInverseWeightOne : ∀ root → gaugeInverseWeight root root ≡ 1ℚ
gaugeRootInverseWeightOne (pair rootCoordinate rootSite)
  rewrite Difference.subtractSiteSelfZero rootSite = refl

------------------------------------------------------------------------
-- Generic absolute row-mass estimate under this diagonal conjugation.
------------------------------------------------------------------------

weightedKernel : GaugeRow → (GaugeRow → GaugeRow → ℚ) → GaugeRow → GaugeRow → ℚ
weightedKernel root kernel =
  CT.diagonalConjugate (gaugeWeight root) (gaugeInverseWeight root) kernel

weightedEntryAbsoluteUpper : ∀ root kernel row column →
  ∣ weightedKernel root kernel row column ∣
  ≤ ∣ kernel row column ∣ * siteGrowthEnvelope
weightedEntryAbsoluteUpper root kernel row column =
  let
    w = gaugeWeight root row
    iw = gaugeInverseWeight root column
    k = kernel row column

    exactAbs :
      ∣ weightedKernel root kernel row column ∣
      ≡ w * (∣ k ∣ * iw)
    exactAbs =
      trans
        (Schur.absoluteProductExact w (k * iw))
        (trans
          (cong (_* ∣ k * iw ∣) (gaugeWeightAbsoluteExact root row))
          (cong (w *_)
            (trans
              (Schur.absoluteProductExact k iw)
              (cong (∣ k ∣ *_)
                (gaugeInverseWeightAbsoluteExact root column)))))

    innerNonnegative : 0ℚ ≤ ∣ k ∣ * iw
    innerNonnegative = multiplyNonnegative _ _
      (ℚP.0≤∣p∣ k) (gaugeInverseWeightNonnegative root column)

    removeWeight : w * (∣ k ∣ * iw) ≤ 1ℚ * (∣ k ∣ * iw)
    removeWeight = PerturbationMass.rightScaleMonotone
      (∣ k ∣ * iw) w 1ℚ innerNonnegative (gaugeWeightBelowOne root row)

    enlargeInverse : ∣ k ∣ * iw ≤ ∣ k ∣ * siteGrowthEnvelope
    enlargeInverse = Norm.scaleNonnegative ∣ k ∣
      (ℚP.0≤∣p∣ k) (gaugeInverseWeightBelowEnvelope root column)
  in
  subst
    (λ lower → lower ≤ ∣ k ∣ * siteGrowthEnvelope)
    (sym exactAbs)
    (ℚP.≤-trans removeWeight
      (subst
        (λ lower → lower ≤ ∣ k ∣ * siteGrowthEnvelope)
        (ℚRing.solve-∀ (∣ k ∣) iw : 1ℚ * (∣ k ∣ * iw) ≡ ∣ k ∣ * iw)
        enlargeInverse))

weightedRowMassUpper : ∀ root kernel row →
  Mass.squareRowMass gaugeRows (weightedKernel root kernel) row
  ≤ Mass.squareRowMass gaugeRows kernel row * siteGrowthEnvelope
weightedRowMassUpper root kernel row =
  let
    pointwise = Schur.sumPointwiseBelow gaugeRows _ _
      (weightedEntryAbsoluteUpper root kernel row)

    rightScaleExact :
      Sums.sumRational gaugeRows
        (λ column → ∣ kernel row column ∣ * siteGrowthEnvelope)
      ≡ Mass.squareRowMass gaugeRows kernel row * siteGrowthEnvelope
    rightScaleExact =
      trans
        (Sums.sumRationalCong gaugeRows _ _
          (λ column →
            ℚP.*-comm ∣ kernel row column ∣ siteGrowthEnvelope))
        (trans
          (Sums.sumRationalScale siteGrowthEnvelope gaugeRows
            (λ column → ∣ kernel row column ∣))
          (ℚP.*-comm siteGrowthEnvelope
            (Mass.squareRowMass gaugeRows kernel row)))
  in
  subst
    (λ upper →
      Mass.squareRowMass gaugeRows (weightedKernel root kernel) row ≤ upper)
    rightScaleExact pointwise

------------------------------------------------------------------------
-- Literal weighted selected-background residual.
------------------------------------------------------------------------

weightedSelectedBackgroundResidual :
  GaugeRow → Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
weightedSelectedBackgroundResidual root background =
  weightedKernel root (Contraction.flatGreenTimesPerturbationKernel background)

weightedContractionBound : ℚ
weightedContractionBound = + 686287161 / 4294967296

weightedContractionExactProduct :
  Contraction.greenPerturbationContractionBound * siteGrowthEnvelope
  ≡ weightedContractionBound
weightedContractionExactProduct = ℚRing.solve []

weightedContractionBelowOneSixth : weightedContractionBound ≤ + 1 / 6
weightedContractionBelowOneSixth =
  belowFromDifference weightedContractionBound (+ 1 / 6)
    (+ 88622165 / 12884901888)
    (ℚRing.solve [])
    (ℚP.nonNegative⁻¹ (+ 88622165 / 12884901888))

oneSixthBelowOneHalf : (+ 1 / 6) ≤ (+ 1 / 2)
oneSixthBelowOneHalf =
  belowFromDifference (+ 1 / 6) (+ 1 / 2) (+ 1 / 3)
    (ℚRing.solve []) (ℚP.nonNegative⁻¹ (+ 1 / 3))

selectedBackgroundWeightedGreenPerturbationAbsoluteRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root row →
  Mass.squareRowMass gaugeRows
    (weightedSelectedBackgroundResidual root background) row
  ≤ weightedContractionBound
selectedBackgroundWeightedGreenPerturbationAbsoluteRowMassBound
    background radius root row =
  let
    raw = weightedRowMassUpper root
      (Contraction.flatGreenTimesPerturbationKernel background) row

    scaled = PerturbationMass.rightScaleMonotone
      siteGrowthEnvelope
      (Mass.squareRowMass gaugeRows
        (Contraction.flatGreenTimesPerturbationKernel background) row)
      Contraction.greenPerturbationContractionBound
      (ℚP.nonNegative⁻¹ siteGrowthEnvelope)
      (Contraction.selectedBackgroundFlatGreenPerturbationAbsoluteRowMassBound
        background radius row)
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        Mass.squareRowMass gaugeRows
          (Contraction.flatGreenTimesPerturbationKernel background) row
          * siteGrowthEnvelope
        ≤ upper)
      weightedContractionExactProduct scaled)

selectedBackgroundWeightedGreenPerturbationOneSixthContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root row →
  Mass.squareRowMass gaugeRows
    (weightedSelectedBackgroundResidual root background) row
  ≤ + 1 / 6
selectedBackgroundWeightedGreenPerturbationOneSixthContraction
    background radius root row =
  ℚP.≤-trans
    (selectedBackgroundWeightedGreenPerturbationAbsoluteRowMassBound
      background radius root row)
    weightedContractionBelowOneSixth

selectedBackgroundWeightedGreenPerturbationHalfContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root row →
  Mass.squareRowMass gaugeRows
    (weightedSelectedBackgroundResidual root background) row
  ≤ + 1 / 2
selectedBackgroundWeightedGreenPerturbationHalfContraction
    background radius root row =
  ℚP.≤-trans
    (selectedBackgroundWeightedGreenPerturbationOneSixthContraction
      background radius root row)
    oneSixthBelowOneHalf

selectedBackgroundRationalWeightInverseLawLevel : ProofLevel
selectedBackgroundRationalWeightInverseLawLevel = machineChecked

selectedBackgroundWeightedPerturbationContractionLevel : ProofLevel
selectedBackgroundWeightedPerturbationContractionLevel = machineChecked

scaleUniformWeightedContractionStillRequiredLevel : ProofLevel
scaleUniformWeightedContractionStillRequiredLevel = conditional
