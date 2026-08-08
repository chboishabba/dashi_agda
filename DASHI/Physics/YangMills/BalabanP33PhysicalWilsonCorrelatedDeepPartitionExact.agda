module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- Refine the canonical four-singleton/eleven-higher-order partition according
-- to the exact configured budgets.  The six quadratic subset terms are joined
-- to the four singleton terms in the correlated channel.  The grouped deep
-- remainder contains exactly the four cubic terms and the quartic term.
--
-- For every one of the sixteen named Wilson placements and then for the
-- literal plaquette sum, prove exactly
--
--   Wilson defect = correlated(singleton + pair) + deep(triple + quartic).
--
-- The decomposition is canonical and noncommutative.  The only remaining
-- caller inputs are the signed lower estimates on these two constructed
-- quantities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length; _++_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonNamedAtomSumExact as NamedSum
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as WilsonGlobal
import DASHI.Physics.YangMills.BalabanP33PhysicalLinearRemainderWLocalExact as WLocal
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as Instantiation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Coercivity
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalTerminalHessianCoercivityExact as Terminal
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

fourFactorPairTerms :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.RationalQuaternion
fourFactorPairTerms a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    d0 = Partition.factorDefect a0 b0
    d1 = Partition.factorDefect a1 b1
    d2 = Partition.factorDefect a2 b2
    d3 = Partition.factorDefect a3 b3
  in
  Telescope.orderedProduct4 d0 d1 b2 b3 ∷
  Telescope.orderedProduct4 d0 b1 d2 b3 ∷
  Telescope.orderedProduct4 d0 b1 b2 d3 ∷
  Telescope.orderedProduct4 b0 d1 d2 b3 ∷
  Telescope.orderedProduct4 b0 d1 b2 d3 ∷
  Telescope.orderedProduct4 b0 b1 d2 d3 ∷ []

fourFactorDeepTerms :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.RationalQuaternion
fourFactorDeepTerms a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    d0 = Partition.factorDefect a0 b0
    d1 = Partition.factorDefect a1 b1
    d2 = Partition.factorDefect a2 b2
    d3 = Partition.factorDefect a3 b3
  in
  Telescope.orderedProduct4 d0 d1 d2 b3 ∷
  Telescope.orderedProduct4 d0 d1 b2 d3 ∷
  Telescope.orderedProduct4 d0 b1 d2 d3 ∷
  Telescope.orderedProduct4 b0 d1 d2 d3 ∷
  Telescope.orderedProduct4 d0 d1 d2 d3 ∷ []

fourFactorPairCountExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  length (fourFactorPairTerms a0 a1 a2 a3 b0 b1 b2 b3) ≡ 6
fourFactorPairCountExact a0 a1 a2 a3 b0 b1 b2 b3 = refl

fourFactorDeepCountExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  length (fourFactorDeepTerms a0 a1 a2 a3 b0 b1 b2 b3) ≡ 5
fourFactorDeepCountExact a0 a1 a2 a3 b0 b1 b2 b3 = refl

higherTermsArePairAppendDeep :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Partition.fourFactorHigherTerms a0 a1 a2 a3 b0 b1 b2 b3
  ≡ fourFactorPairTerms a0 a1 a2 a3 b0 b1 b2 b3
    ++ fourFactorDeepTerms a0 a1 a2 a3 b0 b1 b2 b3
higherTermsArePairAppendDeep a0 a1 a2 a3 b0 b1 b2 b3 = refl

fourFactorPairPart :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
fourFactorPairPart a0 a1 a2 a3 b0 b1 b2 b3 =
  Q.sumQuaternion
    (fourFactorPairTerms a0 a1 a2 a3 b0 b1 b2 b3)

fourFactorDeepRemainder :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
fourFactorDeepRemainder a0 a1 a2 a3 b0 b1 b2 b3 =
  Q.sumQuaternion
    (fourFactorDeepTerms a0 a1 a2 a3 b0 b1 b2 b3)

fourFactorHigherSplitsPairDeep :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Partition.fourFactorNonlinearRemainder
    a0 a1 a2 a3 b0 b1 b2 b3
  ≡ fourFactorPairPart a0 a1 a2 a3 b0 b1 b2 b3
    Q.+q fourFactorDeepRemainder a0 a1 a2 a3 b0 b1 b2 b3
fourFactorHigherSplitsPairDeep a0 a1 a2 a3 b0 b1 b2 b3 =
  trans
    (cong Q.sumQuaternion
      (higherTermsArePairAppendDeep a0 a1 a2 a3 b0 b1 b2 b3))
    (Q.sumQuaternionAppend
      (fourFactorPairTerms a0 a1 a2 a3 b0 b1 b2 b3)
      (fourFactorDeepTerms a0 a1 a2 a3 b0 b1 b2 b3))

fourFactorCorrelatedPart :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
fourFactorCorrelatedPart a0 a1 a2 a3 b0 b1 b2 b3 =
  Partition.fourFactorLinearPart a0 a1 a2 a3 b0 b1 b2 b3
  Q.+q fourFactorPairPart a0 a1 a2 a3 b0 b1 b2 b3

fourFactorCorrelatedDeepExpansionExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Telescope._-q_
    (Telescope.orderedProduct4 a0 a1 a2 a3)
    (Telescope.orderedProduct4 b0 b1 b2 b3)
  ≡ fourFactorCorrelatedPart a0 a1 a2 a3 b0 b1 b2 b3
    Q.+q fourFactorDeepRemainder a0 a1 a2 a3 b0 b1 b2 b3
fourFactorCorrelatedDeepExpansionExact a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    linear = Partition.fourFactorLinearPart
      a0 a1 a2 a3 b0 b1 b2 b3
    pair = fourFactorPairPart a0 a1 a2 a3 b0 b1 b2 b3
    deep = fourFactorDeepRemainder a0 a1 a2 a3 b0 b1 b2 b3
  in
  trans
    (Partition.fourFactorLinearNonlinearExpansionExact
      a0 a1 a2 a3 b0 b1 b2 b3)
    (trans
      (cong (linear Q.+q_)
        (fourFactorHigherSplitsPairDeep
          a0 a1 a2 a3 b0 b1 b2 b3))
      (sym (Q.quaternionAddAssociative linear pair deep)))

placementPairQuaternionPart :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → Q.RationalQuaternion
placementPairQuaternionPart background field plaquette placement =
  let factors = Partition.physicalPlacementSelectedFactors
        background field plaquette placement
  in
  fourFactorPairPart
    (Partition.a0 factors) (Partition.a1 factors)
    (Partition.a2 factors) (Partition.a3 factors)
    (Partition.b0 factors) (Partition.b1 factors)
    (Partition.b2 factors) (Partition.b3 factors)

placementDeepQuaternionRemainder :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → Q.RationalQuaternion
placementDeepQuaternionRemainder background field plaquette placement =
  let factors = Partition.physicalPlacementSelectedFactors
        background field plaquette placement
  in
  fourFactorDeepRemainder
    (Partition.a0 factors) (Partition.a1 factors)
    (Partition.a2 factors) (Partition.a3 factors)
    (Partition.b0 factors) (Partition.b1 factors)
    (Partition.b2 factors) (Partition.b3 factors)

placementCorrelatedWilsonPart :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → ℚ
placementCorrelatedWilsonPart background field plaquette placement =
  Partition.placementLinearWilsonPart background field plaquette placement
  + Telescope.wilsonScalar
      (placementPairQuaternionPart background field plaquette placement)

placementDeepWilsonRemainder :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → ℚ
placementDeepWilsonRemainder background field plaquette placement =
  Telescope.wilsonScalar
    (placementDeepQuaternionRemainder background field plaquette placement)

physicalPlacementWilsonDefectCorrelatedDeepExact :
  ∀ background field plaquette placement →
  Partition.placementLinearWilsonPart background field plaquette placement
    + Partition.placementNonlinearWilsonRemainder
        background field plaquette placement
  ≡ placementCorrelatedWilsonPart background field plaquette placement
    + placementDeepWilsonRemainder background field plaquette placement
physicalPlacementWilsonDefectCorrelatedDeepExact
    background field plaquette placement =
  let
    factors = Partition.physicalPlacementSelectedFactors
      background field plaquette placement
    linear = Partition.placementLinearWilsonPart
      background field plaquette placement
    pair = fourFactorPairPart
      (Partition.a0 factors) (Partition.a1 factors)
      (Partition.a2 factors) (Partition.a3 factors)
      (Partition.b0 factors) (Partition.b1 factors)
      (Partition.b2 factors) (Partition.b3 factors)
    deep = fourFactorDeepRemainder
      (Partition.a0 factors) (Partition.a1 factors)
      (Partition.a2 factors) (Partition.a3 factors)
      (Partition.b0 factors) (Partition.b1 factors)
      (Partition.b2 factors) (Partition.b3 factors)
  in
  trans
    (cong (linear +_)
      (trans
        (cong Telescope.wilsonScalar
          (fourFactorHigherSplitsPairDeep
            (Partition.a0 factors) (Partition.a1 factors)
            (Partition.a2 factors) (Partition.a3 factors)
            (Partition.b0 factors) (Partition.b1 factors)
            (Partition.b2 factors) (Partition.b3 factors)))
        (Partition.wilsonScalarAddExact pair deep)))
    (ℚRing.solve-∀
      linear (Telescope.wilsonScalar pair) (Telescope.wilsonScalar deep))

placementWilsonDefectCorrelatedDeepExact :
  ∀ background field plaquette placement →
  Partition.placementLinearWilsonPart background field plaquette placement
    + Partition.placementNonlinearWilsonRemainder
        background field plaquette placement
  ≡ placementCorrelatedWilsonPart background field plaquette placement
    + placementDeepWilsonRemainder background field plaquette placement
placementWilsonDefectCorrelatedDeepExact =
  physicalPlacementWilsonDefectCorrelatedDeepExact

physicalPlaquetteCorrelatedWilsonPart :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
physicalPlaquetteCorrelatedWilsonPart background field plaquette =
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementCorrelatedWilsonPart background field plaquette)

physicalPlaquetteDeepWilsonRemainder :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
physicalPlaquetteDeepWilsonRemainder background field plaquette =
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementDeepWilsonRemainder background field plaquette)

physicalPlaquetteCanonicalSplitRefinesExact :
  ∀ background field plaquette →
  Partition.physicalPlaquetteWilsonLinearPart background field plaquette
    + Partition.physicalPlaquetteGroupedNonlinearRemainder
        background field plaquette
  ≡ physicalPlaquetteCorrelatedWilsonPart background field plaquette
    + physicalPlaquetteDeepWilsonRemainder background field plaquette
physicalPlaquetteCanonicalSplitRefinesExact background field plaquette =
  trans
    (sym
      (Partition.sumMapPointwiseAdd
        Placement.plaquetteSecondVariationPlacements4
        (Partition.placementLinearWilsonPart background field plaquette)
        (Partition.placementNonlinearWilsonRemainder
          background field plaquette)))
    (trans
      (Partition.sumMapCong
        Placement.plaquetteSecondVariationPlacements4
        (λ placement →
          Partition.placementLinearWilsonPart
            background field plaquette placement
          + Partition.placementNonlinearWilsonRemainder
            background field plaquette placement)
        (λ placement →
          placementCorrelatedWilsonPart background field plaquette placement
          + placementDeepWilsonRemainder background field plaquette placement)
        (physicalPlacementWilsonDefectCorrelatedDeepExact
          background field plaquette))
      (Partition.sumMapPointwiseAdd
        Placement.plaquetteSecondVariationPlacements4
        (placementCorrelatedWilsonPart background field plaquette)
        (placementDeepWilsonRemainder background field plaquette)))

physicalPlaquetteWilsonDefectCorrelatedDeepExact :
  ∀ background field plaquette →
  Physical.plaquetteWilsonSecondVariation background field plaquette
    - Physical.plaquetteWilsonSecondVariation
        Physical.identityBackground field plaquette
  ≡ physicalPlaquetteCorrelatedWilsonPart background field plaquette
    + physicalPlaquetteDeepWilsonRemainder background field plaquette
physicalPlaquetteWilsonDefectCorrelatedDeepExact background field plaquette =
  trans
    (Partition.physicalPlaquetteWilsonDefectLinearNonlinearExact
      background field plaquette)
    (physicalPlaquetteCanonicalSplitRefinesExact
      background field plaquette)

record RefinedCanonicalPhysicalWilsonBounds
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4) : Set₁ where
  field
    correlatedLower : ∀ plaquette →
      - (WilsonGlobal.rhoOverThirtySix
          * WilsonGlobal.plaquetteCrossCharge field plaquette)
      ≤ physicalPlaquetteCorrelatedWilsonPart background field plaquette

    deepRemainderLower : ∀ plaquette →
      - (WilsonGlobal.rhoOverOneFortyFour
          * WilsonGlobal.plaquetteDiagonalCharge field plaquette)
      ≤ physicalPlaquetteDeepWilsonRemainder background field plaquette

open RefinedCanonicalPhysicalWilsonBounds public

refinedBoundsAsRound34Control :
  ∀ {background field} →
  RefinedCanonicalPhysicalWilsonBounds background field →
  WLocal.PhysicalPlaquetteLinearRemainderControl background field
refinedBoundsAsRound34Control {background} {field} bounds = record
  { WLocal.PhysicalPlaquetteLinearRemainderControl.physicalLinearPart =
      physicalPlaquetteCorrelatedWilsonPart background field
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.physicalGroupedRemainder =
      physicalPlaquetteDeepWilsonRemainder background field
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.physicalDecomposition =
      physicalPlaquetteWilsonDefectCorrelatedDeepExact background field
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.selectedCurvatureLinearLower =
      correlatedLower bounds
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.groupedSixteenAtomRemainderLower =
      deepRemainderLower bounds
  }

refinedBoundsImplyWLocal :
  ∀ {background field} →
  RefinedCanonicalPhysicalWilsonBounds background field →
  WilsonGlobal.PhysicalWilsonSignedLocal background field
refinedBoundsImplyWLocal bounds =
  WLocal.physicalLinearRemainderControlImpliesWLocal
    (refinedBoundsAsRound34Control bounds)

selectedVariationalRefinedOneThirtySecond :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : Instantiation.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (Instantiation.bridge inputs)) coarse}
    (family : Instantiation.SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h →
  RefinedCanonicalPhysicalWilsonBounds
    (Coercivity.backgroundOf (Instantiation.model family) h)
    (Coercivity.physicalFieldOf (Instantiation.model family) h) →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation
        (Instantiation.model family) h)
selectedVariationalRefinedOneThirtySecond family h bounds =
  WLocal.selectedVariationalCorrelationOneThirtySecond
    family h (refinedBoundsAsRound34Control bounds)

physicalWilsonCorrelatedDeepPartitionLevel : ProofLevel
physicalWilsonCorrelatedDeepPartitionLevel = machineChecked

physicalWilsonCorrelatedLowerLevel : ProofLevel
physicalWilsonCorrelatedLowerLevel = conditional

physicalWilsonDeepRemainderLowerLevel : ProofLevel
physicalWilsonDeepRemainderLowerLevel = conditional
