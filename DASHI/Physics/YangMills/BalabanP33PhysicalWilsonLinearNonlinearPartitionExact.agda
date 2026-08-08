module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Canonically partition every one of the sixteen physical Wilson placement
-- defects into its first-order and higher-order selected-factor pieces.  For
-- Ai = Bi + Di, exact ordered quaternion multiplication gives
--
--   A0 A1 A2 A3 - B0 B1 B2 B3
--     = sum_{|S|=1} Product(B,D;S)
--       + sum_{|S|>=2} Product(B,D;S).
--
-- There are exactly four singleton terms and eleven higher-order terms.  The
-- multiplication order is unchanged in every term; no quaternion
-- commutativity is used.  The construction is instantiated on each named
-- diagonal/cross Wilson placement and then summed over all sixteen placements.
-- Consequently the Round-34 `linearPart + groupedRemainder` equality is no
-- longer a caller-selected decomposition: it is the literal finite expansion
-- of the computed physical Wilson defect.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
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
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementTelescopeExact as Named
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonNamedAtomSumExact as NamedSum
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as WilsonGlobal
import DASHI.Physics.YangMills.BalabanP33PhysicalLinearRemainderWLocalExact as WLocal
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as Instantiation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Coercivity
import DASHI.Physics.YangMills.BalabanP33PhysicalTerminalHessianCoercivityExact as Terminal
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

factorDefect :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
factorDefect = Telescope._-q_

fourFactorSingletonTerms :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.RationalQuaternion
fourFactorSingletonTerms a0 a1 a2 a3 b0 b1 b2 b3 =
  Telescope.orderedProduct4 (factorDefect a0 b0) b1 b2 b3 ∷
  Telescope.orderedProduct4 b0 (factorDefect a1 b1) b2 b3 ∷
  Telescope.orderedProduct4 b0 b1 (factorDefect a2 b2) b3 ∷
  Telescope.orderedProduct4 b0 b1 b2 (factorDefect a3 b3) ∷ []

fourFactorHigherTerms :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.RationalQuaternion
fourFactorHigherTerms a0 a1 a2 a3 b0 b1 b2 b3 =
  let
    d0 = factorDefect a0 b0
    d1 = factorDefect a1 b1
    d2 = factorDefect a2 b2
    d3 = factorDefect a3 b3
  in
  Telescope.orderedProduct4 d0 d1 b2 b3 ∷
  Telescope.orderedProduct4 d0 b1 d2 b3 ∷
  Telescope.orderedProduct4 d0 b1 b2 d3 ∷
  Telescope.orderedProduct4 b0 d1 d2 b3 ∷
  Telescope.orderedProduct4 b0 d1 b2 d3 ∷
  Telescope.orderedProduct4 b0 b1 d2 d3 ∷
  Telescope.orderedProduct4 d0 d1 d2 b3 ∷
  Telescope.orderedProduct4 d0 d1 b2 d3 ∷
  Telescope.orderedProduct4 d0 b1 d2 d3 ∷
  Telescope.orderedProduct4 b0 d1 d2 d3 ∷
  Telescope.orderedProduct4 d0 d1 d2 d3 ∷ []

fourFactorSingletonCountExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  length (fourFactorSingletonTerms a0 a1 a2 a3 b0 b1 b2 b3) ≡ 4
fourFactorSingletonCountExact a0 a1 a2 a3 b0 b1 b2 b3 = refl

fourFactorHigherCountExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  length (fourFactorHigherTerms a0 a1 a2 a3 b0 b1 b2 b3) ≡ 11
fourFactorHigherCountExact a0 a1 a2 a3 b0 b1 b2 b3 = refl

fourFactorLinearPart :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
fourFactorLinearPart a0 a1 a2 a3 b0 b1 b2 b3 =
  Q.sumQuaternion
    (fourFactorSingletonTerms a0 a1 a2 a3 b0 b1 b2 b3)

fourFactorNonlinearRemainder :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion
fourFactorNonlinearRemainder a0 a1 a2 a3 b0 b1 b2 b3 =
  Q.sumQuaternion
    (fourFactorHigherTerms a0 a1 a2 a3 b0 b1 b2 b3)

fourFactorLinearNonlinearExpansionExact :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Telescope._-q_
    (Telescope.orderedProduct4 a0 a1 a2 a3)
    (Telescope.orderedProduct4 b0 b1 b2 b3)
  ≡ fourFactorLinearPart a0 a1 a2 a3 b0 b1 b2 b3
    Q.+q fourFactorNonlinearRemainder a0 a1 a2 a3 b0 b1 b2 b3
fourFactorLinearNonlinearExpansionExact
    (Q.quat a00 a01 a02 a03)
    (Q.quat a10 a11 a12 a13)
    (Q.quat a20 a21 a22 a23)
    (Q.quat a30 a31 a32 a33)
    (Q.quat b00 b01 b02 b03)
    (Q.quat b10 b11 b12 b13)
    (Q.quat b20 b21 b22 b23)
    (Q.quat b30 b31 b32 b33) =
  Q.quaternionExt
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)
    (ℚRing.solve-∀
      a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33
      b00 b01 b02 b03 b10 b11 b12 b13
      b20 b21 b22 b23 b30 b31 b32 b33)

fourFactorTelescopeIsLinearPlusNonlinear :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 →
  Telescope.fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3
  ≡ fourFactorLinearPart a0 a1 a2 a3 b0 b1 b2 b3
    Q.+q fourFactorNonlinearRemainder a0 a1 a2 a3 b0 b1 b2 b3
fourFactorTelescopeIsLinearPlusNonlinear a0 a1 a2 a3 b0 b1 b2 b3 =
  trans
    (sym
      (Telescope.fourFactorDifferenceTelescopeExact
        a0 a1 a2 a3 b0 b1 b2 b3))
    (fourFactorLinearNonlinearExpansionExact
      a0 a1 a2 a3 b0 b1 b2 b3)

wilsonScalarAddExact : ∀ left right →
  Telescope.wilsonScalar (left Q.+q right)
  ≡ Telescope.wilsonScalar left + Telescope.wilsonScalar right
wilsonScalarAddExact
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3) =
  ℚRing.solve-∀ a0 b0

record PlacementSelectedFactors : Set where
  field
    a0 a1 a2 a3 : Q.RationalQuaternion
    b0 b1 b2 b3 : Q.RationalQuaternion

open PlacementSelectedFactors public

physicalPlacementSelectedFactors :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 →
  PlacementSelectedFactors
physicalPlacementSelectedFactors background field plaquette placement =
  let
    backgroundData = Physical.plaquetteJetData background field plaquette
    identityData =
      Physical.plaquetteJetData Physical.identityBackground field plaquette
  in
  record
    { a0 = Named.selectedFactor0 (Jets.link0 backgroundData) placement
    ; a1 = Named.selectedFactor1 (Jets.link1 backgroundData) placement
    ; a2 = Named.selectedFactor2 (Jets.link2 backgroundData) placement
    ; a3 = Named.selectedFactor3 (Jets.link3 backgroundData) placement
    ; b0 = Named.selectedFactor0 (Jets.link0 identityData) placement
    ; b1 = Named.selectedFactor1 (Jets.link1 identityData) placement
    ; b2 = Named.selectedFactor2 (Jets.link2 identityData) placement
    ; b3 = Named.selectedFactor3 (Jets.link3 identityData) placement
    }

placementLinearQuaternionDefect :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → Q.RationalQuaternion
placementLinearQuaternionDefect background field plaquette placement =
  let factors = physicalPlacementSelectedFactors
        background field plaquette placement
  in
  fourFactorLinearPart
    (a0 factors) (a1 factors) (a2 factors) (a3 factors)
    (b0 factors) (b1 factors) (b2 factors) (b3 factors)

placementNonlinearQuaternionRemainder :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → Q.RationalQuaternion
placementNonlinearQuaternionRemainder background field plaquette placement =
  let factors = physicalPlacementSelectedFactors
        background field plaquette placement
  in
  fourFactorNonlinearRemainder
    (a0 factors) (a1 factors) (a2 factors) (a3 factors)
    (b0 factors) (b1 factors) (b2 factors) (b3 factors)

placementLinearWilsonPart :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → ℚ
placementLinearWilsonPart background field plaquette placement =
  Telescope.wilsonScalar
    (placementLinearQuaternionDefect background field plaquette placement)

placementNonlinearWilsonRemainder :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → ℚ
placementNonlinearWilsonRemainder background field plaquette placement =
  Telescope.wilsonScalar
    (placementNonlinearQuaternionRemainder
      background field plaquette placement)

physicalPlacementWilsonDefectLinearNonlinearExact :
  ∀ background field plaquette placement →
  Named.physicalPlacementWilsonScalarDefect
    background field plaquette placement
  ≡ placementLinearWilsonPart background field plaquette placement
    + placementNonlinearWilsonRemainder
        background field plaquette placement
physicalPlacementWilsonDefectLinearNonlinearExact
    background field plaquette placement =
  let
    factors = physicalPlacementSelectedFactors
      background field plaquette placement

    telescopeSplit = fourFactorTelescopeIsLinearPlusNonlinear
      (a0 factors) (a1 factors) (a2 factors) (a3 factors)
      (b0 factors) (b1 factors) (b2 factors) (b3 factors)
  in
  trans
    (Named.physicalPlacementWilsonScalarDefectTelescopeExact
      background field plaquette placement)
    (trans
      (cong Telescope.wilsonScalar telescopeSplit)
      (wilsonScalarAddExact
        (fourFactorLinearPart
          (a0 factors) (a1 factors) (a2 factors) (a3 factors)
          (b0 factors) (b1 factors) (b2 factors) (b3 factors))
        (fourFactorNonlinearRemainder
          (a0 factors) (a1 factors) (a2 factors) (a3 factors)
          (b0 factors) (b1 factors) (b2 factors) (b3 factors))))

sumMapCong :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≡ right value) →
  NamedSum.sumMap values left ≡ NamedSum.sumMap values right
sumMapCong [] left right pointwise = refl
sumMapCong (value ∷ values) left right pointwise =
  cong₂ _+_
    (pointwise value)
    (sumMapCong values left right pointwise)

sumMapPointwiseAdd :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  NamedSum.sumMap values (λ value → left value + right value)
  ≡ NamedSum.sumMap values left + NamedSum.sumMap values right
sumMapPointwiseAdd [] left right = ℚRing.solve []
sumMapPointwiseAdd (value ∷ values) left right
  rewrite sumMapPointwiseAdd values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (NamedSum.sumMap values left) (NamedSum.sumMap values right)

physicalPlaquetteWilsonLinearPart :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
physicalPlaquetteWilsonLinearPart background field plaquette =
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementLinearWilsonPart background field plaquette)

physicalPlaquetteGroupedNonlinearRemainder :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → ℚ
physicalPlaquetteGroupedNonlinearRemainder background field plaquette =
  NamedSum.sumMap Placement.plaquetteSecondVariationPlacements4
    (placementNonlinearWilsonRemainder background field plaquette)

physicalPlacementDefectSumSplitsExact :
  ∀ background field plaquette →
  NamedSum.physicalPlacementWilsonDefectSum background field plaquette
  ≡ physicalPlaquetteWilsonLinearPart background field plaquette
    + physicalPlaquetteGroupedNonlinearRemainder background field plaquette
physicalPlacementDefectSumSplitsExact background field plaquette =
  trans
    (sumMapCong
      Placement.plaquetteSecondVariationPlacements4
      (Named.physicalPlacementWilsonScalarDefect
        background field plaquette)
      (λ placement →
        placementLinearWilsonPart background field plaquette placement
        + placementNonlinearWilsonRemainder
            background field plaquette placement)
      (physicalPlacementWilsonDefectLinearNonlinearExact
        background field plaquette))
    (sumMapPointwiseAdd
      Placement.plaquetteSecondVariationPlacements4
      (placementLinearWilsonPart background field plaquette)
      (placementNonlinearWilsonRemainder background field plaquette))

physicalPlaquetteWilsonDefectLinearNonlinearExact :
  ∀ background field plaquette →
  Physical.plaquetteWilsonSecondVariation background field plaquette
    - Physical.plaquetteWilsonSecondVariation
        Physical.identityBackground field plaquette
  ≡ physicalPlaquetteWilsonLinearPart background field plaquette
    + physicalPlaquetteGroupedNonlinearRemainder background field plaquette
physicalPlaquetteWilsonDefectLinearNonlinearExact background field plaquette =
  trans
    (sym
      (NamedSum.physicalPlacementWilsonDefectSumExact
        background field plaquette))
    (physicalPlacementDefectSumSplitsExact background field plaquette)

record CanonicalPhysicalWilsonBounds
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4) : Set₁ where
  field
    canonicalLinearLower : ∀ plaquette →
      - (WilsonGlobal.rhoOverThirtySix
          * WilsonGlobal.plaquetteCrossCharge field plaquette)
      ≤ physicalPlaquetteWilsonLinearPart background field plaquette

    canonicalGroupedNonlinearLower : ∀ plaquette →
      - (WilsonGlobal.rhoOverOneFortyFour
          * WilsonGlobal.plaquetteDiagonalCharge field plaquette)
      ≤ physicalPlaquetteGroupedNonlinearRemainder background field plaquette

open CanonicalPhysicalWilsonBounds public

canonicalBoundsAsRound34Control :
  ∀ {background field} →
  CanonicalPhysicalWilsonBounds background field →
  WLocal.PhysicalPlaquetteLinearRemainderControl background field
canonicalBoundsAsRound34Control {background} {field} bounds = record
  { WLocal.PhysicalPlaquetteLinearRemainderControl.physicalLinearPart =
      physicalPlaquetteWilsonLinearPart background field
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.physicalGroupedRemainder =
      physicalPlaquetteGroupedNonlinearRemainder background field
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.physicalDecomposition =
      physicalPlaquetteWilsonDefectLinearNonlinearExact background field
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.selectedCurvatureLinearLower =
      canonicalLinearLower bounds
  ; WLocal.PhysicalPlaquetteLinearRemainderControl.groupedSixteenAtomRemainderLower =
      canonicalGroupedNonlinearLower bounds
  }

canonicalBoundsImplyWLocal :
  ∀ {background field} →
  CanonicalPhysicalWilsonBounds background field →
  WilsonGlobal.PhysicalWilsonSignedLocal background field
canonicalBoundsImplyWLocal bounds =
  WLocal.physicalLinearRemainderControlImpliesWLocal
    (canonicalBoundsAsRound34Control bounds)

selectedVariationalCanonicalTerminalCoefficient :
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
  CanonicalPhysicalWilsonBounds
    (Coercivity.backgroundOf (Instantiation.model family) h)
    (Coercivity.physicalFieldOf (Instantiation.model family) h) →
  Terminal.terminalPhysicalCoefficient
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation
        (Instantiation.model family) h)
selectedVariationalCanonicalTerminalCoefficient family h bounds =
  WLocal.selectedVariationalCorrelationTerminalCoefficient
    family h (canonicalBoundsAsRound34Control bounds)

selectedVariationalCanonicalOneThirtySecond :
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
  CanonicalPhysicalWilsonBounds
    (Coercivity.backgroundOf (Instantiation.model family) h)
    (Coercivity.physicalFieldOf (Instantiation.model family) h) →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation
        (Instantiation.model family) h)
selectedVariationalCanonicalOneThirtySecond family h bounds =
  WLocal.selectedVariationalCorrelationOneThirtySecond
    family h (canonicalBoundsAsRound34Control bounds)

physicalWilsonLinearNonlinearPartitionLevel : ProofLevel
physicalWilsonLinearNonlinearPartitionLevel = machineChecked

physicalWilsonCanonicalBoundsLevel : ProofLevel
physicalWilsonCanonicalBoundsLevel = conditional
