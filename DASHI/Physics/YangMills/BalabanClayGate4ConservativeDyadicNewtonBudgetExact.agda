module DASHI.Physics.YangMills.BalabanClayGate4ConservativeDyadicNewtonBudgetExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact as Construction

------------------------------------------------------------------------
-- One deliberately conservative numerical budget for both Newton problems.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Marco Papi,
-- "On the Domain of the Implicit Function and Applications",
-- Journal of Inequalities and Applications 2005 (2005), 221--234.
-- DOI: 10.1155/JIA.2005.221.
--
-- The selected target is
--
--   radius = 1/2,  contraction <= 1/4,  forcing <= 1/4.
--
-- Hence q r + f <= 1/8 + 1/4 = 3/8 <= 1/2.  The theorem is scalar-
-- representation independent: a constructive-real instantiation supplies the
-- named dyadic constants and their order facts once, and both the Federbush
-- centre and Faddeev--Popov slice reuse the same invariant-ball proof.
------------------------------------------------------------------------

record DyadicNewtonConstants
    {Point Bound : Set}
    (triangle : Construction.MetricTriangleBudget Point Bound) : Set₁ where
  field
    half quarter eighth threeEighths : Bound

    quarterTimesHalf :
      Quantitative.multiply (Construction.metric triangle) quarter half
      ≡ eighth

    eighthPlusQuarter :
      Construction.add triangle eighth quarter ≡ threeEighths

    threeEighthsBelowHalf :
      Quantitative.LessEqual (Construction.metric triangle)
        threeEighths half

    quarterBelowOne :
      Quantitative.StrictlyBelowOne
        (Construction.metric triangle) quarter

    belowQuarterBelowOne : ∀ {value} →
      Quantitative.LessEqual (Construction.metric triangle)
        value quarter →
      Quantitative.StrictlyBelowOne
        (Construction.metric triangle) value

    multiplyMonotone : ∀ {left lower right upper} →
      Quantitative.LessEqual (Construction.metric triangle) left lower →
      Quantitative.LessEqual (Construction.metric triangle) right upper →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.multiply (Construction.metric triangle) left right)
        (Quantitative.multiply (Construction.metric triangle) lower upper)

open DyadicNewtonConstants public

dyadicContractionForcingFits :
  ∀ {Point Bound}
    {triangle : Construction.MetricTriangleBudget Point Bound}
    (constants : DyadicNewtonConstants triangle)
    contraction forcing radius →
  Quantitative.LessEqual (Construction.metric triangle)
    contraction (quarter constants) →
  Quantitative.LessEqual (Construction.metric triangle)
    forcing (quarter constants) →
  radius ≡ half constants →
  Quantitative.LessEqual (Construction.metric triangle)
    (Construction.add triangle
      (Quantitative.multiply (Construction.metric triangle)
        contraction radius)
      forcing)
    radius
dyadicContractionForcingFits {triangle = triangle}
    constants contraction forcing radius contractionBound forcingBound
    radiusMeaning =
  subst
    (λ selectedRadius →
      Quantitative.LessEqual (Construction.metric triangle)
        (Construction.add triangle
          (Quantitative.multiply (Construction.metric triangle)
            contraction selectedRadius)
          forcing)
        selectedRadius)
    (sym radiusMeaning)
    (Quantitative.transitive (Construction.metric triangle)
      (Construction.addMonotone triangle
        (subst
          (λ upper →
            Quantitative.LessEqual (Construction.metric triangle)
              (Quantitative.multiply (Construction.metric triangle)
                contraction (half constants)) upper)
          (quarterTimesHalf constants)
          (multiplyMonotone constants contractionBound
            (Quantitative.reflexive (Construction.metric triangle)
              (half constants))))
        forcingBound)
      (subst
        (λ lower →
          Quantitative.LessEqual (Construction.metric triangle)
            lower (half constants))
        (sym (eighthPlusQuarter constants))
        (threeEighthsBelowHalf constants)))

record ConservativeDyadicContractionBall
    {Point Bound : Set}
    {triangle : Construction.MetricTriangleBudget Point Bound}
    (constants : DyadicNewtonConstants triangle) : Set₁ where
  field
    centre : Point
    map : Point → Point

    radius contractionFactor forcing : Bound
    radiusMeaning : radius ≡ half constants

    InBall : Point → Set
    inBallMeaning : ∀ point →
      InBall point ≡ Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.distance (Construction.metric triangle)
          point centre)
        radius

    centreInBall : InBall centre

    centreDisplacement :
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.distance (Construction.metric triangle)
          (map centre) centre)
        forcing

    contractionEstimate : ∀ left right →
      InBall left → InBall right →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.distance (Construction.metric triangle)
          (map left) (map right))
        (Quantitative.multiply (Construction.metric triangle)
          contractionFactor
          (Quantitative.distance (Construction.metric triangle) left right))

    contractionBelowQuarter :
      Quantitative.LessEqual (Construction.metric triangle)
        contractionFactor (quarter constants)

    forcingBelowQuarter :
      Quantitative.LessEqual (Construction.metric triangle)
        forcing (quarter constants)

    multiplyRadiusMonotone : ∀ value →
      Quantitative.LessEqual (Construction.metric triangle) value radius →
      Quantitative.LessEqual (Construction.metric triangle)
        (Quantitative.multiply (Construction.metric triangle)
          contractionFactor value)
        (Quantitative.multiply (Construction.metric triangle)
          contractionFactor radius)

open ConservativeDyadicContractionBall public

asContractionBallConstruction :
  ∀ {Point Bound}
    {triangle : Construction.MetricTriangleBudget Point Bound}
    {constants : DyadicNewtonConstants triangle} →
  ConservativeDyadicContractionBall constants →
  Construction.ContractionBallConstruction triangle
asContractionBallConstruction {triangle = triangle}
    {constants = constants} dataSet = record
  { Construction.ContractionBallConstruction.centre = centre dataSet
  ; Construction.ContractionBallConstruction.radius = radius dataSet
  ; Construction.ContractionBallConstruction.contractionFactor =
      contractionFactor dataSet
  ; Construction.ContractionBallConstruction.forcing = forcing dataSet
  ; Construction.ContractionBallConstruction.map = map dataSet
  ; Construction.ContractionBallConstruction.InBall = InBall dataSet
  ; Construction.ContractionBallConstruction.inBallMeaning =
      inBallMeaning dataSet
  ; Construction.ContractionBallConstruction.centreInBall =
      centreInBall dataSet
  ; Construction.ContractionBallConstruction.centreDisplacement =
      centreDisplacement dataSet
  ; Construction.ContractionBallConstruction.contractionEstimate =
      contractionEstimate dataSet
  ; Construction.ContractionBallConstruction.contractionFactorBelowOne =
      belowQuarterBelowOne constants (contractionBelowQuarter dataSet)
  ; Construction.ContractionBallConstruction.multiplyRadiusMonotone =
      multiplyRadiusMonotone dataSet
  ; Construction.ContractionBallConstruction.contractedRadiusPlusForcingFits =
      dyadicContractionForcingFits constants
        (contractionFactor dataSet)
        (forcing dataSet)
        (radius dataSet)
        (contractionBelowQuarter dataSet)
        (forcingBelowQuarter dataSet)
        (radiusMeaning dataSet)
  }

record FederbushFaddeevPopovDyadicNewtonReuse
    {PointBF PointFP Bound : Set}
    {triangleBF : Construction.MetricTriangleBudget PointBF Bound}
    {triangleFP : Construction.MetricTriangleBudget PointFP Bound}
    (constantsBF : DyadicNewtonConstants triangleBF)
    (constantsFP : DyadicNewtonConstants triangleFP) : Set₁ where
  field
    federbushCentre : ConservativeDyadicContractionBall constantsBF
    faddeevPopovSlice : ConservativeDyadicContractionBall constantsFP

open FederbushFaddeevPopovDyadicNewtonReuse public

conservativeDyadicNewtonArithmeticLevel : ProofLevel
conservativeDyadicNewtonArithmeticLevel = machineChecked

conservativeDyadicInvariantBallAdapterLevel : ProofLevel
conservativeDyadicInvariantBallAdapterLevel = machineChecked

federbushFaddeevPopovDyadicReuseLevel : ProofLevel
federbushFaddeevPopovDyadicReuseLevel = machineChecked

physicalFederbushQuarterBoundsInputsLevel : ProofLevel
physicalFederbushQuarterBoundsInputsLevel = conditional

physicalFaddeevPopovQuarterBoundsInputsLevel : ProofLevel
physicalFaddeevPopovQuarterBoundsInputsLevel = conditional
