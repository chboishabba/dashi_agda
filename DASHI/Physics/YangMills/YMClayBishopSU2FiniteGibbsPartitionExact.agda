module DASHI.Physics.YangMills.YMClayBishopSU2FiniteGibbsPartitionExact where

------------------------------------------------------------------------
-- FINITE SAME-BISHOP-CARRIER SU2 WILSON GIBBS PARTITION.
--
-- The source-positive *actual* Bishop exponential of the nonnegative
-- finite quaternion Wilson action, the actual Bishop inverse, and
-- the existing nonempty finite positive-weight integration compiler
-- compose without an assumed physical integral or free partition sign.
--
-- This is a finite cubature family on lists of SU2 plaquette holonomies,
-- NOT the original physical lattice link-to-plaquette map or a Haar
-- completion. YM.REAL ORIGINAL-SOURCE GATE REMAINS OPEN.
--
-- Attribution: Wilson/Balaban; Bishop/Bridges; Murray/Csimma; DASHI
-- source positive quaternion, exponential and finite integral owners.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
import Real as B
import RealProperties as P
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact
  as Global
import DASHI.Physics.YangMills.YMClayBishopSU2DeterminantExact as SU2
import DASHI.Physics.YangMills.YMClayBishopSU2WilsonDeficitPositiveExact
  as Wilson
import DASHI.Physics.YangMills.YMClayBishopFiniteWilsonNormalizedExact
  as Finite

Configuration : Set
Configuration = List SU2.UnitQuaternion

density : B.ℝ → Configuration → B.ℝ
density beta cfg =
  Exp.bishopExp
    (B.- (Wilson.finiteSU2WilsonAction beta cfg))

densityPositive :
  ∀ beta → B.NonNegative beta →
  ∀ cfg → B._<_ B.0ℝ (density beta cfg)
densityPositive beta betaNN cfg =
  Wilson.finiteSU2WilsonGibbsWeightPositive beta betaNN cfg

oneTimesDensityPositive :
  ∀ beta → B.NonNegative beta →
  ∀ cfg → B._<_ B.0ℝ (B._*_ B.1ℝ (density beta cfg))
oneTimesDensityPositive beta betaNN cfg =
  P.posx⇒0<x
    (P.posx,y⇒posx*y
      (P.0<x⇒posx Global.onePositive)
      (P.0<x⇒posx (densityPositive beta betaNN cfg)))

oneTimesDensityNonnegative :
  ∀ beta → B.NonNegative beta →
  ∀ cfg → B.NonNegative (B._*_ B.1ℝ (density beta cfg))
oneTimesDensityNonnegative beta betaNN cfg =
  P.pos⇒nonNeg
    (P.0<x⇒posx (oneTimesDensityPositive beta betaNN cfg))

-- A literal nonempty finite quadrature with one positive weight and
-- the remaining nonnegative weights is enough to derive Z>0.
-- There is NO externally assumed positive-partition witness here.
finiteGibbsPartitionStrictlyPositive :
  ∀ beta →
  (betaNN : B.NonNegative beta) →
  (first : Finite.WeightedConfiguration Configuration) →
  (rest : List (Finite.WeightedConfiguration Configuration)) →
  B._<_ B.0ℝ (Finite.weight first) →
  Finite.All
    (λ node → B.NonNegative (Finite.weight node)) rest →
  B._<_ B.0ℝ
    (Finite.partition (first ∷ rest) (density beta))
finiteGibbsPartitionStrictlyPositive
    beta betaNN first rest firstWeightPositive restWeightsNN =
  Finite.weightedSumStrictPositiveHead
    first rest
    (λ cfg → B._*_ B.1ℝ (density beta cfg))
    firstWeightPositive
    (oneTimesDensityPositive beta betaNN (Finite.point first))
    restWeightsNN
    (oneTimesDensityNonnegative beta betaNN)

-- Genuine normalized expectation of 1 on the finite selected weighted
-- Bishop configuration list. No free divide and no free partition sign.
finiteGibbsNormalizedExpectationOne :
  ∀ beta →
  (betaNN : B.NonNegative beta) →
  (first : Finite.WeightedConfiguration Configuration) →
  (rest : List (Finite.WeightedConfiguration Configuration)) →
  (firstWeightPositive : B._<_ B.0ℝ (Finite.weight first)) →
  (restWeightsNN :
    Finite.All
      (λ node → B.NonNegative (Finite.weight node)) rest) →
  B._≃_
    (Finite.normalizedExpectation
      (first ∷ rest) (density beta)
      (finiteGibbsPartitionStrictlyPositive beta betaNN
        first rest firstWeightPositive restWeightsNN)
      (λ _ → B.1ℝ))
    B.1ℝ
finiteGibbsNormalizedExpectationOne
    beta betaNN first rest firstWeightPositive restWeightsNN =
  Finite.normalizedExpectationOne
    (first ∷ rest)
    (density beta)
    (finiteGibbsPartitionStrictlyPositive beta betaNN
      first rest firstWeightPositive restWeightsNN)
