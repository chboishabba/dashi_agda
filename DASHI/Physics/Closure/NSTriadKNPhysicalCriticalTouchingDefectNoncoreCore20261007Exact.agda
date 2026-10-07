module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectNoncoreCore20261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / CORE-NONCORE DEFECT AS ONE BINARY-PARTITION COVARIANCE
--
-- The previous exact owner already proved
--
--   defect = -[ Bip(DFL,Core) + Bip(DHH,Core) ].
--
-- DFL and DHH share the SAME Core side.  Bipartite covariance is additive in
-- its left list, so there is no reason to keep two analytic objects.  Fuse the
-- two deep lists into one literal noncore list
--
--   Noncore := DFL ++ DHH
--
-- and prove on the same physical fibre
--
--   defect = - Bip(Noncore,Core).
--
-- Consequently the eight-term DFL/Core + DHH/Core scalar normal form reduces
-- to the standard FOUR aggregate moments of one bipartite covariance, and the
-- two residual vectors reduce to ONE bipartite residual vector.  Sharp R579
-- Young then leaves exactly one physical vector-budget theorem.
--
-- No sign claim, norm estimate beyond the already-owned sharp Young theorem,
-- absolute-value observer, shell count, or new physical scalar is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact as Bip
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionFilteredExact as Filtered
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact as SplitRows
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectBipartite20261007Exact as Defect
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectVector20261007Exact as DefectVector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Generic additivity of bipartite covariance in the left carrier.
------------------------------------------------------------------------

bipartiteAppendLeft :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (left right core : List A) →
  Bip.bipartitePairSum rate work (left ++ right) core
  ≡ Bip.bipartitePairSum rate work left core
    + Bip.bipartitePairSum rate work right core
bipartiteAppendLeft rate work [] right core =
  solve (Bip.bipartitePairSum rate work right core ∷ [])
bipartiteAppendLeft rate work (head ∷ rest) right core
  rewrite bipartiteAppendLeft rate work rest right core =
  solve
    ( Bip.bipartiteRow rate work head core
    ∷ Bip.bipartitePairSum rate work rest core
    ∷ Bip.bipartitePairSum rate work right core
    ∷ [])

------------------------------------------------------------------------
-- 2. Fuse DFL and DHH into one literal noncore side.
------------------------------------------------------------------------

noncoreItems :
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
noncoreItems items =
  Filtered.deepFarLowItems items ++ Filtered.deepHighHighItems items

noncoreCoreCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
noncoreCoreCovariance rate work items =
  Bip.bipartitePairSum rate work
    (noncoreItems items)
    (Filtered.criticalCoreItems items)

defectCovarianceIsNoncoreCore :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Defect.defectCovariance rate work items
  ≡ noncoreCoreCovariance rate work items
defectCovarianceIsNoncoreCore rate work items =
  sym
    (bipartiteAppendLeft
      rate work
      (Filtered.deepFarLowItems items)
      (Filtered.deepHighHighItems items)
      (Filtered.criticalCoreItems items))

------------------------------------------------------------------------
-- 3. The old eight aggregate moments collapse to one four-moment formula.
------------------------------------------------------------------------

noncoreCoreFourAggregate :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
noncoreCoreFourAggregate rate work items =
    Pair.natAsRational (length (Filtered.criticalCoreItems items))
      * Pair.weightedWorkSum rate work (noncoreItems items)
  + Pair.natAsRational (length (noncoreItems items))
      * Pair.weightedWorkSum rate work (Filtered.criticalCoreItems items)
  - Pair.rateSum rate (noncoreItems items)
      * Pair.workSum work (Filtered.criticalCoreItems items)
  - Pair.rateSum rate (Filtered.criticalCoreItems items)
      * Pair.workSum work (noncoreItems items)

noncoreCoreClosedForm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  noncoreCoreCovariance rate work items
  ≡ noncoreCoreFourAggregate rate work items
noncoreCoreClosedForm rate work items =
  Bip.bipartiteClosedForm
    rate work
    (noncoreItems items)
    (Filtered.criticalCoreItems items)

defectEightAggregateIsNoncoreCoreFourAggregate :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Defect.defectAggregateNormalForm rate work items
  ≡ noncoreCoreFourAggregate rate work items
defectEightAggregateIsNoncoreCoreFourAggregate rate work items =
  trans
    (sym (Defect.defectCovarianceClosedForm rate work items))
    (trans
      (defectCovarianceIsNoncoreCore rate work items)
      (noncoreCoreClosedForm rate work items))

------------------------------------------------------------------------
-- 4. One residual vector for the binary partition.
------------------------------------------------------------------------

noncoreCoreResidualVector :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  C3.Complex3 F
noncoreCoreResidualVector rate value items =
  DefectVector.bipartiteResidualVector rate value
    (noncoreItems items)
    (Filtered.criticalCoreItems items)

noncoreCoreCovarianceIsVectorWork :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  noncoreCoreCovariance rate (Pair.cellWork mixed value) items
  ≡ Work.coherentWork mixed
      (noncoreCoreResidualVector rate value items)
noncoreCoreCovarianceIsVectorWork mixed rate value items =
  DefectVector.bipartiteCovarianceIsVectorWork
    mixed rate value
    (noncoreItems items)
    (Filtered.criticalCoreItems items)

------------------------------------------------------------------------
-- 5. Live same-object specialization and sharp Young envelope.
------------------------------------------------------------------------

module LiveNoncoreCore
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module R = SplitRows.LivePrincipalDefect physicalSystem S output
  module D = Defect.LiveDefectBipartite physicalSystem S output

  noncore : List Physical.PhysicalTriadIncidence
  noncore = noncoreItems R.items

  core : List Physical.PhysicalTriadIncidence
  core = Filtered.criticalCoreItems R.items

  covariance : ℚ
  covariance =
    noncoreCoreCovariance Rate.inputMass (Live.work output) R.items

  fourAggregate : ℚ
  fourAggregate =
    noncoreCoreFourAggregate Rate.inputMass (Live.work output) R.items

  residual : C3.Complex3 F
  residual =
    noncoreCoreResidualVector Rate.inputMass Live.value R.items

  defectIsNegativeNoncoreCore :
    R.defect ≡ 0ℚ - covariance
  defectIsNegativeNoncoreCore =
    trans
      D.defectIsNegativeBipartite
      (cong (0ℚ -_)
        (defectCovarianceIsNoncoreCore
          Rate.inputMass (Live.work output) R.items))

  defectIsNegativeFourAggregate :
    R.defect ≡ 0ℚ - fourAggregate
  defectIsNegativeFourAggregate =
    trans
      defectIsNegativeNoncoreCore
      (cong (0ℚ -_)
        (noncoreCoreClosedForm
          Rate.inputMass (Live.work output) R.items))

  defectIsNegativeVectorWork :
    R.defect
    ≡ 0ℚ - Work.coherentWork (Live.mixed output) residual
  defectIsNegativeVectorWork =
    trans
      defectIsNegativeNoncoreCore
      (cong (0ℚ -_)
        (noncoreCoreCovarianceIsVectorWork
          (Live.mixed output) Rate.inputMass Live.value R.items))

  negativeWorkBelowNorms :
    0ℚ - Work.coherentWork (Live.mixed output) residual
    ≤ L2.complex3NormSquared (Live.mixed output)
      + L2.complex3NormSquared residual
  negativeWorkBelowNorms =
    let
      cross = R179.realHermitianCross (Live.mixed output) residual
      meaning :
        0ℚ - Work.coherentWork (Live.mixed output) residual
        ≡ - (R579.two * cross)
      meaning = solve (cross ∷ [])
    in
    subst
      (_≤ L2.complex3NormSquared (Live.mixed output)
        + L2.complex3NormSquared residual)
      (sym meaning)
      (R579.negTwoRealCrossUpper (Live.mixed output) residual)

  defectBelowSharpVectorYoung :
    R.defect
    ≤ L2.complex3NormSquared (Live.mixed output)
      + L2.complex3NormSquared residual
  defectBelowSharpVectorYoung =
    subst
      (_≤ L2.complex3NormSquared (Live.mixed output)
        + L2.complex3NormSquared residual)
      (sym defectIsNegativeVectorWork)
      negativeWorkBelowNorms

------------------------------------------------------------------------
-- Status: exact fusion is closed; the physical budget is not.
------------------------------------------------------------------------

b4DefectNoncoreCoreBipartiteClosed : Bool
b4DefectNoncoreCoreBipartiteClosed = true

b4DefectNoncoreCoreFourAggregateClosed : Bool
b4DefectNoncoreCoreFourAggregateClosed = true

b4DefectNoncoreCoreVectorClosed : Bool
b4DefectNoncoreCoreVectorClosed = true

b4DefectNoncoreCoreSharpYoungClosed : Bool
b4DefectNoncoreCoreSharpYoungClosed = true

b4DefectNoncoreCorePhysicalBudgetClosed : Bool
b4DefectNoncoreCorePhysicalBudgetClosed = false

b4DefectNoncoreCoreIntroducesEstimate : Bool
b4DefectNoncoreCoreIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

b4DefectNoncoreCoreBipartiteClosedIsTrue :
  b4DefectNoncoreCoreBipartiteClosed ≡ true
b4DefectNoncoreCoreBipartiteClosedIsTrue = refl

b4DefectNoncoreCoreFourAggregateClosedIsTrue :
  b4DefectNoncoreCoreFourAggregateClosed ≡ true
b4DefectNoncoreCoreFourAggregateClosedIsTrue = refl

b4DefectNoncoreCoreVectorClosedIsTrue :
  b4DefectNoncoreCoreVectorClosed ≡ true
b4DefectNoncoreCoreVectorClosedIsTrue = refl

b4DefectNoncoreCoreSharpYoungClosedIsTrue :
  b4DefectNoncoreCoreSharpYoungClosed ≡ true
b4DefectNoncoreCoreSharpYoungClosedIsTrue = refl

b4DefectNoncoreCorePhysicalBudgetClosedIsFalse :
  b4DefectNoncoreCorePhysicalBudgetClosed ≡ false
b4DefectNoncoreCorePhysicalBudgetClosedIsFalse = refl
