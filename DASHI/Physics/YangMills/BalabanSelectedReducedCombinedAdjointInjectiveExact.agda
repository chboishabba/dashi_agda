module DASHI.Physics.YangMills.BalabanSelectedReducedCombinedAdjointInjectiveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers", RAIRO Analyse Numerique 8 (1974),
-- 129--151. No DOI was assigned to the cited article.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Consume the strict 29/1024 floor on the split combined multiplier
-- presentation and prove kernel triviality of the actual reopened adjoint.
-- This is the precise replacement for the false raw-780 claim.  It says only
--
--     L_A^* s(alpha,gamma) = 0  ==>  alpha = 0 and gamma = 0,
--
-- with gamma constrained to the componentwise-mean-zero section.  It does not
-- claim that ker L_A^* on the unreduced raw carrier equals the three flat
-- constants, and therefore remains compatible with the previously proved
-- background-dependent stabilizer stratification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanFiniteSelectorL2DefinitenessExact as L2Def
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as RawRows
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as GaugeReduced
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedReducedCombinedConstraintFloorExact as Floor

record ReducedMultiplierPointwiseZero
    (selected : Split.SelectedReducedCombinedMultiplier) : Set where
  field
    averageZero : ∀ row → Split.averageMultiplier selected row ≡ 0ℚ
    gaugeZero : ∀ row → Split.gaugeMultiplier selected row ≡ 0ℚ

open ReducedMultiplierPointwiseZero public

------------------------------------------------------------------------
-- Pointwise-zero state vectors have zero finite squared norm.
------------------------------------------------------------------------

stateNormZeroFromPointwiseZero :
  ∀ vector →
  (∀ coordinate → vector coordinate ≡ 0ℚ) →
  Rect.finiteNormSq StateCarrier.physicalStateCarrier vector ≡ 0ℚ
stateNormZeroFromPointwiseZero vector pointwiseZero =
  let
    values = Matrix.coordinates StateCarrier.physicalStateCarrier
  in
  trans
    (Sums.sumRationalCong values
      (λ coordinate → vector coordinate * vector coordinate)
      (λ _ → 0ℚ)
      (λ coordinate →
        trans
          (cong₂ _*_
            (pointwiseZero coordinate) (pointwiseZero coordinate))
          (ℚRing.solve [])))
    (Fubini.sumRationalZero values)

------------------------------------------------------------------------
-- The 29/1024 floor forces the reduced multiplier norm to vanish.
------------------------------------------------------------------------

combinedMultiplierNormNonnegative :
  ∀ selected → 0ℚ ≤ Floor.reducedCombinedMultiplierNormSq selected
combinedMultiplierNormNonnegative selected =
  FiniteL2.addNonnegative
    (Floor.averageMultiplierNormNonnegative selected)
    (Floor.gaugeMultiplierNormNonnegative selected)

reciprocalReducedFloor : ℚ
reciprocalReducedFloor = + 1024 / 29

reciprocalReducedFloorNonnegative : 0ℚ ≤ reciprocalReducedFloor
reciprocalReducedFloorNonnegative =
  toWitness {a? = 0ℚ ≤? reciprocalReducedFloor} _

reducedCombinedNormZeroFromAdjointZero :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  (∀ coordinate →
    Floor.selectedReducedCombinedAdjoint background selected coordinate ≡ 0ℚ) →
  Floor.reducedCombinedMultiplierNormSq selected ≡ 0ℚ
reducedCombinedNormZeroFromAdjointZero
    background radius selected adjointZero =
  let
    outputNormZero = stateNormZeroFromPointwiseZero
      (Floor.selectedReducedCombinedAdjoint background selected) adjointZero

    floorRaw = Floor.selectedBackgroundReducedCombinedAdjointFloor
      background radius selected

    floorToZero :
      Floor.selectedBackgroundReducedCombinedFloor
        * Floor.reducedCombinedMultiplierNormSq selected
      ≤ 0ℚ
    floorToZero =
      subst
        (λ upper →
          Floor.selectedBackgroundReducedCombinedFloor
            * Floor.reducedCombinedMultiplierNormSq selected
          ≤ upper)
        outputNormZero floorRaw

    scaled = Norm.scaleNonnegative reciprocalReducedFloor
      reciprocalReducedFloorNonnegative floorToZero

    leftExact :
      reciprocalReducedFloor
        * (Floor.selectedBackgroundReducedCombinedFloor
            * Floor.reducedCombinedMultiplierNormSq selected)
      ≡ Floor.reducedCombinedMultiplierNormSq selected
    leftExact = ℚRing.solve-∀
      (Floor.reducedCombinedMultiplierNormSq selected)

    rightExact : reciprocalReducedFloor * 0ℚ ≡ 0ℚ
    rightExact = ℚRing.solve []

    normBelowZero : Floor.reducedCombinedMultiplierNormSq selected ≤ 0ℚ
    normBelowZero =
      subst
        (λ lower → lower ≤ 0ℚ)
        leftExact
        (subst
          (λ upper →
            reciprocalReducedFloor
              * (Floor.selectedBackgroundReducedCombinedFloor
                  * Floor.reducedCombinedMultiplierNormSq selected)
            ≤ upper)
          rightExact scaled)
  in
  ℚP.≤-antisym normBelowZero
    (combinedMultiplierNormNonnegative selected)

averageNormZeroFromCombinedZero :
  ∀ selected →
  Floor.reducedCombinedMultiplierNormSq selected ≡ 0ℚ →
  Floor.averageMultiplierNormSq selected ≡ 0ℚ
averageNormZeroFromCombinedZero selected combinedZero =
  let
    average = Floor.averageMultiplierNormSq selected
    rawAverageBelowCombined :
      average + 0ℚ ≤ Floor.reducedCombinedMultiplierNormSq selected
    rawAverageBelowCombined =
      ℚP.+-monoʳ-≤ average
        (Floor.gaugeMultiplierNormNonnegative selected)

    averageBelowCombined :
      average ≤ Floor.reducedCombinedMultiplierNormSq selected
    averageBelowCombined =
      subst
        (λ lower → lower ≤ Floor.reducedCombinedMultiplierNormSq selected)
        (ℚP.+-identityʳ average)
        rawAverageBelowCombined

    averageBelowZero : Floor.averageMultiplierNormSq selected ≤ 0ℚ
    averageBelowZero = subst
      (λ upper → Floor.averageMultiplierNormSq selected ≤ upper)
      combinedZero averageBelowCombined
  in
  ℚP.≤-antisym averageBelowZero
    (Floor.averageMultiplierNormNonnegative selected)

gaugeNormZeroFromCombinedZero :
  ∀ selected →
  Floor.reducedCombinedMultiplierNormSq selected ≡ 0ℚ →
  Floor.gaugeMultiplierNormSq selected ≡ 0ℚ
gaugeNormZeroFromCombinedZero selected combinedZero =
  let
    gaugeBelowZero : Floor.gaugeMultiplierNormSq selected ≤ 0ℚ
    gaugeBelowZero = subst
      (λ upper → Floor.gaugeMultiplierNormSq selected ≤ upper)
      combinedZero (Floor.gaugeNormBelowCombinedNorm selected)
  in
  ℚP.≤-antisym gaugeBelowZero
    (Floor.gaugeMultiplierNormNonnegative selected)

------------------------------------------------------------------------
-- Definiteness on the two finite row selectors.
------------------------------------------------------------------------

averageNormZeroPointwise :
  ∀ selected →
  Floor.averageMultiplierNormSq selected ≡ 0ℚ →
  ∀ row → Split.averageMultiplier selected row ≡ 0ℚ
averageNormZeroPointwise selected normZero =
  L2Def.finiteSelectorNormZeroPointwise
    AverageRows.selectedBlockAverageRowFiniteSelector
    (Split.averageMultiplier selected)
    normZero

gaugeNormZeroPointwise :
  ∀ selected →
  Floor.gaugeMultiplierNormSq selected ≡ 0ℚ →
  ∀ row → Split.gaugeMultiplier selected row ≡ 0ℚ
gaugeNormZeroPointwise selected normZero =
  let
    gauge = Split.gaugeMultiplier selected

    rawGaugeNormZero :
      Defect.gaugeMultiplierRowNormSq gauge ≡ 0ℚ
    rawGaugeNormZero =
      trans (GaugeReduced.gaugeMultiplierRowNormSqExact gauge) normZero
  in
  L2Def.finiteSelectorNormZeroPointwise
    RawRows.selectedGaugeRowFiniteSelector gauge rawGaugeNormZero

------------------------------------------------------------------------
-- The reduced combined adjoint has trivial kernel on the chosen section.
------------------------------------------------------------------------

selectedReducedCombinedAdjointInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  (∀ coordinate →
    Floor.selectedReducedCombinedAdjoint background selected coordinate ≡ 0ℚ) →
  ReducedMultiplierPointwiseZero selected
selectedReducedCombinedAdjointInjective
    background radius selected adjointZero =
  let
    combinedZero = reducedCombinedNormZeroFromAdjointZero
      background radius selected adjointZero
    averageNormZero = averageNormZeroFromCombinedZero selected combinedZero
    gaugeNormZero = gaugeNormZeroFromCombinedZero selected combinedZero
  in
  record
    { averageZero = averageNormZeroPointwise selected averageNormZero
    ; gaugeZero = gaugeNormZeroPointwise selected gaugeNormZero
    }

selectedReducedCombinedAdjointKernelTrivialLevel : ProofLevel
selectedReducedCombinedAdjointKernelTrivialLevel = machineChecked
