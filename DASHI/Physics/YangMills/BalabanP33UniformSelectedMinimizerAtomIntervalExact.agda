module DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerAtomIntervalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Ramon E. Moore, R. Baker Kearfott, Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- Make the G2 selected-ball estimate genuinely UNIFORM rather than accepting
-- a fresh endpoint inequality at each configuration.
--
-- The caller supplies ONE region-wide family of interval boxes
--
--   raw_S(A)       in [L_raw(S), U_raw(S)],
--   green_ST(A)    in [L_green(S,T), U_green(S,T)]
--
-- valid for every A in the certified selected region, plus ONE lower bound
-- Q_* <= Q(A).  From the shared boxes we compute the single rational endpoint
--
--   U_* = sum_S U_raw(S) - sum_{S,T} L_green(S,T).
--
-- The only target-facing numerical check is then
--
--   U_* <= (55/18874368) Q_*.
--
-- Finite interval monotonicity proves for EVERY A in the region
--
--   R_corr(A) <= U_* <= (55/18874368) Q_*
--             <= (55/18874368) Q(A),
--
-- and therefore the same theorem for the actual selected minimizer.  There is
-- no configuration-indexed `R_corr <= target` or endpoint-to-target premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33CorrelatedAtomIntervalEvaluationExact as Atom

record SharedCorrelatedAtomBoxes : Set where
  field
    rawBox : Cube.Subset4 → Atom.RationalInterval
    greenBox : Cube.Subset4 → Cube.Subset4 → Atom.RationalInterval
open SharedCorrelatedAtomBoxes public

sharedRawUpperSum : SharedCorrelatedAtomBoxes → ℚ
sharedRawUpperSum boxes =
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → Atom.upper (rawBox boxes subset))

sharedGreenLowerAt : SharedCorrelatedAtomBoxes → Cube.Subset4 → ℚ
sharedGreenLowerAt boxes left =
  Sums.sumRational Cube.nonemptySubsets4
    (λ right → Atom.lower (greenBox boxes left right))

sharedGreenLowerSum : SharedCorrelatedAtomBoxes → ℚ
sharedGreenLowerSum boxes =
  Sums.sumRational Cube.nonemptySubsets4 (sharedGreenLowerAt boxes)

sharedResidualUpper : SharedCorrelatedAtomBoxes → ℚ
sharedResidualUpper boxes =
  sharedRawUpperSum boxes - sharedGreenLowerSum boxes

record UniformSelectedMinimizerAtomInterval (Configuration : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    familyAt : Configuration → Ownership.CorrelatedResidualFamily
    chargeAt : Configuration → ℚ

    sharedBoxes : SharedCorrelatedAtomBoxes

    rawSoundUniform : ∀ configuration →
      InCertifiedRegion configuration →
      ∀ subset →
      Atom.LiesIn
        (Ownership.rawLocalizationAtom (familyAt configuration) subset)
        (rawBox sharedBoxes subset)

    greenSoundUniform : ∀ configuration →
      InCertifiedRegion configuration →
      ∀ left right →
      Atom.LiesIn
        (Ownership.multiplierGreenAtom (familyAt configuration) left right)
        (greenBox sharedBoxes left right)

    chargeLower : ℚ
    chargeLowerBound : ∀ configuration →
      InCertifiedRegion configuration →
      chargeLower ≤ chargeAt configuration

    uniformEndpointFitsLowerCharge :
      sharedResidualUpper sharedBoxes
      ≤ Selector.remainingSingletonCoefficient * chargeLower

open UniformSelectedMinimizerAtomInterval public

atomEnvelopeAt :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration)
    configuration →
  InCertifiedRegion dataSet configuration →
  Atom.CorrelatedAtomIntervalEnvelope (familyAt dataSet configuration)
atomEnvelopeAt dataSet configuration inRegion = record
  { Atom.CorrelatedAtomIntervalEnvelope.rawBox =
      rawBox (sharedBoxes dataSet)
  ; Atom.CorrelatedAtomIntervalEnvelope.greenBox =
      greenBox (sharedBoxes dataSet)
  ; Atom.CorrelatedAtomIntervalEnvelope.rawSound =
      rawSoundUniform dataSet configuration inRegion
  ; Atom.CorrelatedAtomIntervalEnvelope.greenSound =
      greenSoundUniform dataSet configuration inRegion
  }

atomEnvelopeUsesSharedResidualUpper :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Atom.atomIntervalResidualUpper
    (atomEnvelopeAt dataSet configuration inRegion)
  ≡ sharedResidualUpper (sharedBoxes dataSet)
atomEnvelopeUsesSharedResidualUpper dataSet configuration inRegion = refl

remainingSingletonCoefficientNonnegative :
  0ℚ ≤ Selector.remainingSingletonCoefficient
remainingSingletonCoefficientNonnegative =
  ℚP.nonNegative⁻¹ Selector.remainingSingletonCoefficient

uniformRegionResidualBelowSharedEndpoint :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration)
    configuration →
  (inRegion : InCertifiedRegion dataSet configuration) →
  Ownership.correlatedResidualTotal (familyAt dataSet configuration)
  ≤ sharedResidualUpper (sharedBoxes dataSet)
uniformRegionResidualBelowSharedEndpoint dataSet configuration inRegion =
  let
    bounded = Atom.correlatedResidualBelowAtomIntervalUpper
      (atomEnvelopeAt dataSet configuration inRegion)
  in
  Relation.Binary.PropositionalEquality.subst
    (λ upper →
      Ownership.correlatedResidualTotal (familyAt dataSet configuration)
      ≤ upper)
    (atomEnvelopeUsesSharedResidualUpper dataSet configuration inRegion)
    bounded
  where
  open import Relation.Binary.PropositionalEquality

uniformLowerChargeBelowActualTarget :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration)
    configuration →
  (inRegion : InCertifiedRegion dataSet configuration) →
  Selector.remainingSingletonCoefficient * chargeLower dataSet
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
uniformLowerChargeBelowActualTarget dataSet configuration inRegion =
  Norm.scaleNonnegative
    Selector.remainingSingletonCoefficient
    remainingSingletonCoefficientNonnegative
    (chargeLowerBound dataSet configuration inRegion)

uniformRegionResidualClosesFromSharedAtomEndpoint :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration)
    configuration →
  (inRegion : InCertifiedRegion dataSet configuration) →
  Ownership.correlatedResidualTotal (familyAt dataSet configuration)
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
uniformRegionResidualClosesFromSharedAtomEndpoint dataSet configuration inRegion =
  ℚP.≤-trans
    (uniformRegionResidualBelowSharedEndpoint dataSet configuration inRegion)
    (ℚP.≤-trans
      (uniformEndpointFitsLowerCharge dataSet)
      (uniformLowerChargeBelowActualTarget dataSet configuration inRegion))

selectedMinimizerCorrelatedResidualClosesFromAtomIntervals :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration) →
  Ownership.correlatedResidualTotal
    (familyAt dataSet (selectedMinimizer dataSet))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerCorrelatedResidualClosesFromAtomIntervals dataSet =
  uniformRegionResidualClosesFromSharedAtomEndpoint
    dataSet
    (selectedMinimizer dataSet)
    (selectedMinimizerInRegion dataSet)

p33UniformSelectedMinimizerAtomIntervalTransportLevel : ProofLevel
p33UniformSelectedMinimizerAtomIntervalTransportLevel = machineChecked

-- The remaining G2 computation is now exactly:
--   (1) one interval enclosure for every raw/Green atom over the WHOLE selected
--       region,
--   (2) one uniform charge floor, and
--   (3) one rational comparison of the computed shared endpoint with
--       (55/18874368) times that floor.
-- No configuration-indexed target inequality survives this route.
p33PhysicalSelectedMinimizerAtomIntervalEvaluationLevel : ProofLevel
p33PhysicalSelectedMinimizerAtomIntervalEvaluationLevel = conditional
