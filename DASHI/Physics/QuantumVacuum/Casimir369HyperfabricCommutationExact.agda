module DASHI.Physics.QuantumVacuum.Casimir369HyperfabricCommutationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Foundations.RecursiveRadixHypervoxel as HyperBase
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as Hyper
import DASHI.Physics.QuantumVacuum.ZeroPointModeHyperfabricExact as ZPE
import DASHI.Physics.QuantumVacuum.CasimirModeHyperfabricBridgeExact as ModeFabric
import DASHI.Physics.QuantumVacuum.ParallelPlatePhysicalModeClassExact as Class
import DASHI.Physics.QuantumVacuum.ParallelPlatePhysicalModeCompletenessExact as Physical
import DASHI.Physics.QuantumVacuum.CasimirBidiEndgameRouterV8Exact as Endgame
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720
import DASHI.Physics.QuantumVacuum.CasimirCoefficient720To240CompilerExact as C240

------------------------------------------------------------------------
-- CASIMIR x 369 / SO(3)-STYLE HYPERFABRIC MAX-CUT
--
-- This module closes the finite structural cross-pollination that was already
-- latent in the repository without identifying a coefficient coincidence with
-- a physical derivation.
--
-- Existing literal Casimir objects already provide:
--
--   * same-field / different-boundary vacuum mode hyperfabrics;
--   * a same-observable weld to the parallel-plate Casimir kernel;
--   * canonical physical mode classes TEM | TE+ n | TM+ n;
--   * a V8 same-spectrum spine joining those Maxwell modes to transverse and
--     longitudinal Casimir analysis;
--   * 720 = 6 * 120 and the same-object derivative route 720 -> 240.
--
-- Existing 369 closure machinery provides:
--
--   3 axes
--   6 axis x lift-polarity points
--   9 operator-sheet slots = axis x axis
--   18 lifted operator-sheet points = axis x axis x polarity.
--
-- The exact arithmetic alignment is therefore
--
--   720 = 3*240 = 6*120 = 9*80 = 18*40
--   240 = 3*80  = 6*40.
--
-- Crucially, the derivative factor three aligns at fixed residual with the
-- contractions 9 -> 3 and 18 -> 6, NOT with a naive 6 -> 3 contraction at
-- fixed 120.  The latter would give 3*120 = 360, not 240.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Canonical parallel-plate physical mode family <-> three-axis chart.
--
-- Longitudinal index is retained separately so the three-axis observation is
-- reopenable rather than silently identifying all TE_n or TM_n modes.
------------------------------------------------------------------------

data ModeFamily : Set where
  temFamily : ModeFamily
  teFamily  : ModeFamily
  tmFamily  : ModeFamily

modeFamily : Class.PlateModeClass → ModeFamily
modeFamily Class.TEM = temFamily
modeFamily (Class.TE+ n) = teFamily
modeFamily (Class.TM+ n) = tmFamily

familyAxis : ModeFamily → Hyper.SU2Axis
familyAxis temFamily = Hyper.axis₁
familyAxis teFamily  = Hyper.axis₂
familyAxis tmFamily  = Hyper.axis₃

axisFamily : Hyper.SU2Axis → ModeFamily
axisFamily HyperBase.axis-low  = temFamily
axisFamily HyperBase.axis-mid  = teFamily
axisFamily HyperBase.axis-high = tmFamily

familyAxisRoundTrip : ∀ family → axisFamily (familyAxis family) ≡ family
familyAxisRoundTrip temFamily = refl
familyAxisRoundTrip teFamily = refl
familyAxisRoundTrip tmFamily = refl

axisFamilyRoundTrip : ∀ axis → familyAxis (axisFamily axis) ≡ axis
axisFamilyRoundTrip HyperBase.axis-low = refl
axisFamilyRoundTrip HyperBase.axis-mid = refl
axisFamilyRoundTrip HyperBase.axis-high = refl

modeClassAxis : Class.PlateModeClass → Hyper.SU2Axis
modeClassAxis c = familyAxis (modeFamily c)

data LongitudinalResidual : ModeFamily → Set where
  temZero : LongitudinalResidual temFamily
  teIndex : Nat → LongitudinalResidual teFamily
  tmIndex : Nat → LongitudinalResidual tmFamily

ModeClassCode : Set
ModeClassCode = Σ ModeFamily LongitudinalResidual

encodeModeClass : Class.PlateModeClass → ModeClassCode
encodeModeClass Class.TEM = temFamily , temZero
encodeModeClass (Class.TE+ n) = teFamily , teIndex n
encodeModeClass (Class.TM+ n) = tmFamily , tmIndex n

decodeModeClass : ModeClassCode → Class.PlateModeClass
decodeModeClass (temFamily , temZero) = Class.TEM
decodeModeClass (teFamily , teIndex n) = Class.TE+ n
decodeModeClass (tmFamily , tmIndex n) = Class.TM+ n

decodeEncodeModeClass :
  ∀ c → decodeModeClass (encodeModeClass c) ≡ c
decodeEncodeModeClass Class.TEM = refl
decodeEncodeModeClass (Class.TE+ n) = refl
decodeEncodeModeClass (Class.TM+ n) = refl

encodeDecodeModeClass :
  ∀ code → encodeModeClass (decodeModeClass code) ≡ code
encodeDecodeModeClass (temFamily , temZero) = refl
encodeDecodeModeClass (teFamily , teIndex n) = refl
encodeDecodeModeClass (tmFamily , tmIndex n) = refl

codeLongitudinalIndex : ModeClassCode → Nat
codeLongitudinalIndex (temFamily , temZero) = zero
codeLongitudinalIndex (teFamily , teIndex n) = suc n
codeLongitudinalIndex (tmFamily , tmIndex n) = suc n

modeClassCodePreservesLongitudinalIndex :
  ∀ c →
  codeLongitudinalIndex (encodeModeClass c) ≡ Class.longitudinalIndex c
modeClassCodePreservesLongitudinalIndex Class.TEM = refl
modeClassCodePreservesLongitudinalIndex (Class.TE+ n) = refl
modeClassCodePreservesLongitudinalIndex (Class.TM+ n) = refl

------------------------------------------------------------------------
-- 2. Structural six-lift adapter.
--
-- The polarity here is exactly the already-owned finite lift coordinate from
-- SU2SO3369HypervoxelBridge.  This section does NOT claim that the polarity is
-- automatically a Maxwell travelling-wave, helicity, plate-normal direction,
-- spin, or any other physical two-state observable.
------------------------------------------------------------------------

ModeFamilyLift : Set
ModeFamilyLift = ModeFamily × Hyper.LiftPolarity

modeFamilyLiftToAxisLift : ModeFamilyLift → Hyper.AxisLift
modeFamilyLiftToAxisLift (family , polarity) = familyAxis family , polarity

axisLiftToModeFamilyLift : Hyper.AxisLift → ModeFamilyLift
axisLiftToModeFamilyLift (axis , polarity) = axisFamily axis , polarity

modeFamilyLiftAxisRoundTrip :
  ∀ lifted → axisLiftToModeFamilyLift (modeFamilyLiftToAxisLift lifted) ≡ lifted
modeFamilyLiftAxisRoundTrip (temFamily , polarity) = refl
modeFamilyLiftAxisRoundTrip (teFamily , polarity) = refl
modeFamilyLiftAxisRoundTrip (tmFamily , polarity) = refl

axisLiftModeFamilyRoundTrip :
  ∀ lifted → modeFamilyLiftToAxisLift (axisLiftToModeFamilyLift lifted) ≡ lifted
axisLiftModeFamilyRoundTrip (HyperBase.axis-low , polarity) = refl
axisLiftModeFamilyRoundTrip (HyperBase.axis-mid , polarity) = refl
axisLiftModeFamilyRoundTrip (HyperBase.axis-high , polarity) = refl

------------------------------------------------------------------------
-- 3. Literal operator-sheet contractions already present in the hyperfabric.
--
-- MatrixSlot = output-axis x input-axis.  Forgetting one axis has a concrete
-- three-point fibre.  Its lifted sibling retains the existing polarity.
------------------------------------------------------------------------

contractOperatorSlot : Hyper.MatrixSlot → Hyper.SU2Axis
contractOperatorSlot = proj₁

operatorLift₁ operatorLift₂ operatorLift₃ :
  Hyper.SU2Axis → Hyper.MatrixSlot
operatorLift₁ output = output , Hyper.axis₁
operatorLift₂ output = output , Hyper.axis₂
operatorLift₃ output = output , Hyper.axis₃

operatorContractionFibreComplete :
  ∀ slot →
  (slot ≡ operatorLift₁ (contractOperatorSlot slot))
  ⊎
  ((slot ≡ operatorLift₂ (contractOperatorSlot slot))
   ⊎
   (slot ≡ operatorLift₃ (contractOperatorSlot slot)))
operatorContractionFibreComplete (output , HyperBase.axis-low) = inj₁ refl
operatorContractionFibreComplete (output , HyperBase.axis-mid) = inj₂ (inj₁ refl)
operatorContractionFibreComplete (output , HyperBase.axis-high) = inj₂ (inj₂ refl)

LiftedOperatorPoint : Set
LiftedOperatorPoint = Hyper.MatrixSlot × Hyper.LiftPolarity

contractLiftedOperatorPoint : LiftedOperatorPoint → Hyper.AxisLift
contractLiftedOperatorPoint ((output , input) , polarity) = output , polarity

liftedOperatorLift₁ liftedOperatorLift₂ liftedOperatorLift₃ :
  Hyper.AxisLift → LiftedOperatorPoint
liftedOperatorLift₁ (output , polarity) = (output , Hyper.axis₁) , polarity
liftedOperatorLift₂ (output , polarity) = (output , Hyper.axis₂) , polarity
liftedOperatorLift₃ (output , polarity) = (output , Hyper.axis₃) , polarity

liftedOperatorContractionFibreComplete :
  ∀ point →
  (point ≡ liftedOperatorLift₁ (contractLiftedOperatorPoint point))
  ⊎
  ((point ≡ liftedOperatorLift₂ (contractLiftedOperatorPoint point))
   ⊎
   (point ≡ liftedOperatorLift₃ (contractLiftedOperatorPoint point)))
liftedOperatorContractionFibreComplete ((output , HyperBase.axis-low) , polarity) = inj₁ refl
liftedOperatorContractionFibreComplete ((output , HyperBase.axis-mid) , polarity) = inj₂ (inj₁ refl)
liftedOperatorContractionFibreComplete ((output , HyperBase.axis-high) , polarity) = inj₂ (inj₂ refl)

operatorSheetIsThreeAxisFibres :
  Hyper.operatorSheetCount ≡ 3 * Hyper.axisCarrierCount
operatorSheetIsThreeAxisFibres = refl

liftedOperatorSheetIsThreeAxisLiftFibres :
  Hyper.liftedOperatorSheetCount ≡ 3 * Hyper.axisLiftCarrierCount
liftedOperatorSheetIsThreeAxisLiftFibres = refl

------------------------------------------------------------------------
-- 4. Exact Casimir coefficient lattice against the existing hyperfabric counts.
------------------------------------------------------------------------

axisCarrierCountIs3 : Hyper.axisCarrierCount ≡ 3
axisCarrierCountIs3 = refl

axisCountTimes240Is720 :
  Hyper.axisCarrierCount * 240 ≡ 720
axisCountTimes240Is720 = refl

axisLiftCountTimes120Is720 :
  Hyper.axisLiftCarrierCount * 120 ≡ 720
axisLiftCountTimes120Is720 = refl

operatorSheetTimes80Is720 :
  Hyper.operatorSheetCount * 80 ≡ 720
operatorSheetTimes80Is720 = refl

liftedOperatorSheetTimes40Is720 :
  Hyper.liftedOperatorSheetCount * 40 ≡ 720
liftedOperatorSheetTimes40Is720 = refl

axisCountTimes80Is240 :
  Hyper.axisCarrierCount * 80 ≡ 240
axisCountTimes80Is240 = refl

axisLiftCountTimes40Is240 :
  Hyper.axisLiftCarrierCount * 40 ≡ 240
axisLiftCountTimes40Is240 = refl

threeTimes40Is120 : 3 * 40 ≡ 120
threeTimes40Is120 = refl

twoTimes40Is80 : 2 * 40 ≡ 80
twoTimes40Is80 = refl

casimirTransverseSixArithmetic : 6 * 120 ≡ 720
casimirTransverseSixArithmetic = C720.sixTimes120Is720

casimirDerivativeThreeArithmetic : 3 * 240 ≡ 720
casimirDerivativeThreeArithmetic = C240.threeTimes240Is720

-- The literal fixed-residual 6 -> 3 reading is refuted by arithmetic.
-- 3 * 120 normalizes to 360, not 240.
naiveSixToThreeFixed120CannotProduce240 :
  Hyper.axisCarrierCount * 120 ≡ 240 → ⊥
naiveSixToThreeFixed120CannotProduce240 ()

record CasimirCoefficientHyperfabricReceipt : Set where
  constructor casimir-coefficient-hyperfabric-receipt
  field
    energyAsThreeTimes240 : Hyper.axisCarrierCount * 240 ≡ 720
    energyAsSixTimes120 : Hyper.axisLiftCarrierCount * 120 ≡ 720
    energyAsNineTimes80 : Hyper.operatorSheetCount * 80 ≡ 720
    energyAsEighteenTimes40 : Hyper.liftedOperatorSheetCount * 40 ≡ 720

    pressureAsThreeTimes80 : Hyper.axisCarrierCount * 80 ≡ 240
    pressureAsSixTimes40 : Hyper.axisLiftCarrierCount * 40 ≡ 240

    derivativeFactorThree : 3 * 240 ≡ 720
    transverseSixFactor : 6 * 120 ≡ 720

open CasimirCoefficientHyperfabricReceipt public

canonicalCasimirCoefficientHyperfabricReceipt :
  CasimirCoefficientHyperfabricReceipt
canonicalCasimirCoefficientHyperfabricReceipt =
  casimir-coefficient-hyperfabric-receipt
    axisCountTimes240Is720
    axisLiftCountTimes120Is720
    operatorSheetTimes80Is720
    liftedOperatorSheetTimes40Is720
    axisCountTimes80Is240
    axisLiftCountTimes40Is240
    casimirDerivativeThreeArithmetic
    casimirTransverseSixArithmetic

------------------------------------------------------------------------
-- 5. Same-object entry from the canonical Casimir V8 physical spectrum.
--
-- This is not a free-floating cardinality map: the input mode is literally a
-- PhysicalMode of the Maxwell skeleton carried by the canonical Casimir
-- endgame bundle, whose own record retains same-spectrum evidence across the
-- Maxwell/transverse/renormalisation/zeta stages.
------------------------------------------------------------------------

endgameModeAxis :
  ∀ {kernel zetaProblem zetaTrace zeta120} →
  (B : Endgame.CanonicalCasimirEndgameBundle
         kernel zetaProblem zetaTrace zeta120) →
  Physical.PhysicalMode (Endgame.maxwell B) →
  Hyper.SU2Axis
endgameModeAxis B mode =
  modeClassAxis (Physical.modeClass (Endgame.maxwell B) mode)

endgameModeCode :
  ∀ {kernel zetaProblem zetaTrace zeta120} →
  (B : Endgame.CanonicalCasimirEndgameBundle
         kernel zetaProblem zetaTrace zeta120) →
  Physical.PhysicalMode (Endgame.maxwell B) →
  ModeClassCode
endgameModeCode B mode =
  encodeModeClass (Physical.modeClass (Endgame.maxwell B) mode)

endgameModeCodePreservesLongitudinalIndex :
  ∀ {kernel zetaProblem zetaTrace zeta120} →
  (B : Endgame.CanonicalCasimirEndgameBundle
         kernel zetaProblem zetaTrace zeta120) →
  (mode : Physical.PhysicalMode (Endgame.maxwell B)) →
  codeLongitudinalIndex (endgameModeCode B mode)
  ≡
  Class.longitudinalIndex (Physical.modeClass (Endgame.maxwell B) mode)
endgameModeCodePreservesLongitudinalIndex B mode =
  modeClassCodePreservesLongitudinalIndex
    (Physical.modeClass (Endgame.maxwell B) mode)

endgameSameSpectrumReceipt :
  ∀ {kernel zetaProblem zetaTrace zeta120} →
  (B : Endgame.CanonicalCasimirEndgameBundle
         kernel zetaProblem zetaTrace zeta120) →
  Endgame.SamePhysicalSpectrumAcrossMaxwellAndTransverse B
endgameSameSpectrumReceipt B =
  Endgame.samePhysicalSpectrumAcrossMaxwellAndTransverseEvidence B

------------------------------------------------------------------------
-- 6. Full triangle weld: existing mode-hyperfabric observable + canonical
-- physical Maxwell spectrum + 369 contraction semantics.
--
-- The finite/classification and arithmetic sides are already exact.  The final
-- physical statement that boundary differentiation IS the 9->3 / 18->6
-- operator-axis contraction remains an explicit same-object payment.  This is
-- the precise promotion boundary rather than a numerological identification.
------------------------------------------------------------------------

record Casimir369SameObjectContractionWeld
    {S : ZPE.ScalarSpectrum}
    (free cavity : ZPE.FiniteVacuumHyperfabric S)
    {kernel zetaProblem zetaTrace zeta120}
    (endgame : Endgame.CanonicalCasimirEndgameBundle
                 kernel zetaProblem zetaTrace zeta120) : Set₁ where
  field
    modeHyperfabric : ModeFabric.CasimirModeHyperfabricWeld free cavity
    physicalCompleteness :
      Physical.ProofBearingPhysicalModeCompleteness (Endgame.maxwell endgame)

    SameModeCarrierAcrossHyperfabricAndEndgame : Set
    sameModeCarrierAcrossHyperfabricAndEndgame :
      SameModeCarrierAcrossHyperfabricAndEndgame

    SameBoundaryDerivativeAndOperatorContraction : Set
    boundaryDerivativeIsOperatorAxisContraction :
      SameBoundaryDerivativeAndOperatorContraction
    boundaryDerivativeIsLiftedOperatorAxisContraction :
      SameBoundaryDerivativeAndOperatorContraction

    reading : String

open Casimir369SameObjectContractionWeld public

------------------------------------------------------------------------
-- 7. Authority firewalls.
------------------------------------------------------------------------

data IntegerFactorMatchAutomaticallyIsPhysicalMechanism : Set where
data ThreeAxisChartAutomaticallyIsSO3Representation : Set where
data FiniteLiftPolarityAutomaticallyIsMaxwellPolarisation : Set where
data OperatorContractionAutomaticallyIsBoundaryDerivative : Set where

data SixToThreeFixed120ProducesCasimirPressure : Set where

integerMatchDoesNotCreateMechanism :
  IntegerFactorMatchAutomaticallyIsPhysicalMechanism → ⊥
integerMatchDoesNotCreateMechanism ()

threeAxisChartDoesNotCreateSO3Representation :
  ThreeAxisChartAutomaticallyIsSO3Representation → ⊥
threeAxisChartDoesNotCreateSO3Representation ()

finiteLiftDoesNotCreateMaxwellPolarisation :
  FiniteLiftPolarityAutomaticallyIsMaxwellPolarisation → ⊥
finiteLiftDoesNotCreateMaxwellPolarisation ()

operatorContractionNeedsSameObjectWeld :
  OperatorContractionAutomaticallyIsBoundaryDerivative → ⊥
operatorContractionNeedsSameObjectWeld ()

sixToThreeFixed120IsNotTheCasimirDerivative :
  SixToThreeFixed120ProducesCasimirPressure → ⊥
sixToThreeFixed120IsNotTheCasimirDerivative ()

record Casimir369HyperfabricBoundary : Set where
  constructor casimir-369-hyperfabric-boundary
  field
    physicalModeFamilyThreeAxisCodecOwned : Bool
    longitudinalResidualReopeningOwned : Bool
    operatorNineToThreeContractionOwned : Bool
    liftedOperatorEighteenToSixContractionOwned : Bool
    coefficient720ThreeSixNineEighteenLatticeOwned : Bool
    coefficient240ThreeSixLatticeOwned : Bool
    naiveSixToThreeFixed120Refuted : Bool
    canonicalCasimirEndgameModeEntryOwned : Bool

    coefficientArithmeticIdentifiedAsPhysicalMechanism : Bool
    finiteLiftPolarityIdentifiedAsMaxwellPolarisation : Bool
    operatorContractionIdentifiedAsBoundaryDerivativeWithoutWeld : Bool
    su2OrSo3RepresentationOfCasimirModesClaimed : Bool

open Casimir369HyperfabricBoundary public

canonicalCasimir369HyperfabricBoundary : Casimir369HyperfabricBoundary
canonicalCasimir369HyperfabricBoundary =
  casimir-369-hyperfabric-boundary
    true true true true true true true true
    false false false false
