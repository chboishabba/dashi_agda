module DASHI.Analysis.RHHyperfabricNSDyadicSelectedConsumerNonDescentExact where

-- Source-specific sufficient-consumer / sign-loss weld.
-- Original selected periodic integer modes: NSIntegerFourierLattice.
-- Original sign chart: NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact.
-- Original sign quotient section and triad->T9: Round530Exact.
-- Original factorization criterion: Core.ConsumerDescentMinimalObserverExact
-- and Core.ConsumerFibreRepairExact. Original dyadic max norm hat is
-- scripts/ns_radius8_multiplier_scaling.py, selected K=3 here.
--
-- Exact selected integer radii 8/9: h_3(8)=1 and h_3(9)=7/8.
-- Natural numerators in eighths are 8 and 7, not a new analytic estimate.
-- The binary support projection loses still more than the signed chart.
-- The proof is a SAME-SOURCE TWO-MODE counterexample to global descent;
-- it is NOT the full NS nonlinear Fourier or the Clay regularity proof.
-- Agda kernel not run.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Integer.Base using (+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact as Sign
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact as Triad
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.SSPTritCarrier as SSP

data SelectedSourceMode : Set where
  radiusEightSource radiusNineSource : SelectedSourceMode

sourceIntegerMode : SelectedSourceMode → Z3.FourierMode
sourceIntegerMode radiusEightSource = Z3.mode (+ 8) (+ 0) (+ 0)
sourceIntegerMode radiusNineSource = Z3.mode (+ 9) (+ 0) (+ 0)

signedMode : SelectedSourceMode → Geometry.Ternary27Point
signedMode m = Sign.observePeriodicMode529 (sourceIntegerMode m)

signedModesSame :
  signedMode radiusEightSource ≡ signedMode radiusNineSource
signedModesSame = refl

originalModeSignIsPositive :
  signedMode radiusEightSource ≡
    Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
originalModeSignIsPositive = refl

-- Original finite max-norm hat K=3 gives h_3(8)=8/8 and h_3(9)=7/8.
-- This function is the exact selected OUTPUT IN EIGHTHS of that producer.
selectedHatEighths : SelectedSourceMode → Nat
selectedHatEighths radiusEightSource = 8
selectedHatEighths radiusNineSource = 7

hatOutputsDiffer :
  selectedHatEighths radiusEightSource ≡
  selectedHatEighths radiusNineSource → ⊥
hatOutputsDiffer ()

selectedDyadicNonDescent :
  Consumer.ConsumerNonDescentWitness signedMode selectedHatEighths
selectedDyadicNonDescent =
  Consumer.consumerNonDescentWitness
    radiusEightSource radiusNineSource
    signedModesSame hatOutputsDiffer

noSignedChartAloneRecoversMultiplier :
  Consumer.ConsumerSufficient signedMode selectedHatEighths → ⊥
noSignedChartAloneRecoversMultiplier =
  Consumer.nonDescentWitnessBlocksSufficiency selectedDyadicNonDescent

noSignedChartFactorization :
  Consumer.FactorsThrough signedMode selectedHatEighths → ⊥
noSignedChartFactorization =
  Consumer.nonDescentWitnessBlocksFactorization selectedDyadicNonDescent

-- Explicit *selected-consumer* repair, NOT entire Fourier convolution.
repairObservation : SelectedSourceMode →
  Geometry.Ternary27Point × Nat
repairObservation mode = signedMode mode , selectedHatEighths mode

repairIsConsumerSufficient :
  Consumer.ConsumerSufficient repairObservation selectedHatEighths
repairIsConsumerSufficient left right same = cong proj₂ same

-- Reuse existing necessary-repair theorem: any honest repair that
-- makes the dyadic output sufficient must separate 8 from 9.
repairMustSeparateSourceModes :
  (refine : SelectedSourceMode → Nat) →
  Repair.RefinementRepairs signedMode refine selectedHatEighths →
  refine radiusEightSource ≡ refine radiusNineSource → ⊥
repairMustSeparateSourceModes refine good same =
  Repair.refinementRepairSeparatesWitness
    selectedDyadicNonDescent good same

-- The original Round530 section only reconstructs the SIGN observed
-- in Round529, not the original Z^3 frequency magnitude.
selectedRound530SectionIsOnlyObservation :
  (mode : SelectedSourceMode) →
  Sign.observePeriodicMode529
    (Triad.periodicModeRepresentative530 (signedMode mode))
  ≡ signedMode mode
selectedRound530SectionIsOnlyObservation mode =
  Triad.periodicSignObservationSection530 (signedMode mode)

-- NEW positive consumer: original exact P3^3 walk at time pi has
-- the SAME source operator as the periodic C3^3 walk, whose Fourier
-- character at q has phase (-1)^(number of nonzero coordinates).
-- This SPECIAL time eigenphase factors through the R529 sign chart.
-- It does not make the R=8 NS dyadic multiplier or convolution factor.

xorBit : Bool → Bool → Bool
xorBit false b = b
xorBit true true = false
xorBit true false = true

occupied : SSP.SSPTrit → Bool
occupied SSP.sspNegOne = true
occupied SSP.sspZero = false
occupied SSP.sspPosOne = true

oddSupport : Geometry.Ternary27Point → Bool
oddSupport (Geometry.ternary27Point x y z) =
  xorBit (occupied x) (xorBit (occupied y) (occupied z))

stroboscopicPeriodicEigenphase : Z3.FourierMode → Bool
stroboscopicPeriodicEigenphase mode =
  oddSupport (Sign.observePeriodicMode529 mode)

stroboscopicPhaseFactorsThroughSign :
  Consumer.FactorsThrough
    Sign.observePeriodicMode529 stroboscopicPeriodicEigenphase
stroboscopicPhaseFactorsThroughSign =
  Factorized.factorizedRefinement oddSupport (λ mode → refl)

stroboscopicPhaseConsumerSufficient :
  Consumer.ConsumerSufficient
    Sign.observePeriodicMode529 stroboscopicPeriodicEigenphase
stroboscopicPhaseConsumerSufficient =
  Consumer.fibreConstantIsConsumerSufficient
    (Consumer.factorsThroughImpliesFibreConstant
      stroboscopicPhaseFactorsThroughSign)

-- Mathematical source verification of the spectral interpretation:
-- check_hyperfabric_original_stroboscopic_P3_C3_RH_YM_NS_20261123.py
-- Agda does not infer the physical exponential's spectral theorem from
-- this definition alone. That source correspondence is exact matrix math
-- independently checked in the original-source regression.

-- This finite receipt preserves positive/negative/zero; it does not
-- identify the sign trit with a natural binary truth value.
-- OPEN: physical Fourier dynamic kernel and convolution, R406,
-- NS continuum measure, RH FarExact, original YM/Haar/Wilson equality.
