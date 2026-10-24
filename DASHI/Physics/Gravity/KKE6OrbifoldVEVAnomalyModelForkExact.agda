module DASHI.Physics.Gravity.KKE6OrbifoldVEVAnomalyModelForkExact where

------------------------------------------------------------------------
-- 2026-10-24 CONSTRUCTIVE source-specific orbifold gate.
-- SOURCE PRIOR: unmerged E6 #1106 (first-Tits 27, E32/E33 Higgs).
-- Original SU3^3 and E6 branching: Slansky 1981.
-- Original S1/Z2 local anomaly: Arkani-Hamed/Cohen/Georgi 2001;
-- Scrucca/Serone/Silvestrini/Zwirner 2002.
--
-- Explicit parity P_L=P_R=diag(-1,-1,+1) in SU3L/SU3R,
-- P_c=1. Two SOURCE bifundamentals: intrinsic Phi parity ODD,
-- intrinsic Chi parity EVEN. E32 and E33 survive respectively.
-- Their source V6 uses only terms even under individual Phi/Chi
-- signs, so this assignment is compatible with THAT POTENTIAL.
-- Full 27 fermion zero-mode labels from the executable:
--   A=(3,bar3,1) 6L/3R, B=(bar3,1,3) 6L/3R,
--   C=(1,3,bar3) 4L/5R = 16L/11R.
-- Physical tests: IR SM-subgroup anomalies vanish, but UV pre-VEV
-- orbifold U1L/R and mixed anomalies do NOT. The gated physics is
-- SU3c x SU3L x SU3R, not FULL GAUGED E6: full E6 would have
-- 30 additional orbifold-even mixed adjoint generators.
--
-- FINITE parity/action non-descent here, NOT a kernel-verified
-- continuum orbifold spectrum, anomaly, or quantum field theory.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_+_; _*_)
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

data SUThreeIndex : Set where
  first second third : SUThreeIndex

data ZTwoParity : Set where
  even odd : ZTwoParity

_⊗_ : ZTwoParity → ZTwoParity → ZTwoParity
even ⊗ even = even
even ⊗ odd = odd
odd ⊗ even = odd
odd ⊗ odd = even

fundamentalParity : SUThreeIndex → ZTwoParity
fundamentalParity first = odd
fundamentalParity second = odd
fundamentalParity third = even

bifundamentalParity : SUThreeIndex → SUThreeIndex → ZTwoParity
bifundamentalParity row column =
  fundamentalParity row ⊗ fundamentalParity column

phiIntrinsicParity : ZTwoParity
phiIntrinsicParity = odd

chiIntrinsicParity : ZTwoParity
chiIntrinsicParity = even

phiE32EvenZeroMode :
  phiIntrinsicParity ⊗ bifundamentalParity third second ≡ even
phiE32EvenZeroMode = refl

chiE33EvenZeroMode :
  chiIntrinsicParity ⊗ bifundamentalParity third third ≡ even
chiE33EvenZeroMode = refl

-- The two bifundamentals each have 9 complex =18 real components;
-- source #1106 comparison has 36 real, NOT two full complex 27s.
twoBifundamentalRealComponents : 2 * (2 * 9) ≡ 36
twoBifundamentalRealComponents = refl

threeBlockChiralCount : 6 + 6 + 4 ≡ 16
threeBlockChiralCount = refl

threeBlockRightCount : 3 + 3 + 5 ≡ 11
threeBlockRightCount = refl

full27CountStill : 16 + 11 ≡ 27
full27CountStill = refl

-- Orbifold-even SU3L and SU3R gauge algebras have 4 generators
-- each; with colour 8, the parity-invariant trinification gauge
-- algebra has 16. E32/E33 source VEVs leave 4 L/R electroweak
-- generators plus 8 unbroken colour generators.
evenTrinificationGaugeCount : 8 + 4 + 4 ≡ 16
evenTrinificationGaugeCount = refl

sourceElectroweakGaugeKernel : 4 + 4 ≡ 8
sourceElectroweakGaugeKernel = refl

-- Under inner parity in FULL E6, the adjoint (3,3,3) and
-- conjugate each have 15 even and 12 odd, ADDITIONAL to 8+4+4.
fullE6MixedEvenGaugeModes : 2 * 3 * (2 * 2 + 1) ≡ 30
fullE6MixedEvenGaugeModes = refl

fullE6TotalEvenGaugeModes : 16 + 30 ≡ 46
fullE6TotalEvenGaugeModes = refl

data GaugeSourceChoice : Set where
  gaugedTrinification
  gaugedFullE6 : GaugeSourceChoice

selectedEvenGaugeCount : GaugeSourceChoice → Nat
selectedEvenGaugeCount gaugedTrinification = 16
selectedEvenGaugeCount gaugedFullE6 = 46

data LocalGaugeStage : Set where
  preVEVOrbifoldGauge
  postVEVSMSubgroup : LocalGaugeStage

-- The exact rational source script checks:
-- IR SU3c^3, SU3c^2Y, SU2L^2Y, Y^3, gravitational Y = 0,
-- and even SU2L Witten doublet count. It also finds NONZERO
-- UV U1L/R cubic, mixed, gravitational and non-Abelian anomalies.
-- This finite boolean labels those results; it does NOT prove
-- the underlying quantum anomalies inside Agda.
allTestedPerturbativeGaugeCoefficientsZero :
  LocalGaugeStage → Bool
allTestedPerturbativeGaugeCoefficientsZero preVEVOrbifoldGauge = false
allTestedPerturbativeGaugeCoefficientsZero postVEVSMSubgroup = true

source27DimensionAtEitherStage : LocalGaugeStage → Nat
source27DimensionAtEitherStage _ = 27

falseIsNotTrue : false ≡ true → ⊥
falseIsNotTrue ()

IRAnomalyCancellationDoesNotPayUVOrbifoldGauge :
  Transport.ClaimNonTransportWitness
    source27DimensionAtEitherStage
    allTestedPerturbativeGaugeCoefficientsZero
IRAnomalyCancellationDoesNotPayUVOrbifoldGauge =
  Descent.consumerNonDescentWitness
    preVEVOrbifoldGauge postVEVSMSubgroup
    refl falseIsNotTrue

noUVAnomalyPromotionFromIR27 :
  Transport.ClaimTransport
    source27DimensionAtEitherStage
    allTestedPerturbativeGaugeCoefficientsZero → ⊥
noUVAnomalyPromotionFromIR27 =
  Transport.claimNonTransportWitnessBlocksTransport
    IRAnomalyCancellationDoesNotPayUVOrbifoldGauge

-- An E6 mathematical 27 charge carrier does not identify the
-- ACTUAL gauged Lie algebra or its surviving vector spectrum.
constantSource27 : GaugeSourceChoice → Nat
constantSource27 _ = 27

sixteenNotFortySix : 16 ≡ 46 → ⊥
sixteenNotFortySix ()

sameFirstTitsCarrierNotSamePhysicalGaugeSource :
  Transport.ClaimNonTransportWitness
    constantSource27 selectedEvenGaugeCount
sameFirstTitsCarrierNotSamePhysicalGaugeSource =
  Descent.consumerNonDescentWitness
    gaugedTrinification gaugedFullE6
    refl sixteenNotFortySix

-- Source status. Fixed-point anomaly/CS, the actual full spin-gauge
-- action, a unique photon after EW symmetry breaking, an E6-complete
-- Higgs/fermion scalar potential, and NEW orbifold Casimir all OPEN.


------------------------------------------------------------------------
-- COMPLETE selected diagonal SU3R parity family: I or 2 negative
-- signs, while P_c=I and P_L=(-,-,+) keep colour and SU2L.
-- Source executable exhaustively computes actual anomaly sums:
--   I: colour cubic +4, UV Abelian cubic 0;
--   every nontrivial SU3R involution: colour cubic 0,
--                                    U1L^3=+40,U1R^3=-40.
-- The physical ANOMALY calculation is in Python; this is the exact
-- finite consumer-indexed NO-SIMULTANEOUS-PASS theorem, not a
-- kernel proof of continuum triangle diagrams.
------------------------------------------------------------------------

data RightDiagonalInvolution : Set where
  rightIdentity
  rightMinusMinusPlus
  rightMinusPlusMinus
  rightPlusMinusMinus : RightDiagonalInvolution

colourCubicSourcePass : RightDiagonalInvolution → Bool
colourCubicSourcePass rightIdentity = false
colourCubicSourcePass rightMinusMinusPlus = true
colourCubicSourcePass rightMinusPlusMinus = true
colourCubicSourcePass rightPlusMinusMinus = true

uvAbelianCubicSourcePass : RightDiagonalInvolution → Bool
uvAbelianCubicSourcePass rightIdentity = true
uvAbelianCubicSourcePass rightMinusMinusPlus = false
uvAbelianCubicSourcePass rightMinusPlusMinus = false
uvAbelianCubicSourcePass rightPlusMinusMinus = false

noDiagonalRightInvolutionPassesBothUVConsumers :
  (r : RightDiagonalInvolution) →
  colourCubicSourcePass r ≡ true →
  uvAbelianCubicSourcePass r ≡ true → ⊥
noDiagonalRightInvolutionPassesBothUVConsumers rightIdentity c u =
  falseIsNotTrue c
noDiagonalRightInvolutionPassesBothUVConsumers rightMinusMinusPlus c u =
  falseIsNotTrue u
noDiagonalRightInvolutionPassesBothUVConsumers rightMinusPlusMinus c u =
  falseIsNotTrue u
noDiagonalRightInvolutionPassesBothUVConsumers rightPlusMinusMinus c u =
  falseIsNotTrue u

-- A 5D Dirac scalar bilinear is ODD under gamma5 orbifold spinor
-- reflection. The earlier smooth-circle CONSTANT Dirac mass cannot
-- be imported: new odd mass profile or boundary/multiplet dynamics
-- needs its own physical source. Source is the gamma-matrix test
-- check_kk_orbifold_bulk_mass_parity.py, not a Clifford proof here.
data OrbifoldBulkDiracMassSource : Set where
  oldEvenConstantBulkMass
  newlySourcedOddKinkMass : OrbifoldBulkDiracMassSource

orbifoldReflectionAdmissibleMass :
  OrbifoldBulkDiracMassSource → Bool
orbifoldReflectionAdmissibleMass oldEvenConstantBulkMass = false
orbifoldReflectionAdmissibleMass newlySourcedOddKinkMass = true

-- "admissible mass parity" is only one necessary condition;
-- no quantum-consistent kink/brane mass operator is asserted.
