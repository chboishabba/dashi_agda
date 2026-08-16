module DASHI.Moonshine.OggRepresentationFrickeCouplingRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as Cyclic
import DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact as AllPrime
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact as Coupling
import DASHI.Moonshine.PrimeRepresentationFrickeOrbitSaturationExact as Saturation
import DASHI.Moonshine.PrimeRepresentationSupersingularOrbitCouplingExact as Supersingular

------------------------------------------------------------------------
-- Cyclic elliptic stabilisers sit inside, but are not equal to, S3.
------------------------------------------------------------------------

c3RotationEmbeds :
  Cyclic.embedC3InS3 Phase.phase1 ≡ Perm.permRotate
c3RotationEmbeds = refl

c2SwapEmbeds :
  Cyclic.embedC2InS3 Tower.inverse ≡ Perm.permSwapLowMid
c2SwapEmbeds = refl

c3ProperWitness :
  Cyclic.embedC3InS3 Phase.phase2 ≡ Perm.permSwapLowMid → ⊥
c3ProperWitness = Cyclic.c3ImageNeverSwapLowMid Phase.phase2

------------------------------------------------------------------------
-- SO(3) character data reconstruct the modular elliptic/genus budget.
------------------------------------------------------------------------

p3OrderTwoEllipticCount :
  Coupling.representationEllipticOrder2 Matrix.prime3 ≡ 0
p3OrderTwoEllipticCount = refl

p3OrderThreeEllipticCount :
  Coupling.representationEllipticOrder3 Matrix.prime3 ≡ 1
p3OrderThreeEllipticCount = refl

p29RepresentationGenusIsTwo :
  Coupling.representationX0Genus Matrix.prime29 ≡ 2
p29RepresentationGenusIsTwo = refl

p37RepresentationGenusIsTwo :
  Coupling.representationX0Genus Matrix.prime37 ≡ 2
p37RepresentationGenusIsTwo = refl

------------------------------------------------------------------------
-- The same representation-derived budget closes at Ogg primes and leaves the
-- known non-Ogg controls with positive Fricke/Frobenius defect.
------------------------------------------------------------------------

p29OrbitSaturates :
  Saturation.representationOrbitSaturated Matrix.prime29 ≡ true
p29OrbitSaturates = refl

p37OrbitDoesNotSaturate :
  Saturation.representationOrbitSaturated Matrix.prime37 ≡ false
p37OrbitDoesNotSaturate = refl

p67HasTwoFrobeniusPairs :
  Supersingular.representationFrobeniusTwoOrbitCount Matrix.prime67 ≡ 2
p67HasTwoFrobeniusPairs = refl

p71AllSevenSlotsFixed :
  Supersingular.representationSupersingularTotal Matrix.prime71 ≡ 7
p71AllSevenSlotsFixed = refl

p71NoFrobeniusPair :
  Supersingular.representationFrobeniusTwoOrbitCount Matrix.prime71 ≡ 0
p71NoFrobeniusPair = refl

------------------------------------------------------------------------
-- p=2 remains the spinorial SU(2) boundary and closes separately.
------------------------------------------------------------------------

p2IsTwoDimensionalSpinor : AllPrime.spinorPrime2Dimension ≡ 2
p2IsTwoDimensionalSpinor = refl

p2CoupledClosure :
  AllPrime.representationArithmeticFrickeClosed AllPrime.spinorPrime2 ≡ true
p2CoupledClosure = refl

finitePrimeControlUniverseHasTwentyRows :
  Matrix.listCount AllPrime.allPrimeCandidatesUnder72 ≡ 20
finitePrimeControlUniverseHasTwentyRows =
  AllPrime.allPrimeCandidateCountIsTwenty

finiteOggControlLocusHasFifteenRows :
  Matrix.listCount AllPrime.oggPrimeCandidatesUnder72 ≡ 15
finiteOggControlLocusHasFifteenRows =
  AllPrime.oggPrimeCandidateCountIsFifteen
