module DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC WILD-STACK CORRECTION CONJECTURE
--
-- EXTERNAL ARITHMETIC
--
-- Duncan--Swisher prove their monstrous-exponent formula for p > 3.  Their
-- small-characteristic continuation gives:
--
--   p=2 : 36, versus v_2(|M|)=46
--   p=3 : 18, versus v_3(|M|)=20
--
-- so the exact gaps are 10 and 2.
--
-- EXTERNAL GEOMETRIC CONTEXT
--
-- In characteristics 2 and 3 the moduli stack of elliptic curves is wildly
-- stacky: j=0 and j=1728 collide and the stabilizer groups jump.  Modern work
-- on wild stacky modular curves shows that this wild structure changes rings
-- of mod-p modular forms and can create genuinely non-lifting forms.
--
-- DASHI CANDIDATE CORRECTION
--
-- The classically grounded finite carriers constructed upstream have:
--
--   p=2 : 10 coarse sectors
--         = 2 oriented quadratic-order sheets
--           x 5 loop-reversal orbits of binary-tetrahedral inertia.
--
--   p=3 : 2 C2-orbits of the Deligne--Rapoport three-stratum local incidence
--         carrier: {node} and {two exchanged branches}.
--
-- Therefore the exact numerical identities are:
--
--   46 = 36 + 10
--   20 = 18 +  2.
--
-- This module makes that candidate correction law explicit while keeping the
-- decisive theorem flag FALSE: no cited source proves that the Monster
-- valuation discrepancy is an additive wild-stack/inertia correction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact as P2Moduli
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3Local
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical

------------------------------------------------------------------------
-- 1. Modern wild-stack source context.
------------------------------------------------------------------------

kobinzureickBrown : Source.AttributedSource
kobinzureickBrown =
  Source.mkNoDOISource
    "Andrew Kobin and David Zureick-Brown"
    "Wild Stacky Curves and Rings of Mod p Modular Forms"
    "arXiv:2510.08821"
    "2025"
    "https://arxiv.org/abs/2510.08821"
    Source.academicArticleSource
    "source context that characteristics 2 and 3 are wild for elliptic modular stacks, that j=0 and j=1728 collide with enlarged stabilizers, and that wild stack structure changes mod-p modular-form rings; does not state a Monster-exponent correction formula"
    Source.publicAttribution

wildStackCorrectionSourceAtlas : Source.AttributedSourceAtlas
wildStackCorrectionSourceAtlas =
  Source.mkSourceAtlas
    "small-characteristic wild-stack correction source atlas"
    "DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact"
    (kobinzureickBrown ∷ [])
    "modern geometric context for wild ramification and exceptional modular-form behaviour in characteristics 2 and 3; the additive Monster correction law remains a DASHI conjectural cross-weld"

------------------------------------------------------------------------
-- 2. Exact arithmetic gap surface.
------------------------------------------------------------------------

data SmallCharacteristicPrime : Set where
  primeTwo primeThree : SmallCharacteristicPrime

primeLane :
  SmallCharacteristicPrime ->
  Lane.MonsterPrimeLane
primeLane primeTwo = Lane.p2
primeLane primeThree = Lane.p3

duncanSwisherContinuation :
  SmallCharacteristicPrime ->
  Nat
duncanSwisherContinuation primeTwo = 36
duncanSwisherContinuation primeThree = 18

actualMonsterExponent :
  SmallCharacteristicPrime ->
  Nat
actualMonsterExponent p =
  Exponent.monsterOrderExponent (primeLane p)

wildGeometricSectorCount :
  SmallCharacteristicPrime ->
  Nat
wildGeometricSectorCount primeTwo = 10
wildGeometricSectorCount primeThree = 2

p2ContinuationIsThirtySix :
  duncanSwisherContinuation primeTwo ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p2
p2ContinuationIsThirtySix = refl

p3ContinuationIsEighteen :
  duncanSwisherContinuation primeThree ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p3
p3ContinuationIsEighteen = refl

p2ExactCorrectionIdentity :
  actualMonsterExponent primeTwo
  ≡
  duncanSwisherContinuation primeTwo
  + wildGeometricSectorCount primeTwo
p2ExactCorrectionIdentity =
  Exponent.p2ExceptionalGap

p3ExactCorrectionIdentity :
  actualMonsterExponent primeThree
  ≡
  duncanSwisherContinuation primeThree
  + wildGeometricSectorCount primeThree
p3ExactCorrectionIdentity =
  Exponent.p3ExceptionalGap

------------------------------------------------------------------------
-- 3. Geometry receipts for the correction counts.
------------------------------------------------------------------------

p2EnrichedModuliBoundary :
  P2Moduli.P2OrientedInertiaModuliProblemBoundary
p2EnrichedModuliBoundary =
  P2Moduli.canonicalP2OrientedInertiaModuliProblemBoundary

p2FiveInertiaBoundary :
  P2Inertia.P2BinaryTetrahedralInertiaFiveOrbitBoundary
p2FiveInertiaBoundary =
  P2Inertia.canonicalP2BinaryTetrahedralInertiaFiveOrbitBoundary

p3LocalStrataBoundary :
  P3Local.P3DeligneRapoportLocalStrataBoundary
p3LocalStrataBoundary =
  P3Local.canonicalP3DeligneRapoportLocalStrataBoundary

classicalSourcingBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalSourcingBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

------------------------------------------------------------------------
-- 4. Candidate law vs theorem boundary.
------------------------------------------------------------------------

data WildStackCorrectionTheorem : Set where
data SectorCountIsMonsterValuationContribution : Set where
data NumericalEqualityCreatesCausalMechanism : Set where
data DuncanSwisherAttributedWildStackCorrection : Set where

wildStackCorrectionTheoremStillOpen :
  WildStackCorrectionTheorem -> ⊥
wildStackCorrectionTheoremStillOpen ()

sectorCountNotYetProvedAsValuationContribution :
  SectorCountIsMonsterValuationContribution -> ⊥
sectorCountNotYetProvedAsValuationContribution ()

numericalEqualityDoesNotCreateMechanism :
  NumericalEqualityCreatesCausalMechanism -> ⊥
numericalEqualityDoesNotCreateMechanism ()

duncanSwisherNotCreditedWithDASHICorrection :
  DuncanSwisherAttributedWildStackCorrection -> ⊥
duncanSwisherNotCreditedWithDASHICorrection ()

correctionClaimOrigin : Attribution.ClaimOrigin
correctionClaimOrigin =
  Attribution.openRecognitionConjecture

record WildStackCorrectionBoundary : Set where
  constructor wild-stack-correction-boundary
  field
    duncanSwisherP2ContinuationThirtySix : Bool
    duncanSwisherP3ContinuationEighteen : Bool
    actualP2ExponentFortySix : Bool
    actualP3ExponentTwenty : Bool
    p2GeometricSectorCountTen : Bool
    p3GeometricOrbitCountTwo : Bool
    p2AdditiveIdentityExact : Bool
    p3AdditiveIdentityExact : Bool
    wildSmallPrimeModuliContextSourced : Bool
    additiveWildStackCorrectionProved : Bool
    sectorCountValuationMechanismProved : Bool
    numericalCoincidencePromotedToCause : Bool
    correctionAttributedToDuncanSwisher : Bool

canonicalWildStackCorrectionBoundary :
  WildStackCorrectionBoundary
canonicalWildStackCorrectionBoundary =
  wild-stack-correction-boundary
    true true true true true true true true true
    false false false false
