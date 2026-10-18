module DASHI.Moonshine.JInvariant369SSPLevelDihedralIntertwinerExact where

------------------------------------------------------------------------
-- SSP C2/C3 DIHEDRAL ACTION <-> LEVEL-3 CUSP DIHEDRAL ACTION
--
-- This is the positive companion to the earlier no-go theorem.
--
-- The no-go compared signed negation / spectral conjugation (a C2 operation)
-- directly with nontrivial cusp translation (a C3 operation), and correctly
-- proved that those generators cannot be identified.
--
-- The full SSP trit already carries BOTH generators:
--
--   * antipode : C2
--   * cycle    : C3
--
-- while the level-3 cusp fibre carries:
--
--   * inversion   : C2
--   * translation : C3.
--
-- With generators matched by role, the two finite action systems are exactly
-- equivariantly equivalent.  This remains a finite-carrier theorem: signed
-- FRACTRAN magnitude, prime-lane arithmetic, analytic modular curves, and the
-- full deck group are NOT identified by this codec.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (neg; zer; pos; []; _∷_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact as SSPDihedral
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariantColourWheelWaveSignedBidiExact as SignedJ
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Canonical
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- 1. Exact finite carrier codec.
------------------------------------------------------------------------

sspToLevel3 :
  SSP.SSPTrit →
  Level.level3CuspFibre
sspToLevel3 SSP.sspNegOne = neg ∷ []
sspToLevel3 SSP.sspZero   = zer ∷ []
sspToLevel3 SSP.sspPosOne = pos ∷ []

level3ToSSP :
  Level.level3CuspFibre →
  SSP.SSPTrit
level3ToSSP (neg ∷ []) = SSP.sspNegOne
level3ToSSP (zer ∷ []) = SSP.sspZero
level3ToSSP (pos ∷ []) = SSP.sspPosOne

sspLevel3RoundTrip :
  (t : SSP.SSPTrit) →
  level3ToSSP (sspToLevel3 t) ≡ t
sspLevel3RoundTrip SSP.sspNegOne = refl
sspLevel3RoundTrip SSP.sspZero = refl
sspLevel3RoundTrip SSP.sspPosOne = refl

level3SSPRoundTrip :
  (x : Level.level3CuspFibre) →
  sspToLevel3 (level3ToSSP x) ≡ x
level3SSPRoundTrip (neg ∷ []) = refl
level3SSPRoundTrip (zer ∷ []) = refl
level3SSPRoundTrip (pos ∷ []) = refl

------------------------------------------------------------------------
-- 2. C3 generator intertwiner: SSP cycle == cusp translation.
------------------------------------------------------------------------

sspCycleIntertwinesLevel3Translation :
  (t : SSP.SSPTrit) →
  sspToLevel3 (SSPDihedral.cycle t)
  ≡
  Canonical.translateLevel3Residue (sspToLevel3 t)
sspCycleIntertwinesLevel3Translation SSP.sspNegOne = refl
sspCycleIntertwinesLevel3Translation SSP.sspZero = refl
sspCycleIntertwinesLevel3Translation SSP.sspPosOne = refl

------------------------------------------------------------------------
-- 3. C2 generator intertwiner: SSP antipode == cusp inversion.
------------------------------------------------------------------------

sspAntipodeIntertwinesLevel3Inversion :
  (t : SSP.SSPTrit) →
  sspToLevel3 (SSPDihedral.antipode t)
  ≡
  Arithmetic.negateResidue (sspToLevel3 t)
sspAntipodeIntertwinesLevel3Inversion SSP.sspNegOne = refl
sspAntipodeIntertwinesLevel3Inversion SSP.sspZero = refl
sspAntipodeIntertwinesLevel3Inversion SSP.sspPosOne = refl

------------------------------------------------------------------------
-- 4. The dihedral relation is transported exactly.
------------------------------------------------------------------------

sspDihedralConjugacyAtLevel3 :
  (t : SSP.SSPTrit) →
  sspToLevel3
    (SSPDihedral.antipode
      (SSPDihedral.cycle
        (SSPDihedral.antipode t)))
  ≡
  Arithmetic.addResidue
    (Arithmetic.negateResidue (Level.oneResidue Q.one))
    (sspToLevel3 t)
sspDihedralConjugacyAtLevel3 t =
  trans
    (sspAntipodeIntertwinesLevel3Inversion
      (SSPDihedral.cycle (SSPDihedral.antipode t)))
    (trans
      (cong Arithmetic.negateResidue
        (sspCycleIntertwinesLevel3Translation
          (SSPDihedral.antipode t)))
      (trans
        (cong
          (λ x →
            Arithmetic.negateResidue
              (Canonical.translateLevel3Residue x))
          (sspAntipodeIntertwinesLevel3Inversion t))
        (Level.inversionConjugatesTranslationToInverse
          Level.canonicalCuspDihedralAt3
          (sspToLevel3 t))))

------------------------------------------------------------------------
-- 5. Spectral C3 is the same finite trit chart, but only after transporting
--    the C3 action.  Conjugation remains the C2 generator.
------------------------------------------------------------------------

spectralToLevel3 :
  Spectral.AxisFrequency →
  Level.level3CuspFibre
spectralToLevel3 f =
  sspToLevel3 (SignedJ.frequencyToSSP f)

level3ToSpectral :
  Level.level3CuspFibre →
  Spectral.AxisFrequency
level3ToSpectral x =
  SignedJ.sspToFrequency (level3ToSSP x)

spectralLevel3RoundTrip :
  (f : Spectral.AxisFrequency) →
  level3ToSpectral (spectralToLevel3 f) ≡ f
spectralLevel3RoundTrip Spectral.frequencyNegative = refl
spectralLevel3RoundTrip Spectral.frequencyZero = refl
spectralLevel3RoundTrip Spectral.frequencyPositive = refl

level3SpectralRoundTrip :
  (x : Level.level3CuspFibre) →
  spectralToLevel3 (level3ToSpectral x) ≡ x
level3SpectralRoundTrip (neg ∷ []) = refl
level3SpectralRoundTrip (zer ∷ []) = refl
level3SpectralRoundTrip (pos ∷ []) = refl

spectralConjugationIntertwinesLevel3Inversion :
  (f : Spectral.AxisFrequency) →
  spectralToLevel3 (Spectral.conjugateFrequency f)
  ≡
  Arithmetic.negateResidue (spectralToLevel3 f)
spectralConjugationIntertwinesLevel3Inversion Spectral.frequencyNegative = refl
spectralConjugationIntertwinesLevel3Inversion Spectral.frequencyZero = refl
spectralConjugationIntertwinesLevel3Inversion Spectral.frequencyPositive = refl

spectralCycle :
  Spectral.AxisFrequency →
  Spectral.AxisFrequency
spectralCycle f =
  SignedJ.sspToFrequency
    (SSPDihedral.cycle (SignedJ.frequencyToSSP f))

spectralCycleIntertwinesLevel3Translation :
  (f : Spectral.AxisFrequency) →
  spectralToLevel3 (spectralCycle f)
  ≡
  Canonical.translateLevel3Residue (spectralToLevel3 f)
spectralCycleIntertwinesLevel3Translation Spectral.frequencyNegative = refl
spectralCycleIntertwinesLevel3Translation Spectral.frequencyZero = refl
spectralCycleIntertwinesLevel3Translation Spectral.frequencyPositive = refl

------------------------------------------------------------------------
-- 6. Signed FRACTRAN magnitude remains a strict residual above this coarse
--    equivariant C3 codec.
------------------------------------------------------------------------

signedMultiplicityToSSP :
  Signed.SignedMultiplicity →
  SSP.SSPTrit
signedMultiplicityToSSP (Signed.negativeMultiplicity n) = SSP.sspNegOne
signedMultiplicityToSSP Signed.zeroMultiplicity = SSP.sspZero
signedMultiplicityToSSP (Signed.positiveMultiplicity n) = SSP.sspPosOne

signedMultiplicityLevel3Observer :
  Signed.SignedMultiplicity →
  Level.level3CuspFibre
signedMultiplicityLevel3Observer m =
  sspToLevel3 (signedMultiplicityToSSP m)

signedMagnitude :
  Signed.SignedMultiplicity → Nat
signedMagnitude (Signed.negativeMultiplicity n) = n
signedMagnitude Signed.zeroMultiplicity = 0
signedMagnitude (Signed.positiveMultiplicity n) = n

samePositiveLevel3Observation :
  signedMultiplicityLevel3Observer (Signed.positiveMultiplicity 1)
  ≡
  signedMultiplicityLevel3Observer (Signed.positiveMultiplicity 2)
samePositiveLevel3Observation = refl

differentPositiveMagnitude :
  signedMagnitude (Signed.positiveMultiplicity 1)
  ≡
  signedMagnitude (Signed.positiveMultiplicity 2) →
  ⊥
differentPositiveMagnitude ()

signedMagnitudeLevel3NonDescent :
  Descent.ConsumerNonDescentWitness
    signedMultiplicityLevel3Observer
    signedMagnitude
signedMagnitudeLevel3NonDescent =
  Descent.consumerNonDescentWitness
    (Signed.positiveMultiplicity 1)
    (Signed.positiveMultiplicity 2)
    samePositiveLevel3Observation
    differentPositiveMagnitude

signedMagnitudeCannotFactorThroughLevel3 :
  Descent.FactorsThrough
    signedMultiplicityLevel3Observer
    signedMagnitude →
  ⊥
signedMagnitudeCannotFactorThroughLevel3 =
  Descent.nonDescentWitnessBlocksFactorization
    signedMagnitudeLevel3NonDescent

------------------------------------------------------------------------
-- 7. Exact claim boundary.
------------------------------------------------------------------------

record SSPLevel3DihedralIntertwinerBoundary : Set where
  constructor ssp-level3-dihedral-intertwiner-boundary
  field
    finiteCarrierBijectionExact : Bool
    c3CycleTranslationIntertwinerExact : Bool
    c2AntipodeInversionIntertwinerExact : Bool
    dihedralActionIntertwinerExact : Bool
    spectralConjugationInversionIntertwinerExact : Bool
    spectralCycleTranslationIntertwinerExact : Bool

    signedMagnitudeFactorsThroughLevel3 : Bool
    signedFRACTRANArithmeticEqualsCuspArithmetic : Bool
    analyticModularCurveIdentified : Bool
    fullDeckGroupIdentifiedWithDihedralC3 : Bool

open SSPLevel3DihedralIntertwinerBoundary public

canonicalSSPLevel3DihedralIntertwinerBoundary :
  SSPLevel3DihedralIntertwinerBoundary
canonicalSSPLevel3DihedralIntertwinerBoundary =
  ssp-level3-dihedral-intertwiner-boundary
    true true true true true true
    false false false false
