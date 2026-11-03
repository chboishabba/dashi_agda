{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017ControlledPointerRecordUnitaryExact where

-- P01.L13 large proof cut: actual finite C^2 pointer-controlled record
-- emission, not a freely declared environment-overlap number.
--
-- Each local pulse is a real two-by-two rotation on a COMPLEX environment
-- qubit: (a,b) -> (c*a-s*b, s*a+c*b), with c^2+s^2=1. The controlled
-- direct-sum action is identity on the right branch and rotation on the
-- wrong branch. We prove its full four-complex-coordinate Born norm
-- conservation for ALL input vectors, produce site records by actually
-- applying this pulse to a common vacuum, and consume those generated
-- records in the EXISTING heterogeneous ORIGINAL TSVF/ABL theorem.
--
-- This is a nontrivial finite four-complex-coordinate linear isometry,
-- not a claimed physical many-body source, actual cosmological final bra,
-- selected Lorentz clock, real Hilbert completion, or Clay YM solution.
-- Scientific attribution: Aharonov/Bergmann/Lebowitz, Aharonov/Vaidman,
-- Aharonov/Cohen/Landsberger (2017). Reuse original DASHI rational complex
-- and TSVF/ABL source owners; no duplicate probability definition.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; mkℚ; _+_; _-_; _*_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as Env
import DASHI.Quantum.TSVF2017HeterogeneousEnvironmentABLExact as Hetero
import DASHI.Quantum.TSVFComplexGammaProductBornExact as Gamma

record CertifiedRotation : Set where
  constructor certifiedRotation
  field
    c s : ℚ
    circleLaw : c * c + s * s ≡ 1ℚ
open CertifiedRotation public

-- The rotation is complex linear, defined in actual complex coordinates.
rotateRaw : ℚ → ℚ → Env.ComplexPointerRecord →
  Env.ComplexPointerRecord
rotateRaw c s (Env.pointerRecord (C.complex a b) (C.complex d e)) =
  Env.pointerRecord
    (C.complex (c * a - s * d) (c * b - s * e))
    (C.complex (s * a + c * d) (s * b + c * e))

rotate : CertifiedRotation → Env.ComplexPointerRecord →
  Env.ComplexPointerRecord
rotate pulse = rotateRaw (c pulse) (s pulse)

qubitBornNorm : Env.ComplexPointerRecord → ℚ
qubitBornNorm (Env.pointerRecord a b) =
  C.complexNormSq a + C.complexNormSq b

-- The intermediate scale factor is derived, not assumed to be one.
rotationNormScalesExactly :
  (c s : ℚ) (v : Env.ComplexPointerRecord) →
  qubitBornNorm (rotateRaw c s v)
  ≡ (c * c + s * s) * qubitBornNorm v
rotationNormScalesExactly c s
  (Env.pointerRecord (C.complex a b) (C.complex d e)) =
  solve (c ∷ s ∷ a ∷ b ∷ d ∷ e ∷ [])

rotationPreservesBornNorm :
  (pulse : CertifiedRotation) (v : Env.ComplexPointerRecord) →
  qubitBornNorm (rotate pulse v) ≡ qubitBornNorm v
rotationPreservesBornNorm pulse v =
  trans
    (rotationNormScalesExactly (c pulse) (s pulse) v)
    (trans
      (cong (λ q → q * qubitBornNorm v) (circleLaw pulse))
      (ℚₚ.*-identityˡ (qubitBornNorm v)))

------------------------------------------------------------------------
-- A genuine controlled action on C^2(pointer) tensor C^2(environment):
-- the two environment sectors form a DIRECT SUM of four complex coords.
------------------------------------------------------------------------

record PointerEnvironment : Set where
  constructor pointerEnvironment
  field
    rightSector wrongSector : Env.ComplexPointerRecord
open PointerEnvironment public

pointerEnvironmentNorm : PointerEnvironment → ℚ
pointerEnvironmentNorm v =
  qubitBornNorm (rightSector v) + qubitBornNorm (wrongSector v)

controlledRecordPulse : CertifiedRotation → PointerEnvironment →
  PointerEnvironment
controlledRecordPulse pulse v =
  pointerEnvironment (rightSector v) (rotate pulse (wrongSector v))

controlledRecordPreservesFullBornNorm :
  (pulse : CertifiedRotation) (v : PointerEnvironment) →
  pointerEnvironmentNorm (controlledRecordPulse pulse v)
  ≡ pointerEnvironmentNorm v
controlledRecordPreservesFullBornNorm pulse v =
  cong (λ q → qubitBornNorm (rightSector v) + q)
    (rotationPreservesBornNorm pulse (wrongSector v))

vacuum : Env.ComplexPointerRecord
vacuum = Env.pointerRecord C.oneC C.zeroC

preparedPointerEnvironment : PointerEnvironment
preparedPointerEnvironment = pointerEnvironment vacuum vacuum

emittedEnvironmentSite : CertifiedRotation → Hetero.EnvironmentSite
emittedEnvironmentSite pulse =
  Hetero.environmentSite
    (rightSector (controlledRecordPulse pulse preparedPointerEnvironment))
    (wrongSector (controlledRecordPulse pulse preparedPointerEnvironment))

rightEmissionIsOriginalVacuum :
  (pulse : CertifiedRotation) →
  Hetero.rightRecord (emittedEnvironmentSite pulse) ≡ vacuum
rightEmissionIsOriginalVacuum pulse = refl

wrongEmissionIsControlledRotation :
  (pulse : CertifiedRotation) →
  Hetero.wrongRecord (emittedEnvironmentSite pulse)
  ≡ rotate pulse vacuum
wrongEmissionIsControlledRotation pulse = refl

emittedSiteList : List CertifiedRotation → List Hetero.EnvironmentSite
emittedSiteList = map emittedEnvironmentSite

-- Original gamma phases and ORIGINAL ABL, now sourced by actual finite
-- norm-preserving controlled pulses rather than arbitrary overlap labels.
pulseGeneratedWrongABLFactorization :
  (gammas : List C.RationalComplex) (pulses : List CertifiedRotation) →
  Hetero.OriginalABL.numerator
    (Hetero.wrongABL gammas (emittedSiteList pulses))
  ≡ Gamma.complexGammaBornWeight gammas
      * Hetero.tensorBornProduct (emittedSiteList pulses)
pulseGeneratedWrongABLFactorization gammas pulses =
  Hetero.heterogeneousOriginalABLHasCorrectBornFactor
    gammas (emittedSiteList pulses)

pulseGeneratedOriginalABLNormalizes :
  (gammas : List C.RationalComplex) (pulses : List CertifiedRotation) →
  Hetero.OriginalABL.numerator
    (Hetero.rightABL gammas (emittedSiteList pulses))
  + Hetero.OriginalABL.numerator
    (Hetero.wrongABL gammas (emittedSiteList pulses))
  ≡ Hetero.OriginalABL.denominator
    (Hetero.rightABL gammas (emittedSiteList pulses))
pulseGeneratedOriginalABLNormalizes gammas pulses =
  Hetero.heterogeneousOriginalABLNormalizes
    gammas (emittedSiteList pulses)

------------------------------------------------------------------------
-- A nondegenerate rational 3/5,4/5 certified rotation. This pulse
-- EMITS the actual source-owned 2017 finite overlap 3/5, hence 9/25 Born.
------------------------------------------------------------------------

threeFifths fourFifths nineTwentyFifths : ℚ
threeFifths = mkℚ (+ 3) 5 _
fourFifths = mkℚ (+ 4) 5 _
nineTwentyFifths = mkℚ (+ 9) 25 _

threeFourCircleLaw :
  threeFifths * threeFifths + fourFifths * fourFifths ≡ 1ℚ
threeFourCircleLaw = solve []

threeFourPulse : CertifiedRotation
threeFourPulse =
  certifiedRotation threeFifths fourFifths threeFourCircleLaw

threeFourPulseEmitsOriginalWrongQubit :
  rotate threeFourPulse vacuum
  ≡ Env.pointerRecord
      (C.complex threeFifths 0ℚ) (C.complex fourFifths 0ℚ)
threeFourPulseEmitsOriginalWrongQubit =
  cong₂ Env.pointerRecord
    (C.complexExt (solve []) (solve []))
    (C.complexExt (solve []) (solve []))

threeFourPulseOverlap :
  Hetero.siteOverlap (emittedEnvironmentSite threeFourPulse)
  ≡ C.complex threeFifths 0ℚ
threeFourPulseOverlap =
  trans
    (cong (λ v → Env.hermitianPair vacuum v)
      threeFourPulseEmitsOriginalWrongQubit)
    (C.complexExt (solve []) (solve []))

threeFourPulseBornNineTwentyFifths :
  Hetero.siteBorn (emittedEnvironmentSite threeFourPulse)
  ≡ nineTwentyFifths
threeFourPulseBornNineTwentyFifths =
  trans
    (cong C.complexNormSq threeFourPulseOverlap)
    (solve [])

-- Proven: the complex ABL/environment theorem now has a concrete
-- norm-preserving one-step emitter for the 3/5 source overlap.
-- NOT proven: genuine many-body full physical unitary evolution with
-- arbitrary environmental coupling, correlated states, gamma disturbance
-- bounds, postselected cosmological final bra or OS same physical clock.
