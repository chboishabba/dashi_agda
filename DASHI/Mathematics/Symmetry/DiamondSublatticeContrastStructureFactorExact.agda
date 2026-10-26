module DASHI.Mathematics.Symmetry.DiamondSublatticeContrastStructureFactorExact where

-- A necessary occupancy/form-factor discriminator for crystal diffraction.
-- Reuses the eight *actual* source-defined diamond sites; models
-- a UNIFORM A-versus-B sublattice amplitude difference, which is
-- not the same as ONE localized NV defect or its dilute scattering.
-- Classical structure-factor and kinematic diffraction prior art.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_)
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.DiamondEightSiteStructureFactorExact as Diff

bAmplitude : D.Quarter → D.Quarter → D.Quarter → Diff.Gaussian
bAmplitude h k l =
  Diff.gadd
    (Diff.gadd (Diff.sitePhase Diff.p111 h k l)
               (Diff.sitePhase Diff.p133 h k l))
    (Diff.gadd (Diff.sitePhase Diff.p313 h k l)
               (Diff.sitePhase Diff.p331 h k l))

-- Amplitudes represent symbolic scattering coefficients for
-- every site of an entire A or B sublattice (periodic model).
decoratedAmplitude :
  Diff.Gaussian → Diff.Gaussian →
  D.Quarter → D.Quarter → D.Quarter → Diff.Gaussian
decoratedAmplitude a b h k l =
  Diff.gadd
    (Diff.gmul a (Diff.fccFactor h k l))
    (Diff.gmul b (bAmplitude h k l))

equalAtom222 :
  Diff.norm2
    (decoratedAmplitude Diff.gone Diff.gone D.q2 D.q2 D.q2)
  ≡ + 0
equalAtom222 = refl

-- Contrast example: if ALL B sites have zero scattering amplitude
-- while ALL A sites have amplitude one, 222 reappears with intensity
-- 16 in the same conventions; a single NV vacancy is NOT this model.
aOnly222 :
  Diff.norm2
    (decoratedAmplitude Diff.gone Diff.gzero D.q2 D.q2 D.q2)
  ≡ + 16
aOnly222 = refl

equalAtom111 :
  Diff.norm2
    (decoratedAmplitude Diff.gone Diff.gone D.q1 D.q1 D.q1)
  ≡ + 32
equalAtom111 = refl

-- A measured scattering pattern further requires species-specific,
-- momentum/energy-dependent form factors, finite-coherence effects,
-- disorder, sample geometry, instrument and error calibration.
