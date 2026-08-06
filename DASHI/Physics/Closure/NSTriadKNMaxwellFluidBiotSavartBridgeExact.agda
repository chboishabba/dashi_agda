module DASHI.Physics.Closure.NSTriadKNMaxwellFluidBiotSavartBridgeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: James Clerk Maxwell.
-- Title: "A Treatise on Electricity and Magnetism".
-- Clarendon Press, 1873.
-- DOI: not applicable to the original historical monograph.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- PURPOSE
-- Cross-pollinate the repository's Maxwell/physical-constants lane with the
-- Navier--Stokes Fourier lane without conflating their dynamics.  Both the
-- magnetostatic current-to-field map and the incompressible
-- vorticity-to-velocity map use the same inverse-curl amplitude
--
--   |k|^{-2} (k cross source),
--
-- up to an externally fixed coupling/normalisation coefficient.  We prove
-- exact scaling, transversality and the relation between the two operators.
-- Maxwell constitutive closure and fluid regularity remain different theorem
-- surfaces; sharing the elliptic kernel does not transfer a regularity result.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Optics.PhysicalConstantsKernelClosure as Constants

coupledBiotSavart :
  ℚ → V.ProjectionMode → V.Vector3 → V.Vector3
coupledBiotSavart coupling modeData source =
  V.scale coupling (BS.biotSavart modeData source)

fluidVelocityFromVorticity :
  V.ProjectionMode → V.Vector3 → V.Vector3
fluidVelocityFromVorticity = coupledBiotSavart 1ℚ

magneticFieldFromCurrent :
  ℚ → V.ProjectionMode → V.Vector3 → V.Vector3
magneticFieldFromCurrent = coupledBiotSavart

coupledBiotSavartCoordinates :
  (coupling : ℚ) →
  (modeData : V.ProjectionMode) →
  (source : V.Vector3) →
  coupledBiotSavart coupling modeData source
  ≡ V.scale coupling (BS.biotSavart modeData source)
coupledBiotSavartCoordinates coupling modeData source = refl

magneticFluidRelation :
  (electromagneticCoupling : ℚ) →
  (modeData : V.ProjectionMode) →
  (source : V.Vector3) →
  magneticFieldFromCurrent electromagneticCoupling modeData source
  ≡ V.scale electromagneticCoupling
      (fluidVelocityFromVorticity modeData source)
magneticFluidRelation electromagneticCoupling modeData
  (V.v3 sx sy sz)
  with BS.biotSavart modeData (V.v3 sx sy sz)
... | V.v3 bx by bz =
  V.vectorExt
    (solve (electromagneticCoupling ∷ bx ∷ []))
    (solve (electromagneticCoupling ∷ by ∷ []))
    (solve (electromagneticCoupling ∷ bz ∷ []))

coupledBiotSavartTransverse :
  (coupling : ℚ) →
  (modeData : V.ProjectionMode) →
  (source : V.Vector3) →
  V.dot (V.mode modeData)
    (coupledBiotSavart coupling modeData source)
  ≡ 0ℚ
coupledBiotSavartTransverse coupling modeData source =
  trans
    (V.dotScaleRight
      (V.mode modeData)
      (BS.biotSavart modeData source)
      coupling)
    (trans
      (cong (coupling *_)
        (BS.biotSavartTransverse modeData source))
      (solve (coupling ∷ [])))

maxwellConstitutiveLaneRemainsSeparate :
  Constants.status Constants.maxwellWaveSpeedClosure
  ≡ Constants.symbolicIdentityClosed
maxwellConstitutiveLaneRemainsSeparate = refl
