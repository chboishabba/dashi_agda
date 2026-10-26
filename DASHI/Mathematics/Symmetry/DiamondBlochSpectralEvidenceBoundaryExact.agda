module DASHI.Mathematics.Symmetry.DiamondBlochSpectralEvidenceBoundaryExact where

-- Same ideal diamond neighbour/basis geometry as source owner
-- DiamondNearestNeighbourBlochExact. Mathematical intensity-vs-phase
-- separation cross-pollinates PR #1272 (FourierPixel); no experiment,
-- device or sensor measurement is transferred between branches.
--
-- One band-squared scalar can remain cubic-invariant even when an
-- atomically decorated A/B crystal breaks a sublattice-changing glide.
-- Consequently spectral *value* symmetry is weaker than a complete
-- material/space-group/quantum representation witness.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.Bool using (Bool)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.DiamondEightSiteStructureFactorExact as Diff
import DASHI.Mathematics.Symmetry.DiamondNearestNeighbourBlochExact as Bloch
import DASHI.Mathematics.Symmetry.DiamondSublatticeContrastStructureFactorExact as Contrast
import DASHI.Mathematics.Symmetry.DiamondFccPrimitiveGlideExact as FCC

-- A two-sublattice staggered-mass *squared* spectral observable:
-- for spinless H_m(k) = [[m,Gamma(k)],[Gamma*(k),-m]], one has
-- squared eigenvalues E²=m²+|Gamma|². This statement fixes a toy
-- mass term; m is not a measured crystal or NV parameter.
massSquaredEnergy : ℤ → Bloch.K4 → ℤ
massSquaredEnergy m q = (m * m) + Bloch.squaredGap q

massSquaredFullCubicInvariant :
  (m : ℤ) (p : Bloch.Perm3)
  (sx sy sz : Bool) (q : Bloch.K4) →
  massSquaredEnergy m (Bloch.signedPermute p sx sy sz q)
  ≡ massSquaredEnergy m q
massSquaredFullCubicInvariant m p sx sy sz q =
  cong (λ n → (m * m) + n)
       (Bloch.squaredBandFullCubicInvariant p sx sy sz q)

originSample : Bloch.K4
originSample = Bloch.k4 D.q0 D.q0 D.q0

bodySample : Bloch.K4
bodySample = Bloch.k4 D.q1 D.q1 D.q1

-- The scalar |Gamma|² agrees at these two different momenta,
-- but the complex field Gamma itself is provably distinct.
sameScalarDifferentPhase :
  Bloch.squaredGap originSample ≡ Bloch.squaredGap bodySample
sameScalarDifferentPhase = refl

differentComplexAmplitude :
  Bloch.gamma originSample ≡ Bloch.gamma bodySample → ⊥
differentComplexAmplitude ()

noPhaseRecoveryFromBareSpectrum :
  (decode : ℤ → Diff.Gaussian) →
  ((q : Bloch.K4) →
    decode (Bloch.squaredGap q) ≡ Bloch.gamma q) →
  ⊥
noPhaseRecoveryFromBareSpectrum decode exact =
  differentComplexAmplitude
    (trans (sym (exact originSample))
      (trans (cong decode sameScalarDifferentPhase)
        (exact bodySample)))

-- The pre-existing A/B scattering contrast is a concrete *site*
-- witness for lost glide symmetry, whereas the mass² spectral
-- function above is invariant under all 48 cubic index maps.
-- This is a logically valid warning, not a claim that this mass
-- directly produces the same X-ray scattering amplitudes:
spectralInvarianceDoesNotSupplyGlide :
  (∀ s → Contrast.contrastWeight
    (FCC.glideXSite s)
      ≡ Contrast.contrastWeight s) →
  ⊥
spectralInvarianceDoesNotSupplyGlide =
  Contrast.uniformContrastBreaksDiamondGlide

-- For a physically discriminating readout, the consumer needs:
-- (1) the actual species/defect/strain and spin-orbital carrier;
-- (2) symmetry-conjugation of the WHOLE Hamiltonian/measurement;
-- (3) field/reference conventions and an identifiable phase observable;
-- (4) calibrated same-device evidence, as owned by NV PR #1269.
