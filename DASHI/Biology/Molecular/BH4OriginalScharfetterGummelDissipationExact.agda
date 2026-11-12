module DASHI.Biology.Molecular.BH4OriginalScharfetterGummelDissipationExact where

------------------------------------------------------------------------
-- BH4 × 369: genuine Bishop-real SG *face* reuse and finite conservation.
--
-- This is not a new Bernoulli/exponential implementation. Every face
-- is the same BishopSGFaceState and bishopSGFaceFlux owned by
-- DASHI.Physics.Semiconductor.Device.BishopScharfetterGummelFaceFluxExact.
-- Exactly 54 native interior bonds and 29 source-indexed species.
--
-- Proven HERE: for arbitrary Bishop-real face fluxes (including ones
-- constructed from SG), every paired internal flux cancels. This
-- remains true after species-wise scaling and for all six original
-- rational CHNOP/signed-charge axes embedded in Bishop reals.
--
-- NOT proven here: denominator-free continuous B(0) extension;
-- nonzero denominators at the original 54×29 physical drops;
-- same-source Poisson potential; positive diffusion coefficients;
-- chemical detailed balance; log-affinity monotonicity, Lyapunov
-- dissipation or positive implicit root. The module name describes
-- its intended dependency chain, not those unpaid theorems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed
import DASHI.Physics.Semiconductor.Device.BishopScharfetterGummelFaceFluxExact as SG
import DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact as Finite

-- Matrix uses the SAME finite Vec carrier as the original RHS owner.
BishopMatrix : Nat → Nat → Set
BishopMatrix sites species = V.Vec (V.Vec R.ℝ species) sites

-- Source-indexed 54 SG faces × 29 species, using the actual preexisting
-- SG face implementation. No postulated B(x) or "calibrated" 2/1 weight.
bishopSGFaces :
  (series : Series.BishopElementaryPowerSeriesData) → Set
bishopSGFaces series =
  V.Vec (V.Vec (SG.BishopFaceState series) 29) 54

-- Each species carries one Bishop-real per-voxel transport prefactor.
-- To match the original solver, this is D_s/h^2, NOT the dimensional
-- semiconductor charge-current prefactor qD_s/h.
originalBishopSGFluxes :
  (series : Series.BishopElementaryPowerSeriesData) →
  V.Vec R.ℝ 29 →
  bishopSGFaces series →
  BishopMatrix 54 29
originalBishopSGFluxes series prefactors =
  V.map (λ faces →
    V.zipWith
      (λ factor face → R._*_ factor (SG.bishopSGFaceFlux face))
      prefactors faces)

-- At each symbolic Fin 54 / Fin 29, the value is the literal SAME
-- semiconductor SG face flux multiplied by its original rate scale.
originalBishopSGFluxAt :
  (series : Series.BishopElementaryPowerSeriesData)
  (prefactors : V.Vec R.ℝ 29)
  (faces : bishopSGFaces series)
  (bond : F.Fin 54) (species : F.Fin 29) →
  V.lookup
    (V.lookup (originalBishopSGFluxes series prefactors faces) bond)
    species
    ≡
  R._*_
    (V.lookup prefactors species)
    (SG.bishopSGFaceFlux
      (V.lookup (V.lookup faces bond) species))
originalBishopSGFluxAt series prefactors faces bond species =
  trans
    (cong (λ row → V.lookup row species)
      (Finite.qLookupMap
        (λ faceRow →
          V.zipWith
            (λ factor face → R._*_ factor (SG.bishopSGFaceFlux face))
            prefactors faceRow)
        faces bond))
    (lookupFaceScale prefactors (V.lookup faces bond) species)
  where
  lookupFaceScale :
    ∀ {n : Nat} →
    (prefactors : V.Vec R.ℝ n)
    (row : V.Vec (SG.BishopFaceState series) n)
    (species : F.Fin n) →
    V.lookup
      (V.zipWith
        (λ factor face → R._*_ factor (SG.bishopSGFaceFlux face))
        prefactors row) species
      ≡
    R._*_
      (V.lookup prefactors species)
      (SG.bishopSGFaceFlux (V.lookup row species))
  lookupFaceScale V.[] V.[] ()
  lookupFaceScale (V._∷_ scale scales) (V._∷_ face remaining) F.zero = refl
  lookupFaceScale (V._∷_ scale scales) (V._∷_ face remaining) (F.suc i) =
    lookupFaceScale scales remaining i

-- Pairing each edge's outward and inward contributions requires NO
-- exponential identity or positivity assumption. This is the
-- conservation property of the same oriented native face current.
pairedBishopSGSpecies :
  (weight rate : R.ℝ) → R.ℝ
pairedBishopSGSpecies weight rate =
  R._+_ (R.- (R._*_ weight rate)) (R._*_ weight rate)

pairedBishopSGSpeciesZero :
  (weight rate : R.ℝ) →
  R._≃_ (pairedBishopSGSpecies weight rate) R.0ℝ
pairedBishopSGSpeciesZero weight rate =
  let open RP.ℝ-Solver
  in solve 2
    (λ w flux →
      ((⊝ (w ⊗ flux)) ⊕ (w ⊗ flux))
      ⊜ Κ Q.0ℚᵘ)
    RP.≃-refl weight rate

pairedBishopSGRow :
  ∀ {n} → V.Vec R.ℝ n → V.Vec R.ℝ n → R.ℝ
pairedBishopSGRow V.[] V.[] = R.0ℝ
pairedBishopSGRow
  (V._∷_ weight weights) (V._∷_ rate rates) =
  R._+_ (pairedBishopSGSpecies weight rate)
        (pairedBishopSGRow weights rates)

pairedBishopSGRowZero :
  ∀ {n} (weights rates : V.Vec R.ℝ n) →
  R._≃_ (pairedBishopSGRow weights rates) R.0ℝ
pairedBishopSGRowZero V.[] V.[] = RP.≃-refl
pairedBishopSGRowZero
  (V._∷_ weight weights) (V._∷_ rate rates) =
  RP.≃-trans
    (RP.+-cong
      (pairedBishopSGSpeciesZero weight rate)
      (pairedBishopSGRowZero weights rates))
    (RP.+-identityˡ R.0ℝ)

pairedBishopSGNative :
  ∀ {bonds species} →
  V.Vec R.ℝ species →
  BishopMatrix bonds species → R.ℝ
pairedBishopSGNative weights V.[] = R.0ℝ
pairedBishopSGNative weights (V._∷_ row rows) =
  R._+_ (pairedBishopSGRow weights row)
        (pairedBishopSGNative weights rows)

pairedBishopSGNativeZero :
  ∀ {bonds species}
  (weights : V.Vec R.ℝ species)
  (fluxes : BishopMatrix bonds species) →
  R._≃_ (pairedBishopSGNative weights fluxes) R.0ℝ
pairedBishopSGNativeZero weights V.[] = RP.≃-refl
pairedBishopSGNativeZero weights (V._∷_ row rows) =
  RP.≃-trans
    (RP.+-cong
      (pairedBishopSGRowZero weights row)
      (pairedBishopSGNativeZero weights rows))
    (RP.+-identityˡ R.0ℝ)

-- Actual original 54×29 Bishop SG faces, arbitrary real-valued rates.
original369BishopSGAllNativeFacesConserve :
  (series : Series.BishopElementaryPowerSeriesData)
  (prefactors : V.Vec R.ℝ 29)
  (faces : bishopSGFaces series)
  (weights : V.Vec R.ℝ 29) →
  R._≃_
    (pairedBishopSGNative weights
      (originalBishopSGFluxes series prefactors faces))
    R.0ℝ
original369BishopSGAllNativeFacesConserve series prefactors faces weights =
  pairedBishopSGNativeZero weights
    (originalBishopSGFluxes series prefactors faces)

-- Six axes are obtained from the SAME source-indexed rational weights.
original369BishopSGSixAxesConserve :
  (series : Series.BishopElementaryPowerSeriesData)
  (prefactors : V.Vec R.ℝ 29)
  (faces : bishopSGFaces series)
  (sourceWeights : V.Vec (V.Vec Q.ℚᵘ 29) 6)
  (axis : F.Fin 6) →
  R._≃_
    (pairedBishopSGNative
      (V.map Embed.embed (V.lookup sourceWeights axis))
      (originalBishopSGFluxes series prefactors faces))
    R.0ℝ
original369BishopSGSixAxesConserve series prefactors faces sourceWeights axis =
  original369BishopSGAllNativeFacesConserve
    series prefactors faces
    (V.map Embed.embed (V.lookup sourceWeights axis))

-- Removable singularity boundary: at zero dimensionless drop, the
-- correct value is B(0)=1, so the net molar transfer is D/h^2(cL-cR).
-- The quotient-based semiconductor owner requires exp(x)-1 ≠ 0 and
-- therefore does NOT yet implement this branch for arbitrary drops.
zeroDropMolarFaceRate : R.ℝ → R.ℝ → R.ℝ → R.ℝ
zeroDropMolarFaceRate diffusivityOverH2 cLeft cRight =
  R._*_ diffusivityOverH2 (R._-_ cLeft cRight)

zeroDropIsPureDiffusion :
  (diffusivityOverH2 cLeft cRight : R.ℝ) →
  R._≃_
    (zeroDropMolarFaceRate diffusivityOverH2 cLeft cRight)
    (R._-_
      (R._*_ diffusivityOverH2 cLeft)
      (R._*_ diffusivityOverH2 cRight))
zeroDropIsPureDiffusion diffusivityOverH2 cLeft cRight =
  let open RP.ℝ-Solver
  in solve 3
    (λ d left right →
      (d ⊗ (left ⊖ right))
      ⊜ ((d ⊗ left) ⊖ (d ⊗ right)))
    RP.≃-refl diffusivityOverH2 cLeft cRight
