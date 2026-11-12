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

------------------------------------------------------------------------
-- Correct source-independent SG edge entropy factorization.
--
-- Let qL = cL B(x), qR = cR B(-x), and let logL/logR be
-- actual logarithms of those POSITIVE quantities (not established
-- in the current Bishop log owner). The molar face rate is
--       k (qL-qR)
-- while its chemical potential difference is
--       RT (logR-logL).
-- Thus the signed transport power is exactly
--       -k RT (qL-qR)(logL-logR).
--
-- The algebraic equality is fully proved here. Deriving
-- 0 ≤ (qL-qR)(logL-logR) from a concrete Bishop logarithm's
-- monotonicity, and deriving the chemical potentials of the
-- original Poisson-coupled BH4 source, remain independent OPEN
-- analytic obligations. No hidden entropy-positivity premise.
------------------------------------------------------------------------

sgTransportPower :
  (rate RT qL qR logL logR : R.ℝ) → R.ℝ
sgTransportPower rate RT qL qR logL logR =
  R._*_
    (R._*_ rate (R._-_ qL qR))
    (R._*_ RT (R._-_ logR logL))

sgEntropyProductionFactor :
  (rate RT qL qR logL logR : R.ℝ) → R.ℝ
sgEntropyProductionFactor rate RT qL qR logL logR =
  R._*_
    (R._*_ rate RT)
    (R._*_
      (R._-_ qL qR)
      (R._-_ logL logR))

sgTransportPowerIsNegativeEntropyProduction :
  (rate RT qL qR logL logR : R.ℝ) →
  R._≃_
    (sgTransportPower rate RT qL qR logL logR)
    (R.- (sgEntropyProductionFactor rate RT qL qR logL logR))
sgTransportPowerIsNegativeEntropyProduction
  rate RT qL qR logL logR =
  let open RP.ℝ-Solver
  in solve 6
    (λ rate′ rt′ left′ right′ logLeft′ logRight′ →
      ((rate′ ⊗ (left′ ⊖ right′))
       ⊗ (rt′ ⊗ (logRight′ ⊖ logLeft′)))
      ⊜
      (⊝ ((rate′ ⊗ rt′)
       ⊗ ((left′ ⊖ right′)
       ⊗ (logLeft′ ⊖ logRight′)))))
    RP.≃-refl rate RT qL qR logL logR

-- Equilibrium equality is allowed: the transport contribution
-- vanishes when the two Bernoulli-weighted positive activities
-- coincide, even at nonzero potential drop.
sgEqualActivitiesHaveZeroPower :
  (rate RT activity logActivity : R.ℝ) →
  R._≃_
    (sgTransportPower
      rate RT activity activity logActivity logActivity)
    R.0ℝ
sgEqualActivitiesHaveZeroPower rate RT activity logActivity =
  let open RP.ℝ-Solver
  in solve 4
    (λ r t a l →
      ((r ⊗ (a ⊖ a)) ⊗ (t ⊗ (l ⊖ l)))
      ⊜ Κ Q.0ℚᵘ)
    RP.≃-refl rate RT activity logActivity

------------------------------------------------------------------------
-- Stronger CONCRETE Bishop face specialization, available when each
-- dimensionless drop has a certified 0 < drop ≤ 1 chart.
-- This imports the *constructed* Bishop exponential/Bernoulli inverse
-- from the existing semiconductor owner, not an unspecified power
-- series dataSet. General negative/large/zero drops remain OPEN.
------------------------------------------------------------------------

import DASHI.Physics.Semiconductor.Device.BishopConcreteScharfetterGummelFaceFluxExact
  as ConcreteSG

originalConcreteSGFaces : Set₁
originalConcreteSGFaces =
  V.Vec (V.Vec ConcreteSG.ConcreteBishopFaceState 29) 54

originalConcreteSGFluxes :
  V.Vec R.ℝ 29 → originalConcreteSGFaces → BishopMatrix 54 29
originalConcreteSGFluxes prefactors =
  V.map (λ faces →
    V.zipWith
      (λ factor face →
        R._*_ factor (ConcreteSG.concreteBishopSGFaceFlux face))
      prefactors faces)

originalConcreteSGFluxAt :
  (prefactors : V.Vec R.ℝ 29)
  (faces : originalConcreteSGFaces)
  (bond : F.Fin 54) (sp : F.Fin 29) →
  V.lookup (V.lookup (originalConcreteSGFluxes prefactors faces) bond) sp
    ≡
  R._*_
    (V.lookup prefactors sp)
    (ConcreteSG.concreteBishopSGFaceFlux
      (V.lookup (V.lookup faces bond) sp))
originalConcreteSGFluxAt prefactors faces bond sp =
  trans
    (cong (λ row → V.lookup row sp)
      (lookupConcreteMap prefactors faces bond))
    (lookupScale prefactors (V.lookup faces bond) sp)
  where
  lookupConcreteMap :
    ∀ {n : Nat}
    (p : V.Vec R.ℝ 29)
    (rows : V.Vec (V.Vec ConcreteSG.ConcreteBishopFaceState 29) n)
    (index : F.Fin n) →
    V.lookup (V.map
      (λ row → V.zipWith
        (λ factor face →
          R._*_ factor (ConcreteSG.concreteBishopSGFaceFlux face))
        p row) rows) index
    ≡
    V.zipWith
      (λ factor face →
        R._*_ factor (ConcreteSG.concreteBishopSGFaceFlux face))
      p (V.lookup rows index)
  lookupConcreteMap p V.[] ()
  lookupConcreteMap p (V._∷_ row rows) F.zero = refl
  lookupConcreteMap p (V._∷_ row rows) (F.suc index) =
    lookupConcreteMap p rows index

  lookupScale :
    ∀ {n : Nat}
    (p : V.Vec R.ℝ n)
    (row : V.Vec ConcreteSG.ConcreteBishopFaceState n)
    (index : F.Fin n) →
    V.lookup
      (V.zipWith
        (λ factor face →
          R._*_ factor (ConcreteSG.concreteBishopSGFaceFlux face))
        p row) index
    ≡
    R._*_
      (V.lookup p index)
      (ConcreteSG.concreteBishopSGFaceFlux
        (V.lookup row index))
  lookupScale V.[] V.[] ()
  lookupScale (V._∷_ p ps) (V._∷_ face rest) F.zero = refl
  lookupScale (V._∷_ p ps) (V._∷_ face rest) (F.suc index) =
    lookupScale ps rest index

originalConcrete54x29SGTransportConserves :
  (prefactors : V.Vec R.ℝ 29)
  (faces : originalConcreteSGFaces)
  (sourceWeights : V.Vec (V.Vec Q.ℚᵘ 29) 6)
  (axis : F.Fin 6) →
  R._≃_
    (pairedBishopSGNative
      (V.map Embed.embed (V.lookup sourceWeights axis))
      (originalConcreteSGFluxes prefactors faces))
    R.0ℝ
originalConcrete54x29SGTransportConserves
  prefactors faces weights axis =
  pairedBishopSGNativeZero
    (V.map Embed.embed (V.lookup weights axis))
    (originalConcreteSGFluxes prefactors faces)

------------------------------------------------------------------------
-- ACTUAL zero-drop quadratic-energy dissipation (no logarithm).
-- This follows from the concrete Bishop square nonnegativity theorem.
-- For a blocking internal two-cell diffusion edge with inward/outward
-- sign correctly oriented, the instantaneous quadratic-energy power
-- is -k(cL-cR)^2. This proves a real nonnegative dissipation
-- magnitude for k>=0, without claiming the full SG entropy law.
------------------------------------------------------------------------

import DASHI.Foundations.BishopSquareNonnegativeExact as BishopSquare

zeroDropQuadraticDissipation :
  (rateScale left right : R.ℝ) → R.ℝ
zeroDropQuadraticDissipation rateScale left right =
  R._*_
    rateScale
    (R._*_
      (R._-_ left right)
      (R._-_ left right))

zeroDropQuadraticPower :
  (rateScale left right : R.ℝ) → R.ℝ
zeroDropQuadraticPower rateScale left right =
  R._*_
    (zeroDropMolarFaceRate rateScale left right)
    (R._-_ right left)

zeroDropPowerIsMinusQuadraticDissipation :
  (rateScale left right : R.ℝ) →
  R._≃_
    (zeroDropQuadraticPower rateScale left right)
    (R.- (zeroDropQuadraticDissipation rateScale left right))
zeroDropPowerIsMinusQuadraticDissipation rateScale left right =
  let open RP.ℝ-Solver
  in solve 3
    (λ k l r →
      ((k ⊗ (l ⊖ r)) ⊗ (r ⊖ l))
      ⊜ (⊝ (k ⊗ ((l ⊖ r) ⊗ (l ⊖ r)))))
    RP.≃-refl rateScale left right

zeroDropQuadraticDissipationNonnegative :
  (rateScale left right : R.ℝ) →
  R.NonNegative rateScale →
  R.NonNegative
    (zeroDropQuadraticDissipation rateScale left right)
zeroDropQuadraticDissipationNonnegative
  rateScale left right nonnegativeRate =
  RP.nonNegx,y⇒nonNegx*y
    nonnegativeRate
    (BishopSquare.bishopSquareNonnegative
      (R._-_ left right))

zeroDropEqualPopulationsHaveZeroQuadraticPower :
  (rateScale population : R.ℝ) →
  R._≃_
    (zeroDropQuadraticPower rateScale population population)
    R.0ℝ
zeroDropEqualPopulationsHaveZeroQuadraticPower rateScale population =
  let open RP.ℝ-Solver
  in solve 2
    (λ k p → ((k ⊗ (p ⊖ p)) ⊗ (p ⊖ p))
      ⊜ Κ Q.0ℚᵘ)
    RP.≃-refl rateScale population
