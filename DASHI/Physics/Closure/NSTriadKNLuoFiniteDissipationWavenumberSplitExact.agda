module DASHI.Physics.Closure.NSTriadKNLuoFiniteDissipationWavenumberSplitExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
-- arXiv DOI: 10.48550/arXiv.1102.1944.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- This module implements the exact finite algebra of a time-dependent
-- dissipation-wavenumber split.  Every scale is classified either as
--
--   low:  transfer <= explicit low-mode reservoir,
--   high: transfer <= eta * viscous diffusion.
--
-- The classification is carried by a typed certificate, so a scale cannot be
-- counted in both lanes or silently omitted.  Recursive summation proves
--
--   total transfer
--     <= eta * total high diffusion + total low reservoir.
--
-- This is the appropriate established precedent for a dynamic good/bad scale
-- split.  It does not prove that Navier-Stokes supplies the high-mode
-- certificate with a universal eta < 1, nor that the low reservoir is
-- critically integrable.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

data DissipationRegime : Set where
  lowMode viscousHighMode : DissipationRegime

data RegimeCertificate
    (eta transfer diffusion reservoir : ℚ) :
    DissipationRegime → Set where
  lowCertificate :
    transfer ≤ reservoir →
    RegimeCertificate eta transfer diffusion reservoir lowMode
  highCertificate :
    transfer ≤ eta * diffusion →
    RegimeCertificate eta transfer diffusion reservoir viscousHighMode

record DissipationRangeCell (eta : ℚ) : Set where
  constructor dissipationRangeCell
  field
    transfer diffusion lowReservoir : ℚ
    regime : DissipationRegime
    certificate :
      RegimeCertificate eta transfer diffusion lowReservoir regime

open DissipationRangeCell public

highDiffusion :
  ∀ {eta} → DissipationRangeCell eta → ℚ
highDiffusion cell with regime cell
... | lowMode = 0ℚ
... | viscousHighMode = diffusion cell

selectedLowReservoir :
  ∀ {eta} → DissipationRangeCell eta → ℚ
selectedLowReservoir cell with regime cell
... | lowMode = lowReservoir cell
... | viscousHighMode = 0ℚ

localDissipationRangeBound :
  ∀ {eta} (cell : DissipationRangeCell eta) →
  transfer cell
  ≤ eta * highDiffusion cell + selectedLowReservoir cell
localDissipationRangeBound {eta} cell with regime cell | certificate cell
... | lowMode | lowCertificate lowBound =
  subst
    (λ upper → transfer cell ≤ upper)
    (solve (eta ∷ lowReservoir cell ∷ []))
    lowBound
... | viscousHighMode | highCertificate highBound =
  subst
    (λ upper → transfer cell ≤ upper)
    (solve (eta ∷ diffusion cell ∷ []))
    highBound

sumTransfer :
  ∀ {eta} → List (DissipationRangeCell eta) → ℚ
sumTransfer [] = 0ℚ
sumTransfer (cell ∷ cells) = transfer cell + sumTransfer cells

sumHighDiffusion :
  ∀ {eta} → List (DissipationRangeCell eta) → ℚ
sumHighDiffusion [] = 0ℚ
sumHighDiffusion (cell ∷ cells) =
  highDiffusion cell + sumHighDiffusion cells

sumLowReservoir :
  ∀ {eta} → List (DissipationRangeCell eta) → ℚ
sumLowReservoir [] = 0ℚ
sumLowReservoir (cell ∷ cells) =
  selectedLowReservoir cell + sumLowReservoir cells

finiteDissipationWavenumberSplit :
  ∀ {eta} (cells : List (DissipationRangeCell eta)) →
  sumTransfer cells
  ≤ eta * sumHighDiffusion cells + sumLowReservoir cells
finiteDissipationWavenumberSplit [] = ℚₚ.≤-refl
finiteDissipationWavenumberSplit {eta} (cell ∷ cells) =
  let
    summed =
      ℚₚ.+-mono-≤
        (localDissipationRangeBound cell)
        (finiteDissipationWavenumberSplit cells)

    rightMeaning :
      (eta * highDiffusion cell + selectedLowReservoir cell)
      + (eta * sumHighDiffusion cells + sumLowReservoir cells)
      ≡
      eta * (highDiffusion cell + sumHighDiffusion cells)
      + (selectedLowReservoir cell + sumLowReservoir cells)
    rightMeaning =
      solve
        ( eta
        ∷ highDiffusion cell
        ∷ selectedLowReservoir cell
        ∷ sumHighDiffusion cells
        ∷ sumLowReservoir cells
        ∷ [])
  in
  subst
    (λ upper → transfer cell + sumTransfer cells ≤ upper)
    rightMeaning
    summed

record DissipationRangeAuthorityBoundary : Set where
  constructor dissipationRangeAuthorityBoundary
  field
    exclusiveFiniteRegimeCarrierProved : Set
    finiteDynamicSplitSummationProved : Set
    navierStokesHighModeCertificateProduced : Set
    criticalLowReservoirIntegrabilityProved : Set
    universalStrictEtaProduced : Set

canonicalDissipationRangeAuthorityBoundary :
  DissipationRangeAuthorityBoundary
canonicalDissipationRangeAuthorityBoundary =
  dissipationRangeAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
