module DASHI.Physics.Closure.NSTriadKNLuoYuResidualBasisComparisonExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- Author: Runlong Yu.
-- Title: "Critical Ledgers and Scale-Defect Cascades for Navier-Stokes".
-- DOI: 10.48550/arXiv.2606.13887.
--
-- Author: Runlong Yu.
-- Title: "Invisible Defect Cascades for Navier-Stokes Regularity".
-- DOI: 10.48550/arXiv.2606.12756.
--
-- DASHI CONTRIBUTION
--
-- Yu's filtered-vorticity balance has the three explicit positive residual
-- classes
--
--   far-field strain, increment/commutator defect, localization.
--
-- DASHI's broader critical ledger has seven names
--
--   collar, tail, pressure, low, phase, passive, fragmentation.
--
-- These bases are not definitionally identical.  In particular pressure is
-- absent from the curl equation but remains present in local-energy/CKN
-- formulations.  This module permits a candidate regrouping only through
-- explicit equalities supplied by the physical derivation and then proves
--
--   sevenTotal = yuFilteredTotal + pressure.
--
-- No paper title or linguistic similarity is allowed to identify the bases.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLuoResidualSourceLedgerExact as Seven

record YuFilteredResidualCell : Set where
  constructor yuFilteredResidualCell
  field
    farFieldStrain incrementCommutator localization : ℚ

open YuFilteredResidualCell public

yuFilteredTotal : YuFilteredResidualCell → ℚ
yuFilteredTotal cell =
  farFieldStrain cell
  + incrementCommutator cell
  + localization cell

record ExplicitResidualRegrouping : Set where
  constructor explicitResidualRegrouping
  field
    sevenCell : Seven.ResidualCell
    yuCell : YuFilteredResidualCell

    farFieldIdentification :
      farFieldStrain yuCell
      ≡ Seven.tail sevenCell + Seven.low sevenCell

    incrementIdentification :
      incrementCommutator yuCell
      ≡ Seven.phase sevenCell
        + Seven.passive sevenCell
        + Seven.fragmentation sevenCell

    localizationIdentification :
      localization yuCell ≡ Seven.collar sevenCell

open ExplicitResidualRegrouping public

sevenEqualsYuPlusPressure :
  ∀ regrouping →
  Seven.totalResidual (sevenCell regrouping)
  ≡
  yuFilteredTotal (yuCell regrouping)
  + Seven.pressure (sevenCell regrouping)
sevenEqualsYuPlusPressure regrouping
  rewrite farFieldIdentification regrouping
        | incrementIdentification regrouping
        | localizationIdentification regrouping =
  solve
    ( Seven.collar (sevenCell regrouping)
    ∷ Seven.tail (sevenCell regrouping)
    ∷ Seven.pressure (sevenCell regrouping)
    ∷ Seven.low (sevenCell regrouping)
    ∷ Seven.phase (sevenCell regrouping)
    ∷ Seven.passive (sevenCell regrouping)
    ∷ Seven.fragmentation (sevenCell regrouping)
    ∷ [])

record PressureFreeFilteredSpecialization
    (regrouping : ExplicitResidualRegrouping) : Set where
  constructor pressureFreeFilteredSpecialization
  field
    pressureVanishes : Seven.pressure (sevenCell regrouping) ≡ 0

open PressureFreeFilteredSpecialization public

pressureFreeSevenEqualsYu :
  ∀ {regrouping} →
  PressureFreeFilteredSpecialization regrouping →
  Seven.totalResidual (sevenCell regrouping)
  ≡ yuFilteredTotal (yuCell regrouping)
pressureFreeSevenEqualsYu {regrouping} specialization
  rewrite sevenEqualsYuPlusPressure regrouping
        | pressureVanishes specialization =
  solve (yuFilteredTotal (yuCell regrouping) ∷ [])

record ResidualBasisAuthorityBoundary : Set where
  constructor residualBasisAuthorityBoundary
  field
    basesKeptDistinct : Set
    explicitRegroupingTheoremProved : Set
    pressureDifferenceExposed : Set
    physicalResidualIdentificationsProduced : Set
    pressureVanishesInLocalEnergyRoute : Set

canonicalResidualBasisAuthorityBoundary :
  ResidualBasisAuthorityBoundary
canonicalResidualBasisAuthorityBoundary =
  residualBasisAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
