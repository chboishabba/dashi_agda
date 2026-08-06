module DASHI.Physics.Closure.NSTriadKNLuoTorusLerayContractiveExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Re-export the repository's literal rational Fourier-mode Leray theorem at
-- the torus/Galerkin boundary.  For a nonzero mode carrying
--
--   inverseNormSquared * |k|² = 1,
--
-- the exact multiplier is
--
--   P_k v = v - |k|^{-2}(k·v)k,
--
-- and its orthogonal decomposition proves
--
--   |P_k v|² <= |v|².
--
-- No new contractivity field is accepted from the caller.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as Leray

torusLerayMultiplierContractiveSquared :
  (projectionData : Leray.ProjectionMode) →
  (value : Leray.Vector3) →
  Leray.normSquared (Leray.project projectionData value)
  ≤ Leray.normSquared value
torusLerayMultiplierContractiveSquared =
  Leray.projectContractionSquared

torusLerayTransverse :
  (projectionData : Leray.ProjectionMode) →
  (value : Leray.Vector3) →
  Leray.dot
    (Leray.mode projectionData)
    (Leray.project projectionData value)
  ≡ 0ℚ
torusLerayTransverse = Leray.projectTransverse
