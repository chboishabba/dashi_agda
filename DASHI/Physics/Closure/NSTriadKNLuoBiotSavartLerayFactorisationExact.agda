module DASHI.Physics.Closure.NSTriadKNLuoBiotSavartLerayFactorisationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: R. Jason Parsley.
-- Title: "The Biot--Savart Operator and Electrodynamics on Subdomains of the
-- Three-Sphere".
-- Journal of Mathematical Physics 53 (2012), 013102.
-- DOI: 10.1063/1.3673788.
-- arXiv:0904.3524.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Record the exact fixed-mode factorisation behind the operator-theoretic
-- Biot--Savart viewpoint.  The Fourier Biot--Savart map ignores the
-- longitudinal part of its source and its range is already transverse:
--
--   B_k(P_k omega) = B_k omega,
--   P_k(B_k omega) = B_k omega.
--
-- Parsley proves boundedness and compact extension for a curved-domain
-- Biot--Savart operator.  This finite algebra is only the periodic fixed-mode
-- factorisation needed before any Hilbert-space compactness theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS

crossIgnoresLongitudinalProjection :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  BS.cross (V.mode modeData) (V.project modeData omega)
  ≡ BS.cross (V.mode modeData) omega
crossIgnoresLongitudinalProjection modeData omega
  with V.mode modeData | omega
... | V.v3 mx my mz | V.v3 wx wy wz =
  V.vectorExt
    (solve
      ( mx ∷ my ∷ mz
      ∷ wx ∷ wy ∷ wz
      ∷ V.inverseNormSquared modeData
      ∷ []))
    (solve
      ( mx ∷ my ∷ mz
      ∷ wx ∷ wy ∷ wz
      ∷ V.inverseNormSquared modeData
      ∷ []))
    (solve
      ( mx ∷ my ∷ mz
      ∷ wx ∷ wy ∷ wz
      ∷ V.inverseNormSquared modeData
      ∷ []))

biotSavartIgnoresLongitudinalSource :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  BS.biotSavart modeData (V.project modeData omega)
  ≡ BS.biotSavart modeData omega
biotSavartIgnoresLongitudinalSource modeData omega =
  cong
    (V.scale (V.inverseNormSquared modeData))
    (crossIgnoresLongitudinalProjection modeData omega)

biotSavartRangeAlreadyProjected :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.project modeData (BS.biotSavart modeData omega)
  ≡ BS.biotSavart modeData omega
biotSavartRangeAlreadyProjected modeData omega =
  V.projectFixesTransverse
    modeData
    (BS.biotSavart modeData omega)
    (BS.biotSavartTransverse modeData omega)

biotSavartLerayFactorisation :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.project modeData
    (BS.biotSavart modeData (V.project modeData omega))
  ≡ BS.biotSavart modeData omega
biotSavartLerayFactorisation modeData omega =
  trans
    (cong
      (V.project modeData)
      (biotSavartIgnoresLongitudinalSource modeData omega))
    (biotSavartRangeAlreadyProjected modeData omega)
