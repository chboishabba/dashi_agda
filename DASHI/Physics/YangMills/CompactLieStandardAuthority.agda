module DASHI.Physics.YangMills.CompactLieStandardAuthority where

open import Agda.Primitive using (Level)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieLinearAlgebra
open import DASHI.Physics.YangMills.CompactLieAnalyticPackage
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.SU2CompactLieAlgebraInstance

------------------------------------------------------------------------
-- Explicit external-theorem authority.
--
-- Finite-dimensional compact Lie groups possess invariant metrics, local
-- exponential charts, BCH estimates, normalized Haar measure, and Peter--Weyl
-- theory.  DASHI does not silently identify those standard theorems with a
-- locally checked construction: imported witnesses live in this one file and
-- carry `standardImported` status.
------------------------------------------------------------------------

postulate
  standardAnalysisForCompactSimple :
    ∀ {g a : Level} {G : Set g} {𝔤 : Set a} →
    (K : CompactSimpleLieGroup G 𝔤) →
    (R : RealLieAlgebra 𝔤 (algebra K)) →
    StandardCompactLieAnalysis (group K) (algebra K) R

  su2StandardCompactAnalysis :
    StandardCompactLieAnalysis
      su2GenericGroup
      su2GenericLieAlgebra
      su2RealLieAlgebra

standardAuthorityLevel : ProofLevel
standardAuthorityLevel = standardImported
