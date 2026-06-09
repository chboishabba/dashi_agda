module DASHI.Physics.Closure.ExtremalFrobeniusOrbitSummaryPrimeInjectivity where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality.Core using (cong)

open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (MdlLevelCoarseObservable; π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibreFields as SCMCFF
  using (primeField)
open import DASHI.Physics.Closure.ShiftContractMdlLevelP2PrimeBridge as SCMCP
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (shiftContractStateTransportedPrimeEmbedding)
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using
    ( TriadicIndex
    ; i0
    ; i1
    ; i2
    ; triadicGen
    ; triadic-π-mdl-max-constant
    )
import DASHI.Physics.Closure.ExtremalFrobeniusTriadicInjection as TriadicInjection
open import Ontology.GodelLattice as GL using (FactorVec)

------------------------------------------------------------------------
-- P2 orbit-summary injectivity attempt on the canonical triadic subfamily.
--
-- The target is:
--   orbitSummaryAtP2 equality ⇒ transported-prime-image equality.
-- Forward direction is already inhabited in the bridge module; this file
-- documents and checks the constrained reverse direction on the three canonical
-- triadic generators.

triadicPrimeImage = TriadicInjection.triadicPrimeImage
triadicOrbitSummaryAtP2 = TriadicInjection.triadicOrbitSummaryAtP2

record P2OrbitSummaryFieldCollapse
  (i j : TriadicIndex) (h : triadicOrbitSummaryAtP2 i ≡ triadicOrbitSummaryAtP2 j) :
  Set where
  field
    collapsedForcedStable :
      FOS.DefectOrbitSummary.forcedStableCount (triadicOrbitSummaryAtP2 i)
        ≡
      FOS.DefectOrbitSummary.forcedStableCount (triadicOrbitSummaryAtP2 j)

    collapsedMotifChange :
      FOS.DefectOrbitSummary.motifChangeCount (triadicOrbitSummaryAtP2 i)
        ≡
      FOS.DefectOrbitSummary.motifChangeCount (triadicOrbitSummaryAtP2 j)

    collapsedTotalDrift :
      FOS.DefectOrbitSummary.totalDrift (triadicOrbitSummaryAtP2 i)
        ≡
      FOS.DefectOrbitSummary.totalDrift (triadicOrbitSummaryAtP2 j)

    collapsedRepatterning :
      FOS.DefectOrbitSummary.repatterningCount (triadicOrbitSummaryAtP2 i)
        ≡
      FOS.DefectOrbitSummary.repatterningCount (triadicOrbitSummaryAtP2 j)

    collapsedContractive :
      FOS.DefectOrbitSummary.contractiveCount (triadicOrbitSummaryAtP2 i)
        ≡
      FOS.DefectOrbitSummary.contractiveCount (triadicOrbitSummaryAtP2 j)

    collapsedExpansive :
      FOS.DefectOrbitSummary.expansiveCount (triadicOrbitSummaryAtP2 i)
        ≡
      FOS.DefectOrbitSummary.expansiveCount (triadicOrbitSummaryAtP2 j)

-- This is the typed blocker for the missing inverse direction.
data MissingOrbitSummaryToPrimeInjectivity : Set where
  missingP2OrbitSummaryToPrimeInjectivity :
    ∀ i j →
    (h : triadicOrbitSummaryAtP2 i ≡ triadicOrbitSummaryAtP2 j) →
    P2OrbitSummaryFieldCollapse i j h →
    MissingOrbitSummaryToPrimeInjectivity

p2OrbitSummaryFieldCollapse :
  ∀ i j →
  (h : triadicOrbitSummaryAtP2 i ≡ triadicOrbitSummaryAtP2 j) →
  P2OrbitSummaryFieldCollapse i j h
p2OrbitSummaryFieldCollapse i j h =
  record
    { collapsedForcedStable = cong FOS.DefectOrbitSummary.forcedStableCount h
    ; collapsedMotifChange = cong FOS.DefectOrbitSummary.motifChangeCount h
    ; collapsedTotalDrift = cong FOS.DefectOrbitSummary.totalDrift h
    ; collapsedRepatterning = cong FOS.DefectOrbitSummary.repatterningCount h
    ; collapsedContractive = cong FOS.DefectOrbitSummary.contractiveCount h
    ; collapsedExpansive = cong FOS.DefectOrbitSummary.expansiveCount h
    }

-- Strongest finite triadic result now obtainable:
-- - if the indices are the same, transport primes are definitionally equal;
-- - for off-diagonal cases, orbit-summary equality can only be recorded as the
--   explicit blocker above (no constructive inverse route is available).
triadicOrbitSummaryAtP2-to-primeImage :
  ∀ i j →
  triadicOrbitSummaryAtP2 i ≡ triadicOrbitSummaryAtP2 j →
  (triadicPrimeImage i ≡ triadicPrimeImage j) ⊎ MissingOrbitSummaryToPrimeInjectivity
triadicOrbitSummaryAtP2-to-primeImage STF.i0 STF.i0 _ = inj₁ refl
triadicOrbitSummaryAtP2-to-primeImage STF.i0 STF.i1 h =
  inj₂ (missingP2OrbitSummaryToPrimeInjectivity STF.i0 STF.i1 h (p2OrbitSummaryFieldCollapse STF.i0 STF.i1 h))
triadicOrbitSummaryAtP2-to-primeImage STF.i0 STF.i2 h =
  inj₂ (missingP2OrbitSummaryToPrimeInjectivity STF.i0 STF.i2 h (p2OrbitSummaryFieldCollapse STF.i0 STF.i2 h))
triadicOrbitSummaryAtP2-to-primeImage STF.i1 STF.i0 h =
  inj₂ (missingP2OrbitSummaryToPrimeInjectivity STF.i1 STF.i0 h (p2OrbitSummaryFieldCollapse STF.i1 STF.i0 h))
triadicOrbitSummaryAtP2-to-primeImage STF.i1 STF.i1 _ = inj₁ refl
triadicOrbitSummaryAtP2-to-primeImage STF.i1 STF.i2 h =
  inj₂ (missingP2OrbitSummaryToPrimeInjectivity STF.i1 STF.i2 h (p2OrbitSummaryFieldCollapse STF.i1 STF.i2 h))
triadicOrbitSummaryAtP2-to-primeImage STF.i2 STF.i0 h =
  inj₂ (missingP2OrbitSummaryToPrimeInjectivity STF.i2 STF.i0 h (p2OrbitSummaryFieldCollapse STF.i2 STF.i0 h))
triadicOrbitSummaryAtP2-to-primeImage STF.i2 STF.i1 h =
  inj₂ (missingP2OrbitSummaryToPrimeInjectivity STF.i2 STF.i1 h (p2OrbitSummaryFieldCollapse STF.i2 STF.i1 h))
triadicOrbitSummaryAtP2-to-primeImage STF.i2 STF.i2 _ = inj₁ refl

-- Canonical slice witness (for downstream composition checks).
canonicalTriadicOrbitSummaryInverseSurface :
  (∀ i j →
   triadicOrbitSummaryAtP2 i ≡ triadicOrbitSummaryAtP2 j →
   (triadicPrimeImage i ≡ triadicPrimeImage j) ⊎ MissingOrbitSummaryToPrimeInjectivity)
canonicalTriadicOrbitSummaryInverseSurface =
  triadicOrbitSummaryAtP2-to-primeImage
