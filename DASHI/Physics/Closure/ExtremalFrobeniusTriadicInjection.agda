module DASHI.Physics.Closure.ExtremalFrobeniusTriadicInjection where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Product using (_,_)

open import Ontology.GodelLattice as GL using (FactorVec)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS using (DefectOrbitSummary)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibre as SCMCF
  using (ShiftContractMdlLevelCoarseFibre)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibreFields as SCMCFF
  using (primeField)
open import DASHI.Physics.Closure.ShiftContractMdlLevelP2PrimeBridge as SCMCP
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState; shiftContractStateTransportedPrimeEmbedding)
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using
    ( TriadicIndex
    ; i0
    ; i1
    ; i2
    ; triadicGen
    ; triadic-π-mdl-max-constant
    ; primeImageDistinct01
    ; primeImageDistinct02
    ; primeImageDistinct12
    ; triadicPrimeImageDistinct
    )

------------------------------------------------------------------------
-- A minimal three-point prime-image injection slice.
--
-- This records exactly what is currently executable from canonical triadic
-- shift-contract data:
-- - a transported-prime image map on `{i0,i1,i2}`,
-- - strict pairwise inequalities for those three prime images,
-- - the induced orbit-summary-at-`p2` witnesses along the canonical carrier.
-- The injective converse from orbit-summary to prime-image equality is not yet
-- constructible from the available bridge theorem; that missing direction is
-- represented by a typed blocker field below.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

triadicCarrierFibre :
  ∀ i → SCMCF.ShiftContractMdlLevelCoarseFibre (π-mdl-max (triadicGen i0))
triadicCarrierFibre i =
  triadicGen i , sym (triadic-π-mdl-max-constant i0 i)

triadicPrimeImage :
  TriadicIndex → FactorVec
triadicPrimeImage i =
  shiftContractStateTransportedPrimeEmbedding (triadicGen i)

triadicOrbitSummaryAtP2 :
  ∀ i → FOS.DefectOrbitSummary
triadicOrbitSummaryAtP2 i =
  SCMCP.orbitSummaryAtP2 {q = π-mdl-max (triadicGen i0)} (triadicCarrierFibre i)

data MissingOrbitSummaryToPrimeInjectivity : Set where
  missingOrbitSummaryAtP2-to-primeImageInjectivity :
    MissingOrbitSummaryToPrimeInjectivity

record ExtremalFrobeniusTriadicInjection : Set₁ where
  field
    carrier :
      TriadicIndex → ShiftContractState

    primeImage :
      TriadicIndex → FactorVec

    sameSurface :
      ∀ i j →
      π-mdl-max (carrier i) ≡ π-mdl-max (carrier j)

    primeImage01 :
      primeImage i0 ≢ primeImage i1

    primeImage02 :
      primeImage i0 ≢ primeImage i2

    primeImage12 :
      primeImage i1 ≢ primeImage i2

    orbitSummaryWitness :
      ∀ i →
      FOS.DefectOrbitSummary

    orbitSummaryFromPrimeField :
      ∀ i j →
      primeField (triadicCarrierFibre i) ≡ primeField (triadicCarrierFibre j) →
      orbitSummaryWitness i ≡ orbitSummaryWitness j

    missingOrbitSummaryToPrimeInjectivity :
      MissingOrbitSummaryToPrimeInjectivity

canonicalExtremalFrobeniusTriadicInjection :
  ExtremalFrobeniusTriadicInjection
canonicalExtremalFrobeniusTriadicInjection =
  record
    { carrier = triadicGen
    ; primeImage = triadicPrimeImage
    ; sameSurface = triadic-π-mdl-max-constant
    ; primeImage01 = primeImageDistinct01
    ; primeImage02 = primeImageDistinct02
    ; primeImage12 = primeImageDistinct12
    ; orbitSummaryWitness = triadicOrbitSummaryAtP2
    ; orbitSummaryFromPrimeField = λ i j eq →
        SCMCP.orbitSummaryAtP2-from-primeField (triadicCarrierFibre i) (triadicCarrierFibre j) eq
    ; missingOrbitSummaryToPrimeInjectivity =
        missingOrbitSummaryAtP2-to-primeImageInjectivity
    }
