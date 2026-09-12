module DASHI.Moonshine.Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact where

------------------------------------------------------------------------
-- ORDINARY NONZERO VECTOR -> SELECTED NONZERO X6 COORDINATE
--
-- The existing delta-extraction theorem expects a proof-bearing witness that
-- already names x : X6 and a norm-qualified nonzero value f(x).  This owner
-- removes that witness-interface debt for the finite Schrodinger model.
--
-- TernaryFiniteFunctionDeltaBasisExact already owns the exact equivalence
--
--   TritCube 6 <-> X6.
--
-- We recursively search the three branches neg/zer/pos at every ternary
-- depth.  At depth six this is the constructive 3^6 = 729 search, without a
-- flattened Fin 729 carrier or a hand-written enumeration.  If every branch is
-- zero then the function is pointwise zero; otherwise a concrete nonzero
-- coordinate is returned.  Monster3BCyclotomicNormSeparationExact upgrades
-- value != 0 to the norm-qualified inverse witness already consumed by delta
-- extraction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using (0ℚ)
import Data.Rational.Properties as ℚP
open ℚP using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicNormSeparationExact as NormSeparation
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact as Delta
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaOrbitTransitivityExact as Orbit
import DASHI.Moonshine.TernaryFiniteFunctionDeltaBasisExact as Basis

------------------------------------------------------------------------
-- 1. Decidable zero on the exact Q(zeta_3) coordinate pair.
------------------------------------------------------------------------

cyclotomicZero? : (value : C3.Cyclotomic3) → Dec (value ≡ C3.zero)
cyclotomicZero? (C3.cyclotomic3 u v) with u ≟ 0ℚ | v ≟ 0ℚ
... | yes refl | yes refl = yes refl
... | no uNonzero | _ =
  no (λ equality → uNonzero (cong C3.rationalCoeff equality))
... | yes _ | no vNonzero =
  no (λ equality → vNonzero (cong C3.zetaCoeff equality))

------------------------------------------------------------------------
-- 2. Generic constructive search over a ternary cube.
------------------------------------------------------------------------

data CubeSearchResult {n : Nat}
    (f : Basis.TritCube n → C3.Cyclotomic3) : Set where
  found :
    (point : Basis.TritCube n) →
    f point ≢ C3.zero →
    CubeSearchResult f
  allZero :
    ((point : Basis.TritCube n) → f point ≡ C3.zero) →
    CubeSearchResult f

searchTritCube :
  ∀ {n : Nat} →
  (f : Basis.TritCube n → C3.Cyclotomic3) →
  CubeSearchResult f
searchTritCube {zero} f with cyclotomicZero? (f Basis.cube0)
... | yes valueZero =
  allZero (λ { Basis.cube0 → valueZero })
... | no valueNonzero = found Basis.cube0 valueNonzero
searchTritCube {suc n} f
  with searchTritCube (λ tail → f (Basis.cubeS neg tail))
... | found tail valueNonzero =
  found (Basis.cubeS neg tail) valueNonzero
... | allZero negZero
  with searchTritCube (λ tail → f (Basis.cubeS zer tail))
... | found tail valueNonzero =
  found (Basis.cubeS zer tail) valueNonzero
... | allZero zerZero
  with searchTritCube (λ tail → f (Basis.cubeS pos tail))
... | found tail valueNonzero =
  found (Basis.cubeS pos tail) valueNonzero
... | allZero posZero =
  allZero λ where
    (Basis.cubeS neg tail) → negZero tail
    (Basis.cubeS zer tail) → zerZero tail
    (Basis.cubeS pos tail) → posZero tail

------------------------------------------------------------------------
-- 3. Ordinary mathematical nonzeroness for an invariant vector.
------------------------------------------------------------------------

record OrdinaryNonzeroInvariantVector
    {Member : V.SchrodingerFunction → Set}
    (inv : V.HeisenbergInvariantSubspace Member) : Set where
  constructor ordinary-nonzero-invariant-vector
  field
    vector : V.SchrodingerFunction
    vectorMember : Member vector
    vectorNotPointwiseZero :
      V.PointwiseEqual vector V.zeroFunction → ⊥
open OrdinaryNonzeroInvariantVector public

------------------------------------------------------------------------
-- 4. Compile ordinary nonzeroness to the existing selected-coordinate witness.
------------------------------------------------------------------------

upgradeOrdinaryNonzeroInvariantVector :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
  OrdinaryNonzeroInvariantVector inv →
  Delta.NonzeroInvariantVector inv
upgradeOrdinaryNonzeroInvariantVector inv witness
  with searchTritCube
    (λ point → vector witness (Basis.toX6 point))
... | found point valueNonzero =
  Delta.nonzero-invariant-vector
    (vector witness)
    (vectorMember witness)
    (Basis.toX6 point)
    (NormSeparation.nonzeroAmplitudeFromValue
      (vector witness (Basis.toX6 point))
      valueNonzero)
    refl
... | allZero everyCubeZero =
  ⊥-elim
    (vectorNotPointwiseZero witness
      (λ x →
        trans
          (sym (cong (vector witness) (Basis.toFromX6 x)))
          (everyCubeZero (Basis.fromX6 x))))

------------------------------------------------------------------------
-- 5. The previously conditional irreducibility theorem becomes ordinary.
------------------------------------------------------------------------

ordinaryNonzeroInvariantSubspaceIsWholeCarrier :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    (witness : OrdinaryNonzeroInvariantVector inv) →
    (f : V.SchrodingerFunction) →
    Member f
ordinaryNonzeroInvariantSubspaceIsWholeCarrier inv witness f =
  Basis.allDeltaLinesSpanEverySchrodingerFunction inv
    (Orbit.allBooleanDeltaLinesBelong inv
      (upgradeOrdinaryNonzeroInvariantVector inv witness))
    f

------------------------------------------------------------------------
-- 6. Attribution snowball and WrongType firewalls.
------------------------------------------------------------------------

terras : Attribution.AttributedSource
terras = Attribution.mkDOISource
  "Audrey Terras"
  "Fourier Analysis on Finite Groups and Applications"
  "Cambridge University Press"
  "1999"
  "10.1017/CBO9780511626265"
  "https://doi.org/10.1017/CBO9780511626265"
  Attribution.academicBookSource
  "finite Fourier/Heisenberg representation context; citation does not construct DASHI's recursive ternary search"
  Attribution.publicAttribution

terrasAttribution = Snowball.canonicalSourceRoleSnowballReceipt terras

data DimensionCreatesCoordinateWitness : Set where
data CharacterNonzeroCreatesCoordinateWitness : Set where
data CitationCreatesFiniteSearch : Set where
data QidCreatesCoordinateWitness : Set where
data DeweyCreatesCoordinateWitness : Set where
data OeisCreatesCoordinateWitness : Set where

dimensionDoesNotCreateCoordinateWitness : DimensionCreatesCoordinateWitness → ⊥
dimensionDoesNotCreateCoordinateWitness ()

characterNonzeroDoesNotCreateCoordinateWitness :
  CharacterNonzeroCreatesCoordinateWitness → ⊥
characterNonzeroDoesNotCreateCoordinateWitness ()

citationDoesNotCreateFiniteSearch : CitationCreatesFiniteSearch → ⊥
citationDoesNotCreateFiniteSearch ()

qidDoesNotCreateCoordinateWitness : QidCreatesCoordinateWitness → ⊥
qidDoesNotCreateCoordinateWitness ()

deweyDoesNotCreateCoordinateWitness : DeweyCreatesCoordinateWitness → ⊥
deweyDoesNotCreateCoordinateWitness ()

oeisDoesNotCreateCoordinateWitness : OeisCreatesCoordinateWitness → ⊥
oeisDoesNotCreateCoordinateWitness ()

record NonzeroWitnessExternalCoordinates : Set where
  constructor nonzero-witness-external-coordinates
  field
    finiteGroupQid : String
    groupRepresentationQid : String
    finiteGroupDewey : String
    groupRepresentationDewey : String
    oeisCoordinate : String
    oeisHasWitnessAuthority : Bool
open NonzeroWitnessExternalCoordinates public

canonicalNonzeroWitnessExternalCoordinates : NonzeroWitnessExternalCoordinates
canonicalNonzeroWitnessExternalCoordinates =
  nonzero-witness-external-coordinates
    "Q1057968"
    "Q1055807"
    "512.23"
    "512.22"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no finite-search, coordinate-witness, cyclotomic inverse, representation, action, or recognition authority"
    false

record NonzeroWitnessExtractionBoundary : Set where
  constructor nonzero-witness-extraction-boundary
  field
    decidableCyclotomicZeroConstructed : Bool
    recursiveTernaryCubeSearchConstructed : Bool
    cubeSixSearchIsFinite729Search : Bool
    ordinaryNonzeroUpgradedToSelectedCoordinate : Bool
    normQualifiedAmplitudeDerivedFromOrdinaryNonzero : Bool
    unconditionalFiniteSchrodingerIrreducibilityPaid : Bool
    fixedCentralCharacterUniquenessPaidHere : Bool
    actualMonster729IdentificationPaidHere : Bool
open NonzeroWitnessExtractionBoundary public

canonicalNonzeroWitnessExtractionBoundary : NonzeroWitnessExtractionBoundary
canonicalNonzeroWitnessExtractionBoundary =
  nonzero-witness-extraction-boundary
    true true true true true true false false
