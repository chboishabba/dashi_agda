module DASHI.Moonshine.Monster3BCyclotomicNormSeparationExact where

------------------------------------------------------------------------
-- POSITIVE-DEFINITE SEPARATION FOR Q(zeta_3)
--
-- For x = u + v zeta, the existing exact cyclotomic carrier has
--
--   N(x) = u^2 - uv + v^2.
--
-- The identity
--
--   4 N(x) = (2u-v)^2 + 3v^2
--
-- turns N(x)=0 into a sum of nonnegative rational squares.  The repository's
-- generic exact-rational positivity machinery then forces both coordinates to
-- vanish.  This closes the algebraic bridge required to turn ordinary
-- nonzeroness of a cyclotomic value into the norm-qualified witness consumed
-- by Monster3BCyclotomicNonzeroInverseExact.
--
-- The proof helpers are cross-pollinated from the rational finite-L2 lane.
-- Their reuse transfers proof, not physical interpretation or source authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; NonZero; ≢-nonZero)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst; sym; trans)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicNonzeroInverseExact as Inv
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as RationalSeparation

------------------------------------------------------------------------
-- 1. Attribution / provenance.
------------------------------------------------------------------------

washington : Attribution.AttributedSource
washington = Attribution.mkDOISource
  "Lawrence C. Washington"
  "Introduction to Cyclotomic Fields, Second Edition"
  "Graduate Texts in Mathematics 83, Springer"
  "1997"
  "10.1007/978-1-4612-1934-7"
  "https://doi.org/10.1007/978-1-4612-1934-7"
  Attribution.academicBookSource
  "source context for the exact cyclotomic field and norm; the coordinate positive-definiteness proof below is repository-formalised and is not imported merely by citation"
  Attribution.publicAttribution

washingtonAttribution = Snowball.canonicalSourceRoleSnowballReceipt washington

------------------------------------------------------------------------
-- 2. Coordinate identity and positivity.
------------------------------------------------------------------------

scaledNormIdentity :
  (u v : ℚ) →
  RationalL2.square (2 * u - v) +
    (RationalL2.square v + RationalL2.square v + RationalL2.square v)
  ≡ 4 * C3.norm (C3.cyclotomic3 u v)
scaledNormIdentity u v = solve (u ∷ v ∷ [])

threeSquaresNonnegative :
  (v : ℚ) →
  0ℚ ≤ RationalL2.square v +
    RationalL2.square v + RationalL2.square v
threeSquaresNonnegative v =
  RationalL2.addNonnegative
    (RationalL2.addNonnegative
      (RationalL2.squareNonnegative v)
      (RationalL2.squareNonnegative v))
    (RationalL2.squareNonnegative v)

------------------------------------------------------------------------
-- 3. Norm zero separates the two rational coordinates.
------------------------------------------------------------------------

normZeroImpliesZero :
  (value : C3.Cyclotomic3) →
  C3.norm value ≡ 0ℚ →
  value ≡ C3.zero
normZeroImpliesZero (C3.cyclotomic3 u v) normZero =
  let
    left = RationalL2.square (2 * u - v)
    right = RationalL2.square v + RationalL2.square v + RationalL2.square v

    sumZero : left + right ≡ 0ℚ
    sumZero =
      trans
        (scaledNormIdentity u v)
        (trans
          (cong (λ n → 4 * n) normZero)
          (solve []))

    components =
      RationalSeparation.nonnegativeAddZeroComponents
        (RationalL2.squareNonnegative (2 * u - v))
        (threeSquaresNonnegative v)
        sumZero

    linearSquareZero : RationalL2.square (2 * u - v) ≡ 0ℚ
    linearSquareZero = proj₁ components

    tripleSquareZero :
      RationalL2.square v + RationalL2.square v + RationalL2.square v ≡ 0ℚ
    tripleSquareZero = proj₂ components

    vSquareZero : RationalL2.square v ≡ 0ℚ
    vSquareZero =
      proj₁
        (RationalSeparation.nonnegativeAddZeroComponents
          (RationalL2.squareNonnegative v)
          (RationalL2.addNonnegative
            (RationalL2.squareNonnegative v)
            (RationalL2.squareNonnegative v))
          tripleSquareZero)

    vZero : v ≡ 0ℚ
    vZero = RationalSeparation.rationalSquareZeroImpliesZero v vSquareZero

    linearZero : 2 * u - v ≡ 0ℚ
    linearZero =
      RationalSeparation.rationalSquareZeroImpliesZero
        (2 * u - v) linearSquareZero

    twoUTimesZero : 2 * u ≡ 0ℚ
    twoUTimesZero =
      subst (λ rightCoordinate → 2 * u - rightCoordinate ≡ 0ℚ)
        (sym vZero) linearZero

    uZero : u ≡ 0ℚ
    uZero with ℚP.p*q≡0⇒p≡0∨q≡0 twoUTimesZero
    ... | inj₁ ()
    ... | inj₂ proof = proof
  in
  C3.cyclotomic3Ext uZero vZero

------------------------------------------------------------------------
-- 4. Contrapositive bridge to the existing norm-qualified inverse witness.
------------------------------------------------------------------------

nonzeroValueImpliesNormNonzero :
  (value : C3.Cyclotomic3) →
  value ≢ C3.zero →
  NonZero (C3.norm value)
nonzeroValueImpliesNormNonzero value valueNonzero =
  ℚ.≢-nonZero
    (λ normZero → valueNonzero (normZeroImpliesZero value normZero))

nonzeroAmplitudeFromValue :
  (value : C3.Cyclotomic3) →
  value ≢ C3.zero →
  Inv.NonzeroCyclotomicAmplitude
nonzeroAmplitudeFromValue value valueNonzero =
  Inv.nonzeroCyclotomicAmplitude
    value
    (nonzeroValueImpliesNormNonzero value valueNonzero)

------------------------------------------------------------------------
-- 5. WrongType / attribution firewalls.
------------------------------------------------------------------------

data CitationCreatesNormSeparation : Set where
data PhysicalNamespaceCreatesPhysicalMeaning : Set where
data CharacterNonzeroCreatesVectorCoordinate : Set where
data QidCreatesNormSeparation : Set where
data DeweyCreatesNormSeparation : Set where
data OeisCreatesNormSeparation : Set where

citationDoesNotCreateNormSeparation : CitationCreatesNormSeparation → ⊥
citationDoesNotCreateNormSeparation ()

proofReuseDoesNotCreatePhysicalMeaning : PhysicalNamespaceCreatesPhysicalMeaning → ⊥
proofReuseDoesNotCreatePhysicalMeaning ()

characterNonzeroDoesNotCreateVectorCoordinate : CharacterNonzeroCreatesVectorCoordinate → ⊥
characterNonzeroDoesNotCreateVectorCoordinate ()

qidDoesNotCreateNormSeparation : QidCreatesNormSeparation → ⊥
qidDoesNotCreateNormSeparation ()

deweyDoesNotCreateNormSeparation : DeweyCreatesNormSeparation → ⊥
deweyDoesNotCreateNormSeparation ()

oeisDoesNotCreateNormSeparation : OeisCreatesNormSeparation → ⊥
oeisDoesNotCreateNormSeparation ()

record CyclotomicNormExternalCoordinates : Set where
  constructor cyclotomic-norm-external-coordinates
  field
    exactBookQid : String
    algebraTopicDewey : String
    oeisCoordinate : String
    oeisHasNormAuthority : Bool
open CyclotomicNormExternalCoordinates public

canonicalCyclotomicNormExternalCoordinates : CyclotomicNormExternalCoordinates
canonicalCyclotomicNormExternalCoordinates =
  cyclotomic-norm-external-coordinates
    "unresolved rather than guessed for the exact Washington edition"
    "512.44"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no cyclotomic norm, positivity, inverse, coordinate, representation, action, or recognition authority"
    false

record CyclotomicNormSeparationBoundary : Set where
  constructor cyclotomic-norm-separation-boundary
  field
    scaledNormSumOfSquaresIdentityPaid : Bool
    rationalSquarePositivityReused : Bool
    normZeroImpliesValueZeroPaid : Bool
    nonzeroValueImpliesNormNonzeroPaid : Bool
    existingInverseWitnessConstructibleFromOrdinaryNonzero : Bool
    finiteX6NonzeroCoordinateSearchPaidHere : Bool
    actualMonsterZetaRecognitionPaidHere : Bool
open CyclotomicNormSeparationBoundary public

canonicalCyclotomicNormSeparationBoundary : CyclotomicNormSeparationBoundary
canonicalCyclotomicNormSeparationBoundary =
  cyclotomic-norm-separation-boundary
    true true true true true false false
