module DASHI.Wikimedia.IbrahimE7FiftySixAnd128TypedOEISSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional

------------------------------------------------------------------------
-- TYPED OEIS FOLLOW-UP FOR TWO PREVIOUSLY UNRESOLVED SEEDS
--
-- 56:
--   DASHI already owns the Freudenthal carrier shape
--      56 = 1 + 1 + 27 + 27.
--   OEIS A121736 independently lists irreducible E7 representation dimensions
--      1, 56, 133, ...
--   and identifies 56 as the smallest faithful/minuscule representation.
--   This upgrades 56 from an unresolved OEIS leaf to a direct exceptional
--   representation-dimension coordinate, without identifying the DASHI
--   Freudenthal carrier with that E7 module absent a same-action recognition.
--
-- 128:
--   OEIS A000079 pays only the exact power-of-two role 128 = 2^7.
--   DASHI has several unrelated 128 carriers (finite-field Fourier/NTT block,
--   shell-orbit cardinality, sprint labels, etc.).  The numeric-family receipt
--   therefore remains multi-role and does not import Spin/Clifford semantics.
------------------------------------------------------------------------

fiftySixAsFreudenthal : Nat
fiftySixAsFreudenthal = Exceptional.freudenthalDimension

fiftySixValue : fiftySixAsFreudenthal ≡ 56
fiftySixValue = refl

oneTwentyEight : Nat
oneTwentyEight = 128

record E7FiftySixCoordinate : Set where
  constructor e7-fifty-six-coordinate
  field
    value : Nat
    e7Qid : String
    oeisId : String
    oeisRole : String
    directRepresentationDimensionRole : Bool
    sameActionRecognitionPaid : Bool
open E7FiftySixCoordinate public

canonicalE7FiftySixCoordinate : E7FiftySixCoordinate
canonicalE7FiftySixCoordinate = e7-fifty-six-coordinate
  56 "Q3045793" "A121736"
  "dimensions of irreducible complex E7 representations; 56 is the smallest faithful/minuscule representation dimension"
  true false

record OneTwentyEightCoordinate : Set where
  constructor one-twenty-eight-coordinate
  field
    value : Nat
    oeisId : String
    oeisRole : String
    exactPowerOfTwoRole : Bool
    spinOrCliffordRolePaidByThisOEIS : Bool
    sameCarrierAcrossRepo128Uses : Bool
open OneTwentyEightCoordinate public

canonicalOneTwentyEightCoordinate : OneTwentyEightCoordinate
canonicalOneTwentyEightCoordinate = one-twenty-eight-coordinate
  128 "A000079" "powers of 2; 128 = 2^7" true false false

------------------------------------------------------------------------
-- Primary/reference provenance for the Lie-representation interpretation.
------------------------------------------------------------------------

humphreysSource : Attribution.AttributedSource
humphreysSource = Attribution.mkDOISource
  "James E. Humphreys"
  "Introduction to Lie Algebras and Representation Theory"
  "Graduate Texts in Mathematics 9, Springer"
  "1972"
  "10.1007/978-1-4612-6398-2"
  "https://doi.org/10.1007/978-1-4612-6398-2"
  Attribution.academicBookSource
  "semisimple Lie-algebra/root-system/representation-theory provenance; OEIS A121736 supplies the enumerated E7 dimension coordinate"
  Attribution.publicAttribution

humphreysAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt humphreysSource

------------------------------------------------------------------------
-- BIDI / WrongType firewalls.
------------------------------------------------------------------------

data Same56CreatesE7FreudenthalIntertwiner : Set where
data Same128CreatesSpinRepresentation : Set where
data Same128CreatesSameRepoCarrier : Set where

same56DoesNotCreateE7Intertwiner : Same56CreatesE7FreudenthalIntertwiner → ⊥
same56DoesNotCreateE7Intertwiner ()

powerOfTwo128DoesNotCreateSpin : Same128CreatesSpinRepresentation → ⊥
powerOfTwo128DoesNotCreateSpin ()

same128DoesNotIdentifyRepoCarriers : Same128CreatesSameRepoCarrier → ⊥
same128DoesNotIdentifyRepoCarriers ()

record FiftySixOneTwentyEightFrontier : Set where
  constructor fifty-six-one-twenty-eight-frontier
  field
    freudenthal56RepoCarrierPaid : Bool
    e7A121736Direct56RolePaid : Bool
    e7QidPaid : Bool
    humphreysSourcePaid : Bool
    actualFreudenthal56ToE7SameActionRecognitionPaid : Bool
    powerOfTwo128A000079Paid : Bool
    spinClifford128InterpretationPaid : Bool
    repo128UsesIdentifiedAsOneCarrier : Bool
    nextResidual : String
open FiftySixOneTwentyEightFrontier public

currentFiftySixOneTwentyEightFrontier : FiftySixOneTwentyEightFrontier
currentFiftySixOneTwentyEightFrontier = fifty-six-one-twenty-eight-frontier
  true true true true false true false false
  "upgrade the typed audit row for 56 to A121736/E7 direct support; keep 128 at exact A000079 power-of-two strength until a specific repo 128 carrier is selected and a matching Spin/Clifford or finite-field sequence/source is paid. Do not collapse the existing NTT, orbit, and other 128 uses by numeral alone."
