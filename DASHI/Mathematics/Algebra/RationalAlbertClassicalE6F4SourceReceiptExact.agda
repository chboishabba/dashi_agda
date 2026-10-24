module DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact where

------------------------------------------------------------------------
-- SOURCED E6/F4 CLASSIFICATION TARGET FOR THE ACTUAL RATIONAL ALBERT MODULE
--
-- Classical/field-level source:
--
-- * Holger P. Petersson, "A Survey on Albert Algebras" (2017).
--
--   Theorem 2.10 (citing Chevalley--Schafer [CS50]): if J is an Albert algebra
--   over a field F of characteristic zero, Der(J) is a central simple Lie
--   algebra of type F4 over F.
--
--   Theorem 2.12: the structure algebra str(J) is a central simple Lie algebra
--   of type E6 over F in characteristic zero.
--
--   Theorem 2.13: J |-> Aut(J) gives the Albert-algebra / absolutely-simple
--   simply-connected algebraic-group correspondence of type F4.
--
-- Modern ring-level source cross-pollinated from the first-Tits sibling lane:
--
-- * Seidon Alsaody, "Albert algebras over rings and related torsors",
--   Canadian Journal of Mathematics 73(3) (2021), 875--898,
--   DOI 10.4153/S0008414X20000218.
--
--   This gives the modern group-scheme classification surface used here:
--   Aut(A) is semisimple of type F4; the cubic-norm isometry group is
--   semisimple simply connected of type E6; and Aut(A) is the stabilizer of
--   the identity inside the norm-isometry group.
--
-- * Garibaldi--Petersson--Racine, "Albert algebras over Z and other rings",
--   Forum of Mathematics, Sigma 11 (2023), supplies the complementary split
--   group-scheme identification over rings.
--
-- Additional classical reference:
-- * T. A. Springer and F. D. Veldkamp,
--   Octonions, Jordan Algebras and Exceptional Groups,
--   Springer Monographs in Mathematics, DOI 10.1007/978-3-662-12622-6.
--
-- DASHI attribution rule:
-- these are SOURCE RECEIPTS. They do not become Agda kernel theorems merely
-- because the concrete RationalAlbert carrier, Jordan product/cubic and exact
-- root data have been constructed.  The remaining formal promotion is no
-- longer a source-discovery problem: it is the proof-relevant instantiation of
-- the Albert/group-scheme classification theorem on this precise original-Q
-- object (including its form), with no physical gauge interpretation inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact as InnerLaw
import DASHI.Mathematics.Algebra.RationalAlbertLinearExceptionalGroupsExact as Linear

record ClassicalExceptionalSourceReceipt : Set where
  constructor classical-exceptional-source-receipt
  field
    peterssonSurveyTitle : String
    peterssonDerivationTheoremNumber : String
    peterssonStructureAlgebraTheoremNumber : String
    peterssonAutomorphismGroupTheoremNumber : String
    springerVeldkampDOI : String

    alsaodyTitle : String
    alsaodyDOI : String
    garibaldiPeterssonRacineTitle : String

    peterssonDerivationTheoremLocated : Bool
    characteristicZeroAlbertDerivationTypeF4 : Bool
    characteristicZeroAlbertStructureAlgebraTypeE6 : Bool
    AlbertAutomorphismGroupTypeF4 : Bool
    finiteDimensionalDerivationIsLieAutGroupScheme : Bool

    modernRingLevelAlbertClassificationLocated : Bool
    modernRingLevelAutTypeF4Located : Bool
    modernRingLevelNormIsometryTypeE6Located : Bool
    modernRingLevelAutEqualsUnitStabilizerLocated : Bool
    splitGroupSchemeOverRingsSourceLocated : Bool

    rationalAlbertCarrierMatchesH3OctonionShape : Bool
    rationalAlbertJordanIdentitySourceWritten : Bool
    rationalAlbertInnerDerivationLawSourceWritten : Bool
    linearSameCarrierE6F4TargetTyped : Bool

    remainingClassificationIsSourceDiscovery : Bool
    AgdaClassificationInstantiationPaid : Bool
    AgdaAutJEqualsF4Paid : Bool
    AgdaCubicGroupEqualsE6Paid : Bool
    AgdaF4EqualsE6UnitStabilizerPaid : Bool
open ClassicalExceptionalSourceReceipt public

canonicalClassicalExceptionalSourceReceipt : ClassicalExceptionalSourceReceipt
canonicalClassicalExceptionalSourceReceipt =
  classical-exceptional-source-receipt
    "A Survey on Albert Algebras (Holger P. Petersson, 2017)"
    "Theorem 2.10"
    "Theorem 2.12"
    "Theorem 2.13"
    "10.1007/978-3-662-12622-6"

    "Albert algebras over rings and related torsors"
    "10.4153/S0008414X20000218"
    "Albert algebras over Z and other rings"

    true true true true true
    true true true true true
    true true true true
    false
    false false false false
