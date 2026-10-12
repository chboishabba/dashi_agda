module DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact where

------------------------------------------------------------------------
-- SOURCED CLASSICAL E6/F4 CLASSIFICATION TARGET FOR THE ACTUAL ALBERT MODULE
--
-- Precise modern source used by this formalisation lane:
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
--   simply-connected algebraic-group correspondence of type F4 (and the
--   analogous octonion/G2 correspondence).
--
-- Petersson also states in §2.9 that for finite-dimensional A, Der(A) is the
-- Lie algebra of the automorphism group scheme Aut(A), citing KMRT.
--
-- Additional classical reference:
-- * T. A. Springer and F. D. Veldkamp,
--   Octonions, Jordan Algebras and Exceptional Groups,
--   Springer Monographs in Mathematics, DOI 10.1007/978-3-662-12622-6.
--
-- DASHI attribution rule:
-- these are SOURCE RECEIPTS.  They do not become Agda kernel theorems merely
-- because the concrete RationalAlbert carrier and its exact split root datum
-- have now been constructed.  The remaining formal promotion must instantiate
-- the characteristic-zero/rational-form hypotheses on this precise carrier and
-- build the group/form classification object explicitly.
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
    peterssonDerivationTheoremLocated : Bool
    characteristicZeroAlbertDerivationTypeF4 : Bool
    characteristicZeroAlbertStructureAlgebraTypeE6 : Bool
    AlbertAutomorphismGroupTypeF4 : Bool
    finiteDimensionalDerivationIsLieAutGroupScheme : Bool
    rationalAlbertCarrierMatchesH3OctonionShape : Bool
    rationalAlbertJordanIdentitySourceWritten : Bool
    rationalAlbertInnerDerivationLawSourceWritten : Bool
    linearSameCarrierE6F4TargetTyped : Bool
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
    true true true true true
    true true true true
    false false false false
