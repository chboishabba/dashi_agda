module DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact where

------------------------------------------------------------------------
-- SOURCED CLASSICAL E6/F4 CLASSIFICATION TARGET FOR THE ACTUAL ALBERT MODULE
--
-- Primary sources used by this formalisation lane:
--
-- * C. Chevalley and R. D. Schafer (1950): for an Albert algebra in
--   characteristic zero, the derivation algebra is central simple of type F4.
--   A modern survey statement is Petersson, "Albert Algebras" §2.10.
--
-- * T. A. Springer and F. D. Veldkamp,
--   Octonions, Jordan Algebras and Exceptional Groups,
--   Springer Monographs in Mathematics, DOI 10.1007/978-3-662-12622-6.
--   Their exceptional-groups chapter identifies the automorphism group of an
--   Albert algebra as type F4 and the group preserving the cubic determinant
--   as type E6.
--
-- DASHI attribution rule:
-- these literature theorems are recorded as SOURCE RECEIPTS.  They do not
-- become Agda kernel theorems merely because the actual RationalAlbert carrier
-- has now been constructed.  The remaining formal promotion must instantiate
-- the hypotheses on this precise rational form and build the same-carrier
-- intertwiner/type recognition.
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
    springerVeldkampDOI : String
    peterssonDerivationTheoremLocated : Bool
    characteristicZeroAlbertDerivationTypeF4 : Bool
    AlbertAutomorphismGroupTypeF4 : Bool
    AlbertCubicDeterminantGroupTypeE6 : Bool
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
    "10.1007/978-3-662-12622-6"
    true true true true
    true true true true
    false false false false
