module DASHI.Foundations.FirstTitsAlbertE6F4ClassicalSourceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CLASSICAL ALBERT -> F4 / E6 GROUP-THEOREM DONOR
--
-- Primary modern ring-level source:
--   Seidon Alsaody, "Albert algebras over rings and related torsors",
--   Canadian Journal of Mathematics 73(3) (2021), 875-898,
--   published online 30 March 2020,
--   DOI 10.4153/S0008414X20000218.
--
-- The source proves/describes, for an Albert algebra A with cubic norm N:
--   Aut(A) is a semisimple algebraic group of type F4;
--   Isom(N) is semisimple simply connected of type E6;
--   Aut(A) is the stabilizer of the identity inside the norm-isometry group.
--
-- Related modern source over Z/rings:
--   Garibaldi--Petersson--Racine, "Albert algebras over Z and other rings",
--   Forum of Mathematics, Sigma 11 (2023), which identifies the split
--   automorphism group scheme with the split Chevalley F4 group scheme and the
--   cubic-norm isometry group with simply connected E6.
--
-- DASHI's local first-Tits executable separately verifies that its literal
-- M3^3 product/cubic has the standard first-Tits normalization and recovers the
-- same E6/F4 Lie-root data.  This source owner contributes classification
-- authority only; it is not an Agda proof of the hypotheses for the local
-- carrier.
------------------------------------------------------------------------

record ClassicalAlbertGroupSourceReceipt : Set where
  constructor classical-albert-group-source-receipt
  field
    primaryAuthor : String
    primaryTitle : String
    primaryDOI : String
    primaryPublication : String
    automorphismGroupTypeF4SourcePaid : Bool
    normIsometryGroupTypeE6SourcePaid : Bool
    automorphismEqualsUnitStabilizerSourcePaid : Bool
    splitChevalleyGroupSchemeSourcePaid : Bool
    sourceTheoremIsAgdaKernelProof : Bool
    sourceTheoremCreatesPhysicalGaugeIdentification : Bool
    boundary : String
open ClassicalAlbertGroupSourceReceipt public

canonicalClassicalAlbertGroupSourceReceipt : ClassicalAlbertGroupSourceReceipt
canonicalClassicalAlbertGroupSourceReceipt =
  classical-albert-group-source-receipt
    "Seidon Alsaody"
    "Albert algebras over rings and related torsors"
    "10.4153/S0008414X20000218"
    "Canadian Journal of Mathematics 73(3), 875-898 (2021; online 2020)"
    true true true true
    false false
    "Classical algebraic-group classification pays the theorem that an Albert algebra has automorphism group of type F4 and cubic-norm isometry group of type E6, with Aut(A) the identity stabilizer. Applying it to the local first-Tits carrier still requires a same-object proof that the source-written product/cubic is the standard Albert construction; physical SM/DHR interpretation remains wholly separate."
