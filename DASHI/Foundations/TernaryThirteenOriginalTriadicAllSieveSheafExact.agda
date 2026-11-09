module DASHI.Foundations.TernaryThirteenOriginalTriadicAllSieveSheafExact where

------------------------------------------------------------------------
-- ALL-COVERING-SIEVE SHEAF DESCENT on the already existing
-- NON-DISCRETE relational Stage-12 Grothendieck topology.
--
-- Site.RelCover has two genuine cases: maximal sieve at any object,
-- and a sieve containing all three AB/BC/CA arrows at globalABC.
-- Pullback stability and transitivity are inherited from the
-- ORIGINAL RelationalStageTwelveGrothendieckExtensionExact owner.
--
-- This pays the all-cover existence/uniqueness theorem for the
-- CONSTRUCTED central-valuation Section presheaf, not semantic
-- identification with an independent relational/Monster/world model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Stage12
import DASHI.Foundations.TernaryThirteenOriginalTriadicPresheafExact as P
import DASHI.Foundations.TernaryThirteenOriginalTriadicSiteGluingExact as T

-- A matching family is genuinely indexed by every arrow of a sieve.
-- It is proof-independent and natural under restriction/compose.
record SieveMatching
  {U : Site.RelObj}
  (sieve : Stage12.Sieve Site.relationalPatchCategory U) : Set₁ where
  field
    value :
      {V : Site.RelObj} →
      (f : Site.RelHom V U) →
      Stage12.Sieve.contains sieve f →
      P.Section V

    proofIndependent :
      {V : Site.RelObj} →
      (f : Site.RelHom V U) →
      (p q : Stage12.Sieve.contains sieve f) →
      value f p ≡ value f q

    natural :
      {V W : Site.RelObj} →
      (f : Site.RelHom V U) →
      (p : Stage12.Sieve.contains sieve f) →
      (g : Site.RelHom W V) →
      P.restrictAlong g (value f p)
      ≡ value (Site.composeRel f g)
          (Stage12.Sieve.closed sieve f p g)

open SieveMatching public

-- The restriction of any global section gives a matching family,
-- for ALL source sieves, not just covering ones.
restrictToSieve :
  {U : Site.RelObj}
  (sieve : Stage12.Sieve Site.relationalPatchCategory U) →
  P.Section U → SieveMatching sieve
restrictToSieve sieve section = record
  { value = λ f p → P.restrictAlong f section
  ; proofIndependent = λ f p q → refl
  ; natural = λ f p g → sym (P.restrictComposition f g section)
  }

-- From arbitrary sieve membership of all three generators,
-- construct the exact overlap matches by naturality and proof
-- independence at the same original vertex arrow.
triadicMatchingFromSieve :
  (sieve : Stage12.Sieve Site.relationalPatchCategory Site.globalABC)
  (family : SieveMatching sieve)
  (hab : Stage12.Sieve.contains sieve Site.abToGlobal)
  (hbc : Stage12.Sieve.contains sieve Site.bcToGlobal)
  (hca : Stage12.Sieve.contains sieve Site.caToGlobal) →
  P.CoverTripleMatches
    (value family Site.abToGlobal hab)
    (value family Site.bcToGlobal hbc)
    (value family Site.caToGlobal hca)
triadicMatchingFromSieve sieve family hab hbc hca =
  P.cover-triple-matches agreeA agreeB agreeC
  where
    aAB = Stage12.Sieve.closed sieve Site.abToGlobal hab Site.aToAB
    aCA = Stage12.Sieve.closed sieve Site.caToGlobal hca Site.aToCA
    bAB = Stage12.Sieve.closed sieve Site.abToGlobal hab Site.bToAB
    bBC = Stage12.Sieve.closed sieve Site.bcToGlobal hbc Site.bToBC
    cBC = Stage12.Sieve.closed sieve Site.bcToGlobal hbc Site.cToBC
    cCA = Stage12.Sieve.closed sieve Site.caToGlobal hca Site.cToCA

    agreeA :
      P.restrictAlong Site.aToAB (value family Site.abToGlobal hab)
      ≡ P.restrictAlong Site.aToCA (value family Site.caToGlobal hca)
    agreeA =
      trans
        (natural family Site.abToGlobal hab Site.aToAB)
        (trans
          (proofIndependent family Site.aToGlobal aAB aCA)
          (sym (natural family Site.caToGlobal hca Site.aToCA)))

    agreeB :
      P.restrictAlong Site.bToAB (value family Site.abToGlobal hab)
      ≡ P.restrictAlong Site.bToBC (value family Site.bcToGlobal hbc)
    agreeB =
      trans
        (natural family Site.abToGlobal hab Site.bToAB)
        (trans
          (proofIndependent family Site.bToGlobal bAB bBC)
          (sym (natural family Site.bcToGlobal hbc Site.bToBC)))

    agreeC :
      P.restrictAlong Site.cToBC (value family Site.bcToGlobal hbc)
      ≡ P.restrictAlong Site.cToCA (value family Site.caToGlobal hca)
    agreeC =
      trans
        (natural family Site.bcToGlobal hbc Site.cToBC)
        (trans
          (proofIndependent family Site.cToGlobal cBC cCA)
          (sym (natural family Site.caToGlobal hca Site.cToCA)))

-- Every covering sieve of the already-proved source topology:
-- maximal case uses its identity arrow; triadic case uses the
-- genuine three-chart matching and glue.
glueSieve :
  {U : Site.RelObj}
  (sieve : Stage12.Sieve Site.relationalPatchCategory U)
  (cover : Site.RelCover sieve)
  (family : SieveMatching sieve) →
  P.Section U
glueSieve sieve (Site.maximalCover maximal) family =
  value family (Site.idR _) (maximal (Site.idR _))
glueSieve sieve (Site.triadicGlobalCover hab hbc hca) family =
  P.glueCoverTriple
    (value family Site.abToGlobal hab)
    (value family Site.bcToGlobal hbc)
    (value family Site.caToGlobal hca)
    (triadicMatchingFromSieve sieve family hab hbc hca)

-- A single proof-independent original arrow restriction can be
-- recovered after triadic gluing, by case analysis on all source
-- RelHom constructors.
triadicGlueRestrictsEveryMember :
  (sieve : Stage12.Sieve Site.relationalPatchCategory Site.globalABC)
  (family : SieveMatching sieve)
  (hab : Stage12.Sieve.contains sieve Site.abToGlobal)
  (hbc : Stage12.Sieve.contains sieve Site.bcToGlobal)
  (hca : Stage12.Sieve.contains sieve Site.caToGlobal)
  {V : Site.RelObj}
  (f : Site.RelHom V Site.globalABC)
  (pf : Stage12.Sieve.contains sieve f) →
  P.restrictAlong f
    (glueSieve sieve (Site.triadicGlobalCover hab hbc hca) family)
  ≡ value family f pf
triadicGlueRestrictsEveryMember sieve family hab hbc hca
  (Site.idR Site.globalABC) pf =
  sym (T.triadicGluingUnique ab bc ca matching candidate
    candidateAB candidateBC candidateCA)
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = P.coverTripleToTriadicMatching ab bc ca
      (triadicMatchingFromSieve sieve family hab hbc hca)
    candidate = value family (Site.idR Site.globalABC) pf

    candidateAB : T.restrictAB candidate ≡ ab
    candidateAB =
      trans
        (natural family (Site.idR Site.globalABC) pf Site.abToGlobal)
        (proofIndependent family Site.abToGlobal
          (Stage12.Sieve.closed sieve
            (Site.idR Site.globalABC) pf Site.abToGlobal) hab)

    candidateBC : T.restrictBC candidate ≡ bc
    candidateBC =
      trans
        (natural family (Site.idR Site.globalABC) pf Site.bcToGlobal)
        (proofIndependent family Site.bcToGlobal
          (Stage12.Sieve.closed sieve
            (Site.idR Site.globalABC) pf Site.bcToGlobal) hbc)

    candidateCA : T.restrictCA candidate ≡ ca
    candidateCA =
      trans
        (natural family (Site.idR Site.globalABC) pf Site.caToGlobal)
        (proofIndependent family Site.caToGlobal
          (Stage12.Sieve.closed sieve
            (Site.idR Site.globalABC) pf Site.caToGlobal) hca)

triadicGlueRestrictsEveryMember sieve family hab hbc hca
  Site.abToGlobal pf =
  trans
    (P.glueCoverTripleAB ab bc ca matching)
    (proofIndependent family Site.abToGlobal hab pf)
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = triadicMatchingFromSieve sieve family hab hbc hca

triadicGlueRestrictsEveryMember sieve family hab hbc hca
  Site.bcToGlobal pf =
  trans
    (P.glueCoverTripleBC ab bc ca matching)
    (proofIndependent family Site.bcToGlobal hbc pf)
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = triadicMatchingFromSieve sieve family hab hbc hca

triadicGlueRestrictsEveryMember sieve family hab hbc hca
  Site.caToGlobal pf =
  trans
    (P.glueCoverTripleCA ab bc ca matching)
    (proofIndependent family Site.caToGlobal hca pf)
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = triadicMatchingFromSieve sieve family hab hbc hca

triadicGlueRestrictsEveryMember sieve family hab hbc hca
  Site.aToGlobal pf =
  trans
    (cong (P.restrictAlong Site.aToAB)
      (P.glueCoverTripleAB ab bc ca matching))
    (trans
      (natural family Site.abToGlobal hab Site.aToAB)
      (proofIndependent family Site.aToGlobal
        (Stage12.Sieve.closed sieve Site.abToGlobal hab Site.aToAB)
        pf))
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = triadicMatchingFromSieve sieve family hab hbc hca

triadicGlueRestrictsEveryMember sieve family hab hbc hca
  Site.bToGlobal pf =
  trans
    (cong (P.restrictAlong Site.bToAB)
      (P.glueCoverTripleAB ab bc ca matching))
    (trans
      (natural family Site.abToGlobal hab Site.bToAB)
      (proofIndependent family Site.bToGlobal
        (Stage12.Sieve.closed sieve Site.abToGlobal hab Site.bToAB)
        pf))
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = triadicMatchingFromSieve sieve family hab hbc hca

triadicGlueRestrictsEveryMember sieve family hab hbc hca
  Site.cToGlobal pf =
  trans
    (cong (P.restrictAlong Site.cToBC)
      (P.glueCoverTripleBC ab bc ca matching))
    (trans
      (natural family Site.bcToGlobal hbc Site.cToBC)
      (proofIndependent family Site.cToGlobal
        (Stage12.Sieve.closed sieve Site.bcToGlobal hbc Site.cToBC)
        pf))
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = triadicMatchingFromSieve sieve family hab hbc hca

-- Every declared covering sieve, not only the three named
-- generators, gets a compatible glue with all its restrictions.
allCoverGlueRestricts :
  {U : Site.RelObj}
  (sieve : Stage12.Sieve Site.relationalPatchCategory U)
  (cover : Site.RelCover sieve)
  (family : SieveMatching sieve)
  {V : Site.RelObj}
  (f : Site.RelHom V U)
  (pf : Stage12.Sieve.contains sieve f) →
  P.restrictAlong f (glueSieve sieve cover family)
  ≡ value family f pf
allCoverGlueRestricts sieve (Site.maximalCover maximal)
  family f pf =
  trans
    (natural family (Site.idR _) (maximal (Site.idR _)) f)
    (proofIndependent family f
      (Stage12.Sieve.closed sieve (Site.idR _)
        (maximal (Site.idR _)) f)
      pf)
allCoverGlueRestricts sieve (Site.triadicGlobalCover hab hbc hca)
  family f pf =
  triadicGlueRestrictsEveryMember sieve family hab hbc hca f pf

-- Uniqueness: a competing global section with the same restrictions
-- is the one selected by the above constructive glue.
allCoverGlueUnique :
  {U : Site.RelObj}
  (sieve : Stage12.Sieve Site.relationalPatchCategory U)
  (cover : Site.RelCover sieve)
  (family : SieveMatching sieve)
  (candidate : P.Section U) →
  ({V : Site.RelObj}
    (f : Site.RelHom V U)
    (pf : Stage12.Sieve.contains sieve f) →
    P.restrictAlong f candidate ≡ value family f pf) →
  candidate ≡ glueSieve sieve cover family
allCoverGlueUnique sieve (Site.maximalCover maximal)
  family candidate paid =
  paid (Site.idR _) (maximal (Site.idR _))
allCoverGlueUnique sieve (Site.triadicGlobalCover hab hbc hca)
  family candidate paid =
  T.triadicGluingUnique ab bc ca matching candidate
    (paid Site.abToGlobal hab)
    (paid Site.bcToGlobal hbc)
    (paid Site.caToGlobal hca)
  where
    ab = value family Site.abToGlobal hab
    bc = value family Site.bcToGlobal hbc
    ca = value family Site.caToGlobal hca
    matching = P.coverTripleToTriadicMatching ab bc ca
      (triadicMatchingFromSieve sieve family hab hbc hca)

-- Source site topology ALREADY had these axioms. The proof above
-- adds sheaf gluing/uniqueness, not another fake Grothendieck receipt.
selectedTopology =
  Site.relationalTriadicTopology
