module DASHI.Foundations.TernaryGolay.CoxeterToddRoutesBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Correct Coxeter–Todd routes.
--
-- Route A: an order-three fixed-sublattice construction inside the Leech
-- lattice, requiring an explicit automorphism and equivalence receipt.
-- Route B: an Eisenstein Construction-Bc style route from a length-six
-- ternary repetition code, requiring the actual Eisenstein and construction
-- laws. Neither route is conflated with the corrected Z/9 Golay lift.
------------------------------------------------------------------------

record CoxeterToddInvariantReceipt : Set where
  constructor coxeterToddInvariantReceipt
  field
    realRank : Nat
    eisensteinRank : Nat
    minimumNorm : Nat
    minimalVectorCount : Nat
    discriminantExponentOfThree : Nat
    automorphismGroupOrder : Nat
    realRankIsTwelve : realRank ≡ 12
    eisensteinRankIsSix : eisensteinRank ≡ 6
    minimumNormIsFour : minimumNorm ≡ 4
    minimalVectorCountIs756 : minimalVectorCount ≡ 756
    discriminantExponentIsSix : discriminantExponentOfThree ≡ 6
    automorphismGroupOrderIs78382080 :
      automorphismGroupOrder ≡ 78382080
    rootless : Bool
    rootlessIsTrue : rootless ≡ true
    invariantSourceAuthor : String
    invariantSourceTitle : String
    invariantSourceDOI : String

open CoxeterToddInvariantReceipt public

canonicalCoxeterToddInvariants : CoxeterToddInvariantReceipt
canonicalCoxeterToddInvariants =
  coxeterToddInvariantReceipt
    12 6 4 756 6 78382080
    refl refl refl refl refl refl
    true refl
    (Sources.author Sources.sloaneCoxeterToddEntry)
    (Sources.title Sources.sloaneCoxeterToddEntry)
    "10.1017/S0305004100060746"

record OrderThreeFixedSublatticeRoute
    (Leech Automorphism K12 : Set) : Set₁ where
  field
    fixedSigma : Automorphism
    fixedAutomorphismActs : Automorphism → Leech → Leech
    fixedIdentityAutomorphism : Automorphism
    fixedComposeAutomorphism : Automorphism → Automorphism → Automorphism
    fixedSigmaCubedIsIdentity :
      fixedComposeAutomorphism
        fixedSigma
        (fixedComposeAutomorphism fixedSigma fixedSigma)
      ≡ fixedIdentityAutomorphism
    Fixed : Leech → Set
    fixedDefinition :
      (x : Leech) →
      Fixed x →
      fixedAutomorphismActs fixedSigma x ≡ x
    fixedCarrier : Set
    fixedCarrierRepresentsFixedPoints : Set
    fixedEquivalenceToK12 : Set
    fixedEquivalenceReceipt : fixedEquivalenceToK12
    fixedSourceAuthor : String
    fixedSourceTitle : String
    fixedSourceDOI : String

open OrderThreeFixedSublatticeRoute public

record EisensteinRepetitionConstructionRoute
    (Eisenstein CoefficientVector RepetitionCode Lattice K12 : Set) : Set₁ where
  field
    eisensteinZero : Eisenstein
    eisensteinOne : Eisenstein
    eisensteinOmega : Eisenstein
    eisensteinAdd : Eisenstein → Eisenstein → Eisenstein
    eisensteinMul : Eisenstein → Eisenstein → Eisenstein
    eisensteinOmegaQuadraticLaw :
      eisensteinAdd
        (eisensteinAdd
          (eisensteinMul eisensteinOmega eisensteinOmega)
          eisensteinOmega)
        eisensteinOne
      ≡ eisensteinZero
    lengthSixCoefficientVector : CoefficientVector
    ternaryRepetitionCode : RepetitionCode
    repetitionCodeLengthIsSix : Set
    constructionBc : RepetitionCode → Lattice
    constructionLattice : Lattice
    constructionLatticeIsBcImage :
      constructionLattice ≡ constructionBc ternaryRepetitionCode
    eisensteinEquivalenceToK12 : Set
    eisensteinEquivalenceReceipt : eisensteinEquivalenceToK12
    eisensteinSourceAuthor : String
    eisensteinSourceTitle : String
    eisensteinSourceDOI : String

open EisensteinRepetitionConstructionRoute public

data CorrectK12RouteKind : Set where
  leechOrderThreeFixedRoute : CorrectK12RouteKind
  eisensteinRepetitionBcRoute : CorrectK12RouteKind

record CoxeterToddRouteStatus : Set where
  constructor coxeterToddRouteStatus
  field
    validRouteKinds : CorrectK12RouteKind → Bool
    fixedRouteRecognised :
      validRouteKinds leechOrderThreeFixedRoute ≡ true
    eisensteinRouteRecognised :
      validRouteKinds eisensteinRepetitionBcRoute ≡ true
    ternaryGolayZ9ConstructionAProducesK12 : Bool
    ternaryGolayZ9ConstructionAProducesK12IsFalse :
      ternaryGolayZ9ConstructionAProducesK12 ≡ false
    fixedRouteProofImportedHere : Bool
    fixedRouteProofImportedHereIsFalse : fixedRouteProofImportedHere ≡ false
    eisensteinRouteProofImportedHere : Bool
    eisensteinRouteProofImportedHereIsFalse :
      eisensteinRouteProofImportedHere ≡ false
    routeReading : String

open CoxeterToddRouteStatus public

routeAccepted : CorrectK12RouteKind → Bool
routeAccepted leechOrderThreeFixedRoute = true
routeAccepted eisensteinRepetitionBcRoute = true

canonicalCoxeterToddRouteStatus : CoxeterToddRouteStatus
canonicalCoxeterToddRouteStatus =
  coxeterToddRouteStatus
    routeAccepted
    refl
    refl
    false refl
    false refl
    false refl
    "the fixed-sublattice and Eisenstein-Bc routes are legitimate theorem interfaces; their external proofs have not been silently imported"

coxeterToddRoutesGenericReceipt : GenericReceipt.GenericReceipt
coxeterToddRoutesGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Coxeter-Todd correct-route boundary"
    "DASHI.Foundations.TernaryGolay.CoxeterToddRoutesBoundary"
    "canonicalCoxeterToddRouteStatus"
    "K12 invariants, an order-three Leech fixed-sublattice interface, and an Eisenstein repetition-code Bc interface are separated from the corrected Z9 lift"
    "actual lattice equivalences, Eisenstein generation, and automorphism proofs require named external theorem imports"
    "agda -i . DASHI/Foundations/TernaryGolay/CoxeterToddRoutesBoundary.agda"

coxeterToddRoutesGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim coxeterToddRoutesGenericReceipt ≡ false
coxeterToddRoutesGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse coxeterToddRoutesGenericReceipt
