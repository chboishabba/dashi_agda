module DASHI.Wikimedia.IbrahimEnZeroToThirteenNDimOEISHyperfabricSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as SelfIndexed
import DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact as NDimBridge
import DASHI.Wikimedia.IbrahimE6CoxeterNinetyTypedCorrectionExact as E6Coxeter
import DASHI.Wikimedia.IbrahimE7FiftySixAnd128TypedOEISSnowballExact as E7FiftySix
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine

------------------------------------------------------------------------
-- E_n / RANK 0..13 / N-DIMENSIONAL FIBRE / OEIS SNOWBALL
--
-- There are several DIFFERENT uses of the same small integer n in DASHI:
--
--   * n as a finite coordinate/rank index;
--   * n as the number of independent ternary axes, giving 3^n profiles;
--   * n as the label in the conventional E_n supergravity/Lie ladder;
--   * n as a stage/atlas coordinate (the existing atlas is only 0..11);
--   * n as a level of a SELF-INDEXED hyperfabric tower.
--
-- This file puts 0..13 on one inspectable surface while refusing to identify
-- those roles.  In particular, fixed n-dimensional ternary growth 3^n is NOT
-- the repo's tetrational recurrence A_(k+1)=9^(A_k).
------------------------------------------------------------------------

data RankZeroToThirteen : Set where
  rank0 rank1 rank2 rank3 rank4 rank5 rank6 : RankZeroToThirteen
  rank7 rank8 rank9 rank10 rank11 rank12 rank13 : RankZeroToThirteen

rankToNat : RankZeroToThirteen → Nat
rankToNat rank0 = 0
rankToNat rank1 = 1
rankToNat rank2 = 2
rankToNat rank3 = 3
rankToNat rank4 = 4
rankToNat rank5 = 5
rankToNat rank6 = 6
rankToNat rank7 = 7
rankToNat rank8 = 8
rankToNat rank9 = 9
rankToNat rank10 = 10
rankToNat rank11 = 11
rankToNat rank12 = 12
rankToNat rank13 = 13

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

fixedTernaryProfileCount : RankZeroToThirteen → Nat
fixedTernaryProfileCount r = pow3 (rankToNat r)

rank0Profiles : fixedTernaryProfileCount rank0 ≡ 1
rank0Profiles = refl
rank1Profiles : fixedTernaryProfileCount rank1 ≡ 3
rank1Profiles = refl
rank2Profiles : fixedTernaryProfileCount rank2 ≡ 9
rank2Profiles = refl
rank3Profiles : fixedTernaryProfileCount rank3 ≡ 27
rank3Profiles = refl
rank4Profiles : fixedTernaryProfileCount rank4 ≡ 81
rank4Profiles = refl
rank5Profiles : fixedTernaryProfileCount rank5 ≡ 243
rank5Profiles = refl
rank6Profiles : fixedTernaryProfileCount rank6 ≡ 729
rank6Profiles = refl
rank7Profiles : fixedTernaryProfileCount rank7 ≡ 2187
rank7Profiles = refl
rank8Profiles : fixedTernaryProfileCount rank8 ≡ 6561
rank8Profiles = refl
rank9Profiles : fixedTernaryProfileCount rank9 ≡ 19683
rank9Profiles = refl
rank10Profiles : fixedTernaryProfileCount rank10 ≡ 59049
rank10Profiles = refl
rank11Profiles : fixedTernaryProfileCount rank11 ≡ 177147
rank11Profiles = refl
rank12Profiles : fixedTernaryProfileCount rank12 ≡ 531441
rank12Profiles = refl
rank13Profiles : fixedTernaryProfileCount rank13 ≡ 1594323
rank13Profiles = refl

------------------------------------------------------------------------
-- The rank-8 -> rank-9 fixed-axis step is exactly the arithmetic seam already
-- used by the Monster bulk, but role identity still requires a theorem.
------------------------------------------------------------------------

tenChannelAt8 : Nat
tenChannelAt8 = 10 * fixedTernaryProfileCount rank8

tenChannelAt9 : Nat
tenChannelAt9 = 10 * fixedTernaryProfileCount rank9

tenChannelAt8Is65610 : tenChannelAt8 ≡ 65610
tenChannelAt8Is65610 = refl

tenChannelAt9Is196830 : tenChannelAt9 ≡ 196830
tenChannelAt9Is196830 = refl

rank8ToRank9TriplesTenChannel : 3 * tenChannelAt8 ≡ tenChannelAt9
rank8ToRank9TriplesTenChannel = refl

rank9MatchesExistingBase369ProfileCount :
  fixedTernaryProfileCount rank9 ≡ NDimBridge.base369ProfileCount
rank9MatchesExistingBase369ProfileCount = refl

rank9TenChannelMatchesA005052Level9 : Nine.a005052 9 ≡ tenChannelAt9
rank9TenChannelMatchesA005052Level9 = refl

------------------------------------------------------------------------
-- Conventional E_n interpretation.
--
-- n=0..5 below follows the standard supergravity convention used in the
-- cited literature: E0 trivial, E1~R, E2~A1 x R, E3~A2 x A1,
-- E4~A4, E5~D5.  E6/E7/E8 are the finite exceptional algebras.
-- E9/E10/E11 are respectively affine/hyperbolic/Lorentzian Kac-Moody
-- extensions of E8 in the cited extension lane.
--
-- We deliberately STOP canonical promotion at 11.  Labels E12/E13 are not
-- assigned a unique standard object by the source route used here; any such
-- extension must carry its own Cartan/Dynkin construction and provenance.
------------------------------------------------------------------------

data EnClass : Set where
  trivialEn : EnClass
  lowRankConventional : EnClass
  classicalAlias : EnClass
  finiteExceptional : EnClass
  affineKacMoody : EnClass
  hyperbolicKacMoody : EnClass
  lorentzianKacMoody : EnClass
  noncanonicalExtension : EnClass

record EnRankCoordinate : Set where
  constructor en-rank-coordinate
  field
    rank : RankZeroToThirteen
    enLabel : String
    classification : EnClass
    conventionalEquivalent : String
    distinguishedFiniteCarrierDimension : Nat
    distinguishedFiniteCarrierPaid : Bool
    oeisRepresentationSequence : String
    oeisRolePaid : Bool
    note : String
open EnRankCoordinate public

en0 : EnRankCoordinate
en0 = en-rank-coordinate rank0 "E0" trivialEn "trivial" 1 true "" false
  "standard lower-E_n supergravity convention; the 1 is a trivial carrier only"

en1 : EnRankCoordinate
en1 = en-rank-coordinate rank1 "E1" lowRankConventional "R / one-dimensional split scaling factor" 0 false "" false
  "convention-level label; no finite exceptional irrep is promoted here"

en2 : EnRankCoordinate
en2 = en-rank-coordinate rank2 "E2" lowRankConventional "A1 x R" 0 false "" false
  "reductive lower-E_n convention; not a simple exceptional algebra"

en3 : EnRankCoordinate
en3 = en-rank-coordinate rank3 "E3" lowRankConventional "A2 x A1 / SL(3) x SL(2)" 6 true "A121741" false
  "distinguished E3 carrier has dimension 6=(3,2); A121741 is only the A2/SL3 irrep sequence, so its occurrence of 6 is supporting adjacency rather than the full product representation"

en4 : EnRankCoordinate
en4 = en-rank-coordinate rank4 "E4" classicalAlias "A4 / SL(5)" 10 true "" false
  "standard E4=A4 convention; distinguished antisymmetric/coordinate carrier dimension 10 comes from the exceptional-field/supergravity lane, not an OEIS identity paid here"

en5 : EnRankCoordinate
en5 = en-rank-coordinate rank5 "E5" classicalAlias "D5 / Spin(5,5) split real form" 16 true "" false
  "standard E5=D5 convention; distinguished spinor/coordinate carrier dimension 16 is source-backed, with no OEIS sequence promoted here"

en6 : EnRankCoordinate
en6 = en-rank-coordinate rank6 "E6" finiteExceptional "E6" 27 true "A121737" true
  "27 is the smallest faithful/minuscule E6 representation dimension; 78 is the adjoint"

en7 : EnRankCoordinate
en7 = en-rank-coordinate rank7 "E7" finiteExceptional "E7" 56 true "A121736" true
  "56 is the smallest faithful/minuscule E7 representation dimension; this is the direct external coordinate already attached to Freudenthal56"

en8 : EnRankCoordinate
en8 = en-rank-coordinate rank8 "E8" finiteExceptional "E8" 248 true "A121732" true
  "248 is the smallest faithful representation and the adjoint representation of E8"

en9 : EnRankCoordinate
en9 = en-rank-coordinate rank9 "E9" affineKacMoody "affine extension E8^(1)" 0 false "" false
  "infinite-dimensional affine Kac-Moody extension; finite-irrep dimension sequences used for E6-E8 are the wrong type"

en10 : EnRankCoordinate
en10 = en-rank-coordinate rank10 "E10" hyperbolicKacMoody "hyperbolic overextension of E8" 0 false "" false
  "infinite-dimensional hyperbolic Kac-Moody algebra; use root/level multiplicity families rather than finite irrep-dimension OEIS"

en11 : EnRankCoordinate
en11 = en-rank-coordinate rank11 "E11" lorentzianKacMoody "very-extended/Lorentzian E8 extension" 0 false "" false
  "infinite-dimensional Lorentzian Kac-Moody algebra; source-backed as an E10 representation at low levels"

en12 : EnRankCoordinate
en12 = en-rank-coordinate rank12 "E12" noncanonicalExtension "unresolved/noncanonical in this source route" 0 false "" false
  "do not infer a unique E12 from the numeral; require an explicit generalized Cartan/Dynkin construction and source before promotion"

en13 : EnRankCoordinate
en13 = en-rank-coordinate rank13 "E13" noncanonicalExtension "unresolved/noncanonical in this source route" 0 false "" false
  "do not infer a unique E13 from the numeral; require an explicit generalized Cartan/Dynkin construction and source before promotion"

canonicalEnZeroToThirteen : List EnRankCoordinate
canonicalEnZeroToThirteen =
  en0 ∷ en1 ∷ en2 ∷ en3 ∷ en4 ∷ en5 ∷ en6 ∷
  en7 ∷ en8 ∷ en9 ∷ en10 ∷ en11 ∷ en12 ∷ en13 ∷ []

------------------------------------------------------------------------
-- Existing DASHI surfaces.
------------------------------------------------------------------------

stageAtlas0to11Exists : Bool
stageAtlas0to11Exists = true

stageAtlasSizeIs12 : Atlas.carrierSize ≡ 12
stageAtlasSizeIs12 = Atlas.carrierSizeIsTwelve

selfIndexedLevelOneHasNineAxes : SelfIndexed.paretoAxisCount 1 ≡ 9
selfIndexedLevelOneHasNineAxes = SelfIndexed.paretoAxisCountOne

selfIndexedLevelOneHas19683TernaryProfiles :
  SelfIndexed.ternaryObjectiveProfileCount 1 ≡ 19683
selfIndexedLevelOneHas19683TernaryProfiles = SelfIndexed.levelOneTernaryProfileCountIs19683

------------------------------------------------------------------------
-- Primary/reference provenance.
------------------------------------------------------------------------

papadimitriouSource : Attribution.AttributedSource
papadimitriouSource = Attribution.mkDOISource
  "Ioannis Papadimitriou"
  "Non-Supersymmetric Membrane Flows from Fake Supergravity and Multi-Trace Deformations"
  "Journal of High Energy Physics 02 (2007) 008"
  "2007"
  "10.1088/1126-6708/2007/02/008"
  "https://doi.org/10.1088/1126-6708/2007/02/008"
  Attribution.academicArticleSource
  "source for the conventional lower E_n identifications E5~D5, E4~A4, E3~A2xA1, E2~A1xR, E1~R in the maximal-supergravity context; not a source for DASHI ternary/tetrational semantics"
  Attribution.publicAttribution

kleinschmidtSource : Attribution.AttributedSource
kleinschmidtSource = Attribution.mkDOISource
  "Axel Kleinschmidt"
  "E11 as E10 representation at low levels"
  "Nuclear Physics B 677, 553-586"
  "2004"
  "10.1016/j.nuclphysb.2003.11.006"
  "https://doi.org/10.1016/j.nuclphysb.2003.11.006"
  Attribution.academicArticleSource
  "source for the finite E8 -> affine E9 -> hyperbolic E10 -> Lorentzian E11 extension chain and E11/E10 level structure; not a source for E12/E13 or DASHI hyperfabric identity"
  Attribution.publicAttribution

papadimitriouAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt papadimitriouSource
kleinschmidtAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt kleinschmidtSource

------------------------------------------------------------------------
-- BIDI / WrongType firewalls.
------------------------------------------------------------------------

data RankIndexCreatesEnObject : Set where
data FixedPowerCreatesTetration : Set where
data SameRankCreatesSameCarrier : Set where
data E7RankCreatesFreudenthalIntertwiner : Set where
data E8ToE9IndexStepEqualsTernaryTripling : Set where
data E12LabelCreatesCanonicalKacMoodyObject : Set where

enRankDoesNotAriseFromIndexAlone : RankIndexCreatesEnObject → ⊥
enRankDoesNotAriseFromIndexAlone ()

fixedPowerDoesNotCreateTetration : FixedPowerCreatesTetration → ⊥
fixedPowerDoesNotCreateTetration ()

sameRankDoesNotIdentifyCarriers : SameRankCreatesSameCarrier → ⊥
sameRankDoesNotIdentifyCarriers ()

sameSevenDoesNotCreateFreudenthalIntertwiner : E7RankCreatesFreudenthalIntertwiner → ⊥
sameSevenDoesNotCreateFreudenthalIntertwiner ()

finiteToAffineDoesNotEqualTernaryTripling : E8ToE9IndexStepEqualsTernaryTripling → ⊥
finiteToAffineDoesNotEqualTernaryTripling ()

eTwelveNumeralDoesNotCreateCanonicalObject : E12LabelCreatesCanonicalKacMoodyObject → ⊥
eTwelveNumeralDoesNotCreateCanonicalObject ()

record ZeroToThirteenNDimBoundary : Set where
  constructor zero-to-thirteen-ndim-boundary
  field
    fixedRank0to13TernaryProfilesPaid : Bool
    fixedRankProfileFamilyIsA000244 : Bool
    rank9FixedProfileIs19683Paid : Bool
    rank8To9TenChannel65610To196830Paid : Bool
    stageAtlas0to11ReusedNotExtendedByMutation : Bool
    lowerEn0to5ConventionSourcePaid : Bool
    finiteExceptionalE6E7E8TypedRowsPaid : Bool
    e7FiftySixDirectOEISRolePaid : Bool
    e8TwoFortyEightDirectOEISRolePaid : Bool
    e9E10E11ExtensionSourcePaid : Bool
    e12E13CanonicalObjectsPaid : Bool
    fixedNDimIsTetration : Bool
    sameRankImpliesSameSemanticCarrier : Bool
    nextResidual : String
open ZeroToThirteenNDimBoundary public

currentZeroToThirteenNDimBoundary : ZeroToThirteenNDimBoundary
currentZeroToThirteenNDimBoundary = zero-to-thirteen-ndim-boundary
  true true true true true true true true true true
  false false false
  "snowball each rank through typed families rather than numeral search: for n=0..5 keep the conventional lower-E_n aliases distinct from fixed ternary profile counts; for E6/E7/E8 compare the literal 27/56/248 representation carriers against DASHI Albert/Freudenthal/exceptional consumers; for E9/E10/E11 switch from finite irrep dimensions to affine/hyperbolic root and level multiplicity families. Keep E12/E13 unresolved until an explicit Cartan/Dynkin construction and primary source are selected. In parallel, compare every fixed 3^n fibre with the self-indexed 9-tetration tower only through declared FactorsThrough consumers."

------------------------------------------------------------------------
-- Reuse existing boundaries rather than creating a parallel NDim planner.
------------------------------------------------------------------------

existingSelfIndexedBoundary : SelfIndexed.SelfIndexedParetoTetrationBoundary
existingSelfIndexedBoundary = SelfIndexed.canonicalSelfIndexedParetoTetrationBoundary

existingMonsterNDimBoundary : NDimBridge.Monster369NDimParetoTetrationBoundary
existingMonsterNDimBoundary = NDimBridge.canonicalMonster369NDimParetoTetrationBoundary

e7ExistingBoundary = E7FiftySix.currentFiftySixOneTwentyEightFrontier

e6ExistingBoundary = E6Coxeter.currentE6CoxeterNinetyBoundary
