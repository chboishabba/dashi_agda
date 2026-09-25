module DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC SUPERSINGULAR / CM / LEVEL-STRUCTURE SOURCE ATLAS
--
-- Purpose
--
-- Separate four different claim strengths:
--
--   (1) classical direct facts:
--       unique coarse supersingular class at p=2 and p=3;
--       exceptional automorphism groups in characteristics 2 and 3;
--
--   (2) classical CM-reduction facts:
--       non-split CM reduction is supersingular and carries normalized optimal
--       embedding data in the supersingular endomorphism ring;
--
--   (3) classical bad-level moduli framework:
--       p-power level structures in characteristic p are Drinfeld/group-scheme
--       moduli data and Γ0(p^r) at bad primes is not a naive finite point set;
--
--   (4) DASHI finite presentations:
--       the exact three-state p=3 quotient and ten-state p=2 retained carrier.
--
-- The sources support (1)--(3).  They do NOT state (4), and this atlas makes
-- that non-identification theorem-bearing.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_%_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- 1. Classical sources.
------------------------------------------------------------------------

silverman : Source.AttributedSource
silverman =
  Source.mkDOISource
    "Joseph H. Silverman"
    "The Arithmetic of Elliptic Curves, Second Edition"
    "Graduate Texts in Mathematics 106, Springer"
    "2009"
    "10.1007/978-0-387-09494-6"
    "https://doi.org/10.1007/978-0-387-09494-6"
    Source.academicBookSource
    "classical authority for supersingularity criteria, the unique characteristic-2 supersingular curve y^2+y=x^3, and exceptional automorphism groups in characteristics 2 and 3; does not state the DASHI three-state or ten-state marked presentations"
    Source.publicAttribution

katzMazur : Source.AttributedSource
katzMazur =
  Source.mkDOISource
    "Nicholas M. Katz and Barry Mazur"
    "Arithmetic Moduli of Elliptic Curves"
    "Annals of Mathematics Studies 108, Princeton University Press"
    "1985"
    "10.1515/9781400881710"
    "https://doi.org/10.1515/9781400881710"
    Source.academicBookSource
    "classical moduli authority for Drinfeld level structures and p-power level structure in bad characteristic; supports marked/group-scheme moduli over the coarse j-line, not the repository's exact finite 369 carrier"
    Source.publicAttribution


deligneRapoport : Source.AttributedSource
deligneRapoport =
  Source.mkDOISource
    "Pierre Deligne and Michael Rapoport"
    "Les schemas de modules de courbes elliptiques"
    "Modular Functions of One Variable II, Lecture Notes in Mathematics 349, Springer"
    "1973"
    "10.1007/978-3-540-37855-6_4"
    "https://doi.org/10.1007/978-3-540-37855-6_4"
    Source.academicArticleSource
    "classical source for the bad-prime model of X0(p): two components meeting at supersingular points, with the two p-isogeny branches represented by Frobenius and Verschiebung; supports the p=3 local node/branch incidence realization, not three distinct supersingular curves"
    Source.publicAttribution

bertoliniDarmonPrasannaConrad : Source.AttributedSource
bertoliniDarmonPrasannaConrad =
  Source.mkDOISource
    "Massimo Bertolini, Henri Darmon, Kartik Prasanna, and Brian Conrad"
    "p-adic L-functions and the coniveau filtration on Chow groups"
    "Journal fur die reine und angewandte Mathematik 731, 21-86"
    "2017"
    "10.1515/crelle-2014-0150"
    "https://doi.org/10.1515/crelle-2014-0150"
    Source.academicArticleSource
    "Appendix-level bad-characteristic modular-curve authority used for the exact statement that a supersingular elliptic curve admits a unique Drinfeld cyclic subgroup scheme of order p^r, namely the kernel of the r-fold relative Frobenius; this rules out interpreting the ten DASHI p=2 states as ten distinct Gamma0(4) supersingular level structures"
    Source.publicAttribution


gorenLove : Source.AttributedSource
gorenLove =
  Source.mkDOISource
    "Eyal Z. Goren and Jonathan R. Love"
    "On elements of prescribed norm in maximal orders of a quaternion algebra"
    "Canadian Journal of Mathematics 77(6), 1938-1965"
    "2025"
    "10.4153/S0008414X24000592"
    "https://doi.org/10.4153/S0008414X24000592"
    Source.academicArticleSource
    "classical quaternion-order authority for oriented imaginary quadratic orders: every imaginary quadratic discriminant has exactly two oriented orders up to oriented isomorphism, exchanged by the nontrivial Galois action; also relates oriented quadratic-order embeddings to primitive Gross-lattice elements"
    Source.publicAttribution

dadhwalPankaj : Source.AttributedSource
dadhwalPankaj =
  Source.mkDOISource
    "Madhu Dadhwal and Pankaj"
    "Group codes over binary tetrahedral group"
    "Journal of Mathematical Cryptology 16(1), 310-319"
    "2022"
    "10.1515/jmc-2022-0009"
    "https://doi.org/10.1515/jmc-2022-0009"
    Source.academicArticleSource
    "explicit finite-group source listing the seven conjugacy classes of the binary tetrahedral group; used only for the class/inversion quotient count, not for elliptic-curve identification"
    Source.publicAttribution

conrad : Source.AttributedSource
conrad =
  Source.mkDOISource
    "Brian Conrad"
    "Arithmetic moduli of generalized elliptic curves"
    "Journal of the Institute of Mathematics of Jussieu 6(2), 209-278"
    "2007"
    "10.1017/S1474748006000089"
    "https://doi.org/10.1017/S1474748006000089"
    Source.academicArticleSource
    "integral/bad-characteristic Γ-level and Γ0(n) moduli authority; in particular non-squarefree p-power level can have non-etale automorphisms and must be treated as Artin/Drinfeld moduli rather than a naive set of torsion points"
    Source.publicAttribution

elkiesOnoYang : Source.AttributedSource
elkiesOnoYang =
  Source.mkDOISource
    "Noam D. Elkies, Ken Ono, and Tonghai Yang"
    "Reduction of CM elliptic curves and modular function congruences"
    "International Mathematics Research Notices 2005(44), 2695-2707"
    "2005"
    "10.1155/IMRN.2005.2695"
    "https://doi.org/10.1155/IMRN.2005.2695"
    Source.academicArticleSource
    "modern source explicitly invoking Deuring reduction: CM reduction at inert or ramified primes is supersingular and a normalized CM embedding descends to an optimal embedding into the supersingular endomorphism ring; supports genuine marked endomorphism data over a coarse supersingular j-class"
    Source.publicAttribution

ogg : Source.AttributedSource
ogg =
  Source.mkNoDOISource
    "Andrew P. Ogg"
    "Automorphismes de courbes modulaires"
    "Seminaire Delange-Pisot-Poitou, 16e annee 1974/75, expose 7"
    "1975"
    "https://www.numdam.org/item/SDPP_1974-1975__16_1_A4_0.pdf"
    Source.academicArticleSource
    "source context for supersingular points on modular curves and the exceptional characteristic-2 supersingular curve; Ogg's cyclic-subgroup counting argument quoted for odd level does not justify a Γ0(4) ten-state identification"
    Source.publicAttribution

smallCharacteristicClassicalAtlas : Source.AttributedSourceAtlas
smallCharacteristicClassicalAtlas =
  Source.mkSourceAtlas
    "small-characteristic supersingular/CM/level-structure classical atlas"
    "DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact"
    (silverman ∷ katzMazur ∷ deligneRapoport ∷ bertoliniDarmonPrasannaConrad ∷ gorenLove ∷ dadhwalPankaj ∷ conrad ∷ elkiesOnoYang ∷ ogg ∷ [])
    "classical authority is partitioned into coarse supersingular classification, CM reduction/optimal-embedding marking, and bad-characteristic level-moduli theory; exact DASHI finite state counts and 369 recognitions remain repository reconstructions unless independently identified"

------------------------------------------------------------------------
-- 2. Claim-strength grading.
------------------------------------------------------------------------

data ClassicalSupportGrade : Set where
  directClassicalTheorem :
    ClassicalSupportGrade

  classicalFrameworkSupportsShape :
    ClassicalSupportGrade

  repositoryFormalReconstruction :
    ClassicalSupportGrade

  externalSameObjectIdentificationOpen :
    ClassicalSupportGrade

p2UniqueCoarseSupersingularClassGrade :
  ClassicalSupportGrade
p2UniqueCoarseSupersingularClassGrade =
  directClassicalTheorem

p3UniqueCoarseSupersingularClassGrade :
  ClassicalSupportGrade
p3UniqueCoarseSupersingularClassGrade =
  directClassicalTheorem

smallCharacteristicAutomorphismEnhancementGrade :
  ClassicalSupportGrade
smallCharacteristicAutomorphismEnhancementGrade =
  directClassicalTheorem

cmReductionToSupersingularGrade :
  ClassicalSupportGrade
cmReductionToSupersingularGrade =
  directClassicalTheorem

normalizedOptimalEmbeddingMarkingGrade :
  ClassicalSupportGrade
normalizedOptimalEmbeddingMarkingGrade =
  directClassicalTheorem

badPrimeLevelStructureNeedsGroupSchemeModuliGrade :
  ClassicalSupportGrade
badPrimeLevelStructureNeedsGroupSchemeModuliGrade =
  directClassicalTheorem

p3DeligneRapoportLocalNodeGrade :
  ClassicalSupportGrade
p3DeligneRapoportLocalNodeGrade =
  directClassicalTheorem

p2UniqueDrinfeldOrderFourSubgroupGrade :
  ClassicalSupportGrade
p2UniqueDrinfeldOrderFourSubgroupGrade =
  directClassicalTheorem

p2TwoOrientedQuadraticOrdersGrade :
  ClassicalSupportGrade
p2TwoOrientedQuadraticOrdersGrade =
  directClassicalTheorem

binaryTetrahedralSevenConjugacyClassesGrade :
  ClassicalSupportGrade
binaryTetrahedralSevenConjugacyClassesGrade =
  directClassicalTheorem

binaryTetrahedralFiveInversionOrbitGrade :
  ClassicalSupportGrade
binaryTetrahedralFiveInversionOrbitGrade =
  repositoryFormalReconstruction

p3ThreeStateExtensionQuotientGrade :
  ClassicalSupportGrade
p3ThreeStateExtensionQuotientGrade =
  repositoryFormalReconstruction

p2TenStateRetainedCMCarrierGrade :
  ClassicalSupportGrade
p2TenStateRetainedCMCarrierGrade =
  repositoryFormalReconstruction

p3ClassicalSameObjectGrade :
  ClassicalSupportGrade
p3ClassicalSameObjectGrade =
  externalSameObjectIdentificationOpen

p2ClassicalSameObjectGrade :
  ClassicalSupportGrade
p2ClassicalSameObjectGrade =
  externalSameObjectIdentificationOpen

------------------------------------------------------------------------
-- 3. Small-characteristic normalization facts.
--
-- In characteristics 2 and 3 the integers 1728 and 0 have the same residue
-- class.  Thus phrases such as "j=1728" at p=2 or p=3 must be understood as a
-- CM-lift/characteristic-zero label when used to distinguish Gaussian-CM
-- provenance; they do not name a second coarse geometric j-class downstairs.
------------------------------------------------------------------------

j1728Mod2 :
  1728 % 2 ≡ 0
j1728Mod2 = refl

j1728Mod3 :
  1728 % 3 ≡ 0
j1728Mod3 = refl

data J1728CreatesSecondCoarseClassAtP2 : Set where
data J1728CreatesSecondCoarseClassAtP3 : Set where

j1728DoesNotCreateSecondCoarseClassAtP2 :
  J1728CreatesSecondCoarseClassAtP2 -> ⊥
j1728DoesNotCreateSecondCoarseClassAtP2 ()

j1728DoesNotCreateSecondCoarseClassAtP3 :
  J1728CreatesSecondCoarseClassAtP3 -> ⊥
j1728DoesNotCreateSecondCoarseClassAtP3 ()

------------------------------------------------------------------------
-- 4. What the classical literature DOES license.
------------------------------------------------------------------------

record ClassicalMarkedSupersingularShape : Set where
  constructor classical-marked-supersingular-shape
  field
    oneCoarseSupersingularClassAllowed : Bool
    extraEndomorphismOrLevelMarkingAllowed : Bool
    FrobeniusOrGaloisActionOnMarkingAllowed : Bool
    nonEtaleBadLevelStructureAllowed : Bool
    stackOrGroupoidSemanticsNatural : Bool

canonicalClassicalMarkedSupersingularShape :
  ClassicalMarkedSupersingularShape
canonicalClassicalMarkedSupersingularShape =
  classical-marked-supersingular-shape
    true true true true true

------------------------------------------------------------------------
-- 5. What the classical literature in this atlas does NOT license.
------------------------------------------------------------------------

data ClassicalSourcesProveP3ThreeStateCarrier : Set where
data ClassicalSourcesProveP2TenStateCarrier : Set where
data ClassicalSourcesIdentifyBase369Carrier : Set where
data ClassicalSourcesIdentifyNineOrbit : Set where
data ClassicalSourcesIdentifyTrialectic369 : Set where
data OggOddLevelCountAppliesDirectlyToGamma0Four : Set where

classicalSourcesDoNotProveP3ThreeStateCarrier :
  ClassicalSourcesProveP3ThreeStateCarrier -> ⊥
classicalSourcesDoNotProveP3ThreeStateCarrier ()

classicalSourcesDoNotProveP2TenStateCarrier :
  ClassicalSourcesProveP2TenStateCarrier -> ⊥
classicalSourcesDoNotProveP2TenStateCarrier ()

classicalSourcesDoNotIdentifyBase369Carrier :
  ClassicalSourcesIdentifyBase369Carrier -> ⊥
classicalSourcesDoNotIdentifyBase369Carrier ()

classicalSourcesDoNotIdentifyNineOrbit :
  ClassicalSourcesIdentifyNineOrbit -> ⊥
classicalSourcesDoNotIdentifyNineOrbit ()

classicalSourcesDoNotIdentifyTrialectic369 :
  ClassicalSourcesIdentifyTrialectic369 -> ⊥
classicalSourcesDoNotIdentifyTrialectic369 ()

oggOddLevelCountDoesNotApplyDirectlyToGamma0Four :
  OggOddLevelCountAppliesDirectlyToGamma0Four -> ⊥
oggOddLevelCountDoesNotApplyDirectlyToGamma0Four ()

------------------------------------------------------------------------
-- 6. Canonical sourcing boundary.
------------------------------------------------------------------------

record SmallCharacteristicClassicalSourcingBoundary : Set where
  constructor small-characteristic-classical-sourcing-boundary
  field
    uniqueP2CoarseClassClassicallySourced : Bool
    uniqueP3CoarseClassClassicallySourced : Bool
    exceptionalAutomorphismsClassicallySourced : Bool
    deuringCMReductionClassicallySourced : Bool
    normalizedOptimalEmbeddingMarkingClassicallySourced : Bool
    badPrimeDrinfeldLevelFrameworkClassicallySourced : Bool
    gamma0PpowerStackSubtletyClassicallySourced : Bool
    p3DeligneRapoportLocalNodeClassicallySourced : Bool
    p2UniqueDrinfeldOrderFourSubgroupClassicallySourced : Bool
    p2TwoOrientedQuadraticOrdersClassicallySourced : Bool
    binaryTetrahedralSevenClassesClassicallySourced : Bool
    binaryTetrahedralFiveInversionOrbitsReconstructed : Bool

    p3ThreeStateCountClassicallySourced : Bool
    p2TenStateCountClassicallySourced : Bool
    base369ClassicallyIdentified : Bool
    nineOrbitClassicallyIdentified : Bool

    j1728AtP2IsDistinctCoarseJ : Bool
    j1728AtP3IsDistinctCoarseJ : Bool

    dashiFinitePresentationsRemainFormalReconstructions : Bool

canonicalSmallCharacteristicClassicalSourcingBoundary :
  SmallCharacteristicClassicalSourcingBoundary
canonicalSmallCharacteristicClassicalSourcingBoundary =
  small-characteristic-classical-sourcing-boundary
    true true true true true true true true true true true true
    false false false false
    false false
    true
