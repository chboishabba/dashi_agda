module DASHI.Mathematics.Topology.ExoticSourceGenealogyParetoExact where

------------------------------------------------------------------------
-- SOURCE GENEALOGY / IBRAHIM FIRST-LINK / SNOWBALL / PARETO
--
-- DO NOT treat a citation, DOI, source network edge, DDC, QID, or
-- Pareto rank as importing a theorem.  Reuse the ORIGINAL attributed
-- source and snowball attribution owners, with explicitly open
-- geometric and Lean/Agda kernel obligations.
--
-- Primary source objects inspected 2026-10-25:
--   Richards 1963, DOI 10.2307/1993768\n--   Brahana 1921, DOI 10.2307/1968030 (prior compact surface source)\n--   Kerekjarto 1923, DOI from later digital edition 2013
--   Fox--Artin 1948, DOI 10.2307/1969408
--   Yoneyama 1917, original Tohoku Math J publication (no DOI
--     verified by this atlas)
--   Bombieri--De Giorgi--Giusti 1969, DOI 10.1007/BF01404309
--   Mardesic 1978 ICM survey (no DOI verified by this atlas)
--   Hatcher textbook (no DOI verified by this atlas)
--   Jack McCarthy's Hatcher-at Lean sphere homology module,
--     different toolchain/Mathlib revision from DASHI.
--
-- The first-link route is a DOCUMENT/DONOR traversal, NOT evidence
-- that every citation edge implies a dependency or a proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as A
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snow

richardsOriginal : A.AttributedSource
richardsOriginal = A.mkDOISource
  "Ian Richards"
  "On the Classification of Noncompact Surfaces"
  "Transactions of the American Mathematical Society 106(2), 259-269"
  "1963"
  "10.2307/1993768"
  "https://doi.org/10.2307/1993768"
  A.academicArticleSource
  "primary owner: classified surfaces by orientability, genus, ideal-boundary/end data; not imported without surface realisation and a suitable formal classification theorem"
  A.publicAttribution

foxArtinOriginal : A.AttributedSource
foxArtinOriginal = A.mkDOISource
  "Ralph H. Fox; Emil Artin"
  "Some Wild Cells and Spheres in Three-Dimensional Space"
  "Annals of Mathematics 49(4), 979-990"
  "1948"
  "10.2307/1969408"
  "https://doi.org/10.2307/1969408"
  A.academicArticleSource
  "primary owner for wild arcs: Example 1.1* nontrivial complement pi1; Example 1.2 wild with open-3-cell complement; Example 1.3 trivial complement pi1 but not open-3-cell; global pi1 does not certify all local wildness"
  A.publicAttribution

yoneyamaOriginal : A.AttributedSource
yoneyamaOriginal = A.mkNoDOISource
  "Kunizo Yoneyama"
  "Theory of Continuous Set of Points (not finished)"
  "Tohoku Mathematical Journal, First Series 12, 43-158"
  "1917"
  "https://www.jstage.jst.go.jp/article/tmj1911/12/0/12_0_43/_article"
  A.academicArticleSource
  "historical publication of the classical common-boundary lakes construction attributed to Wada; source does not imply current DASHI domains satisfy frontier equality"
  A.publicAttribution

bombieriDeGiorgiGiustiOriginal : A.AttributedSource
bombieriDeGiorgiGiustiOriginal = A.mkDOISource
  "Enrico Bombieri; Ennio De Giorgi; Enrico Giusti"
  "Minimal Cones and the Bernstein Problem"
  "Inventiones Mathematicae 7, 243-268"
  "1969"
  "10.1007/BF01404309"
  "https://doi.org/10.1007/BF01404309"
  A.academicArticleSource
  "primary minimising-cone theorem donor; Simons polynomial/gradient/link calculation is not a calibration or minimality proof"
  A.publicAttribution

mardesicShapeSurvey : A.AttributedSource
mardesicShapeSurvey = A.mkNoDOISource
  "Sibe Mardesic"
  "Shape Theory"
  "Proceedings of the International Congress of Mathematicians, Helsinki"
  "1978"
  "https://citeseerx.ist.psu.edu/document?doi=1689fd7674a0d927b89aad5f68c1cfa6456d01d4&repid=rep1&type=pdf"
  A.academicArticleSource
  "historical shape-theory survey: Warsaw circle weak homotopy versus noncontractibility; this survey is NOT an original proof of Borsuk's underlying shape theory"
  A.publicAttribution

hatcherBook : A.AttributedSource
hatcherBook = A.mkNoDOISource
  "Allen Hatcher"
  "Algebraic Topology"
  "Cambridge University Press; freely distributed author text"
  "2002"
  "https://pi.math.cornell.edu/~hatcher/AT/AT.pdf"
  A.academicBookSource
  "classical sphere, CW and algebraic-topology theorem source; geometric theorem must retain its own Lean/Agda proof or separately typechecked import"
  A.publicAttribution

mccarthyLeanSphere : A.AttributedSource
mccarthyLeanSphere = A.mkNoDOISource
  "Jack McCarthy"
  "Hatcher/Sphere/Homology.lean: reducedHomology_sphere"
  "Deicyde/hatcher-at; Mathlib/Lean v4.34.1 source"
  "2026"
  "https://github.com/Deicyde/hatcher-at/blob/main/Hatcher/Sphere/Homology.lean"
  A.namedSourceKind "Lean proof implementation"
  "source-written and upstream-checked sphere reduced-homology supplier on TopCat.sphere; local DASHI v4.28.0 reduced-to-ordinary and kernel revision join still required"
  A.publicAttribution


-- Snowball from Richards' own bibliography: these are NOT 1963
-- discoveries. Richards (p. 260) credits the compact bordered-surface
-- theorem to Brahana and describes Kerékjártó's earlier classification
-- outline (noting gaps and providing a corrected argument).
brahanaOriginal : A.AttributedSource
brahanaOriginal = A.mkDOISource
  "H. R. Brahana"
  "Systems of Circuits on Two-Dimensional Manifolds"
  "Annals of Mathematics 23(2), 144-168"
  "1921"
  "10.2307/1968030"
  "https://doi.org/10.2307/1968030"
  A.academicArticleSource
  "older primary source, credited by Richards for compact bordered-surface classification; owner of genus/Euler/boundary finite stage classification"
  A.publicAttribution

kerekjartoOriginal : A.AttributedSource
kerekjartoOriginal = A.mkDOISource
  "Bela Kerekjarto"
  "Vorlesungen uber Topologie: I, Flachentopologie"
  "Springer, Grundlehren der mathematischen Wissenschaften 8"
  "1923; digital eBook DOI edition 2013"
  "10.1007/978-3-642-50825-7"
  "https://doi.org/10.1007/978-3-642-50825-7"
  A.academicBookSource
  "older ideal-boundary/noncompact-surface classification ancestor according to Richards; DOI belongs to the 2013 electronic reissue, NOT the 1923 printed object; Richards notes earlier proof gaps"
  A.publicAttribution

originalsAndImplementation : List A.AttributedSource
originalsAndImplementation =
  richardsOriginal ∷
  brahanaOriginal ∷
  kerekjartoOriginal ∷
  foxArtinOriginal ∷
  yoneyamaOriginal ∷
  bombieriDeGiorgiGiustiOriginal ∷
  mardesicShapeSurvey ∷
  hatcherBook ∷
  mccarthyLeanSphere ∷ []

originalCount : A.sourceCount originalsAndImplementation ≡ 9
originalCount = refl

exoticTopologyAtlas : A.AttributedSourceAtlas
exoticTopologyAtlas = A.mkSourceAtlas
  "Exotic topology original-root / implementation-donor atlas"
  "DASHI.Mathematics.Topology.ExoticSourceGenealogyParetoExact"
  originalsAndImplementation
  "source roots, proof implementations and missing source-specific same-object tests; DOI bibliographic identity does not grant theorem use"

attributionDoesNotPromote :
  (validation : String) →
  Receipt.promotesClaim
    (A.attributedSourceAtlasReceipt exoticTopologyAtlas validation)
  ≡ false
attributionDoesNotPromote = A.attributedSourceAtlasReceiptNonPromoting exoticTopologyAtlas

richardsSnowballReceipt : Snow.SourceRoleSnowballReceipt richardsOriginal
richardsSnowballReceipt = Snow.canonicalSourceRoleSnowballReceipt richardsOriginal

foxArtinSnowballReceipt : Snow.SourceRoleSnowballReceipt foxArtinOriginal
foxArtinSnowballReceipt = Snow.canonicalSourceRoleSnowballReceipt foxArtinOriginal

hatcherSnowballReceipt : Snow.SourceRoleSnowballReceipt mccarthyLeanSphere
hatcherSnowballReceipt = Snow.canonicalSourceRoleSnowballReceipt mccarthyLeanSphere

------------------------------------------------------------------------
-- Typed, CONSUMER-DRIVEN first-link routing. Not a proof dependency.
------------------------------------------------------------------------

data PaymentStatus : Set where
  primaryRootLocated : PaymentStatus
  consumerBuiltConditional : PaymentStatus
  geometricSameObjectOpen : PaymentStatus
  kernelImportOpen : PaymentStatus

record TopologyParetoLeaf : Set where
  constructor topologyParetoLeaf
  field
    rank : Nat
    primary : A.AttributedSource
    donor : String
    consumer : String
    remainingReceipt : String
    fanout : String
    status : PaymentStatus
    doiOrIdentifierNotProof : Bool
    rankNotProof : Bool
open TopologyParetoLeaf public

sphereHomologyLeaf : TopologyParetoLeaf
sphereHomologyLeaf = topologyParetoLeaf
  1 mccarthyLeanSphere
  "dashi_lean4 native CP1≃TopCat.sphere 2 + Hatcher-at reducedHomology_sphere"
  "Synthesis.ExoticTopologyCP1SphereH2Acceptance"
  "pin-reconciled ordinary/reduced rational H2 comparison and actual import or separately kernel-checked port at exact Mathlib revision"
  "CP1/S2 homology, finite cellular-to-singular comparison, sphere CW consumers"
  kernelImportOpen true false

richardsRealisationLeaf : TopologyParetoLeaf
richardsRealisationLeaf = topologyParetoLeaf
  2 richardsOriginal
  "actual marked PL pants/handle triangulations and vertex transport; source-written Lean CompatibleCantorTower inverse limit reusing Integration.Address"
  "Cantor tree / Jacob's ladder / Loch Ness monster"
  "finite manifold and every-old-frontier ancestry now source-written; NEXT actual collared direct-limit 2-manifold, Richards same-object end homeomorphism, decorated genus/nonplanar end proof, kernel-recognised classification"
  "three noncompact surfaces and their decorated end types; conditional end-space argument in Docs/topology/ExoticInfiniteSurfaceEndSpaceConditionalTheorem20261025.md"
  geometricSameObjectOpen true false

foxArtinGeometricLeaf : TopologyParetoLeaf
foxArtinGeometricLeaf = topologyParetoLeaf
  3 foxArtinOriginal
  "Alexander horned C3 PR #1244 finite horn embeddings/commutators"
  "Fox--Artin wild arc / wild knot"
  "literal Example 1.1* chain-stitch nested embedding (nontrivial complement pi1), then Example 1.2 local neighborhood inclusion maps and Example 1.3 trivial global pi1 but non-3-cell complement; do not identify these separate source examples"
  "wild arcs, wild knots, ambient Schoenflies obstruction"
  geometricSameObjectOpen true false

warsawShapeLeaf : TopologyParetoLeaf
warsawShapeLeaf = topologyParetoLeaf
  4 mardesicShapeSurvey
  "dashi_lean4 literal real sine-closure WarsawCircleSpace"
  "Warsaw weak-contractibility / non-CW type"
  "vertical closure and continuum proofs, vanishing homotopy groups, noncontractibility via proper shape/Čech comparison"
  "CW/Whitehead negative-control family"
  geometricSameObjectOpen true false

wadaCommonBoundaryLeaf : TopologyParetoLeaf
wadaCommonBoundaryLeaf = topologyParetoLeaf
  5 yoneyamaOriginal
  "dashi_lean4 WadaThreeDomains and Agda C3-incidence no-go"
  "Lakes of Wada"
  "actual three connected disjoint planar open domains and a proved common nonempty frontier"
  "planar wild boundaries; equivariance not sufficient"
  geometricSameObjectOpen true false

simonsMinimalityLeaf : TopologyParetoLeaf
simonsMinimalityLeaf = topologyParetoLeaf
  6 bombieriDeGiorgiGiustiOriginal
  "native Simons polynomial, spherical link and singular-gradient algebra"
  "area-minimising Simons cone"
  "geometric measure theory: currents/calibration/area minimality, not merely singular-link equations"
  "minimal cones, singular GMT and geometric variation"
  geometricSameObjectOpen true false

paretoLeafCount : Nat
paretoLeafCount = 6

-- Routing metadata never imports mathematical proofs.
allLeavesRemainConsumerSpecific : Bool
allLeavesRemainConsumerSpecific = true

unresolvedQID : String
unresolvedQID = "not inspected for this source atlas; no substitute QID"

unresolvedDewey : String
unresolvedDewey = "not inspected for these source objects; no fabricated DDC"
