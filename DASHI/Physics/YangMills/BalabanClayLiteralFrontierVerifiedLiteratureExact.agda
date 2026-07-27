module DASHI.Physics.YangMills.BalabanClayLiteralFrontierVerifiedLiteratureExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Structured provenance for the literal T2--T5 frontier.
--
-- This module is the canonical metadata owner imported by the producer bundle.
-- It records authors, exact titles, venue/year, DOI or arXiv identifier, the
-- section/equation actually used, and the relationship of the source to DASHI.
-- A source is calibration or architecture, never an automatic proof inhabitant.
------------------------------------------------------------------------

record LiteratureSource : Set where
  constructor source
  field
    authors : String
    title : String
    venueYear : String
    doi : String
    arxiv : String
    sectionEquation : String
    relationship : String

open LiteratureSource public

balabanPropagatorsI : LiteratureSource
balabanPropagatorsI = source
  "Tadeusz Bałaban"
  "Propagators and Renormalization Transformations for Lattice Gauge Theories. I"
  "Communications in Mathematical Physics 95 (1984), 17--40"
  "10.1007/BF01215753"
  ""
  "quadratic action, gauge fixing, propagator regularity and decay"
  "primary architecture and normalization target for the reference Hessian"

balabanPropagatorsII : LiteratureSource
balabanPropagatorsII = source
  "Tadeusz Bałaban"
  "Propagators and Renormalization Transformations for Lattice Gauge Theories. II"
  "Communications in Mathematical Physics 96 (1984), 223--250"
  "10.1007/BF01240221"
  ""
  "many-scale restrictions and local/exponential propagator bounds"
  "primary architecture for scale-, volume- and patch-uniform Green estimates"

balabanAveraging : LiteratureSource
balabanAveraging = source
  "Tadeusz Bałaban"
  "Averaging Operations for Lattice Gauge Theories"
  "Communications in Mathematical Physics 98 (1985), 17--51"
  "10.1007/BF01211042"
  ""
  "analyticity and regularity of lattice gauge averaging operations"
  "primary source for the nonlinear block-map and constraint derivative lane"

balabanBackgroundPropagator : LiteratureSource
balabanBackgroundPropagator = source
  "Tadeusz Bałaban"
  "Propagators for Lattice Gauge Theories in a Background Field"
  "Communications in Mathematical Physics 99 (1985), 389--434"
  "10.1007/BF01240355"
  ""
  "background expansion, regularity, random-walk representation and decay"
  "primary falsification target for the five background-Hessian estimates"

balabanUltraviolet3D : LiteratureSource
balabanUltraviolet3D = source
  "Tadeusz Bałaban"
  "Ultraviolet Stability of Three-Dimensional Lattice Pure Gauge Field Theories"
  "Communications in Mathematical Physics 102 (1985), 255--275"
  "10.1007/BF01229380"
  ""
  "small/large field split and Wilson-action suppression"
  "primary architecture for the activity gain-minus-loss ledger"

balabanVariational : LiteratureSource
balabanVariational = source
  "Tadeusz Bałaban"
  "The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories"
  "Communications in Mathematical Physics 102 (1985), 277--309"
  "10.1007/BF01229381"
  ""
  "constrained minimum, uniqueness modulo gauge and background regularity"
  "primary target for the literal background construction"

balabanRGI : LiteratureSource
balabanRGI = source
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Communications in Mathematical Physics 109 (1987), 249--301"
  "10.1007/BF01215223"
  ""
  "Sections 4--5; Ward--Takahashi identities, vacuum polarization, beta functions; Eq. (5.36) is the tensor-structure comparison target"
  "primary one-step RG and vacuum-polarization falsification target"

balabanRGII : LiteratureSource
balabanRGII = source
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. II. Cluster Expansions"
  "Communications in Mathematical Physics 116 (1988), 1--22"
  "10.1007/BF01239022"
  ""
  "exponentiated fluctuation-field cluster expansion"
  "primary thermodynamic-locality and connected-tail architecture"

dashenGross : LiteratureSource
dashenGross = source
  "Roger Dashen and David J. Gross"
  "Relationship between Lattice and Continuum Definitions of the Gauge-Theory Coupling"
  "Physical Review D 23 (1981), 2340--2344"
  "10.1103/PhysRevD.23.2340"
  ""
  "weak background lattice field and Wilson-action coupling calibration"
  "normalization cross-check; not a replacement for the exact RG coefficient proof"

goswamiVariational : LiteratureSource
goswamiVariational = source
  "Abhishek Goswami"
  "The Variational Problem and Background Field in the Renormalization Group Method for Nonlinear Sigma Models"
  "Annales Henri Poincaré 25 (2024), 2065--2085"
  "10.1007/s00023-023-01353-7"
  "arXiv:2204.08252"
  "single-scale nonlinear-sigma variational construction"
  "modern explanatory analogue; not the source of arXiv:2403.09800"

dybalskiStottmeisterTanimoto : LiteratureSource
dybalskiStottmeisterTanimoto = source
  "Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto"
  "The Bałaban Variational Problem in the Non-Linear Sigma Model"
  "arXiv preprint (14 March 2024)"
  "No DOI assigned in arXiv:2403.09800v1"
  "arXiv:2403.09800v1"
  "Sections 3--4 and Appendix A; critical equation, positivity and random-walk Green bounds"
  "modern explanatory analogue; model-specific Yang--Mills estimates remain DASHI obligations"

barfootStateEstimation : LiteratureSource
barfootStateEstimation = source
  "Timothy D. Barfoot"
  "State Estimation for Robotics"
  "Cambridge University Press (2017)"
  "10.1017/9781316671528"
  ""
  "SO(3) exponential, left/right Jacobians and inverse formulas"
  "convention calibration for the literal chart singular-value proof"

hallLieGroups : LiteratureSource
hallLieGroups = source
  "Brian C. Hall"
  "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction"
  "Second edition, Springer (2015)"
  "10.1007/978-3-319-13467-3"
  ""
  "finite-dimensional exponential and adjoint identities"
  "general Lie-theoretic calibration; SU(2) constants are derived separately"

simonTraceIdeals : LiteratureSource
simonTraceIdeals = source
  "Barry Simon"
  "Trace Ideals and Their Applications"
  "Second edition, American Mathematical Society (2005)"
  "10.1090/surv/120"
  ""
  "trace ideals, determinants and trace-log bounds"
  "operator-theoretic architecture for the localized determinant lane"

blanesCasasOteoRos1998 : LiteratureSource
blanesCasasOteoRos1998 = source
  "Sergio Blanes, Fernando Casas, José A. Oteo and José Ros"
  "Magnus and Fer Expansions for Matrix Differential Equations: The Convergence Problem"
  "Journal of Physics A: Mathematical and General 31 (1998), 259--268"
  "10.1088/0305-4470/31/1/023"
  ""
  "explicit convergence and truncation-error estimates"
  "generic Magnus/BCH sanity check; not the sharp SU(2) quaternion owner"

blanesCasas2004 : LiteratureSource
blanesCasas2004 = source
  "Sergio Blanes and Fernando Casas"
  "On the Convergence and Optimization of the Baker--Campbell--Hausdorff Formula"
  "Linear Algebra and its Applications 378 (2004), 135--158"
  "10.1016/j.laa.2003.09.010"
  ""
  "BCH convergence domains and optimized truncations"
  "generic comparison radius for the plaquette logarithm"

blanesCasasOteoRos2009 : LiteratureSource
blanesCasasOteoRos2009 = source
  "Sergio Blanes, Fernando Casas, José A. Oteo and José Ros"
  "The Magnus Expansion and Some of Its Applications"
  "Physics Reports 470 (2009), 151--238"
  "10.1016/j.physrep.2008.11.001"
  ""
  "review of convergence, effective exponentials and applications"
  "expository and comparison source only"

deyLonigroYuasaBurgarth : LiteratureSource
deyLonigroYuasaBurgarth = source
  "Anirban Dey, Davide Lonigro, Kazuya Yuasa and Daniel Burgarth"
  "Error Bounds for the Floquet--Magnus Expansion and Their Application to the Semiclassical Quantum Rabi Model"
  "Physical Review A 112 (2025), 053723"
  "10.1103/6bgj-s987"
  "arXiv:2504.20533"
  "explicit finite-order effective-dynamics error bounds"
  "recent comparison source; not imported into the SU(2) plaquette proof"

koteckyPreiss : LiteratureSource
koteckyPreiss = source
  "Roman Kotecký and David Preiss"
  "Cluster Expansion for Abstract Polymer Models"
  "Communications in Mathematical Physics 103 (1986), 491--498"
  "10.1007/BF01211762"
  ""
  "polymer convergence criterion"
  "abstract convergence theorem instantiated only after literal activity and incompatibility proofs"

fernandezProcacci : LiteratureSource
fernandezProcacci = source
  "Roberto Fernández and Aldo Procacci"
  "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old Approach"
  "Communications in Mathematical Physics 274 (2007), 123--140"
  "10.1007/s00220-007-0279-2"
  "arXiv:math-ph/0605041"
  "Penrose identity and improved neighborhood partition function"
  "source of the clique partition-function criterion and the 1/12 comparison"

bissacotFernandezProcacci : LiteratureSource
bissacotFernandezProcacci = source
  "Rodrigo Bissacot, Roberto Fernández and Aldo Procacci"
  "On the Convergence of Cluster Expansions for Polymer Gases"
  "Journal of Statistical Physics 139 (2010), 598--617"
  "10.1007/s10955-010-9956-1"
  "arXiv:1002.3261"
  "criterion comparison and subset-polymer specialization"
  "source for keeping KP, Dobrushin, GK and sharper combinatorial criteria distinct"

osterwalderSchraderI : LiteratureSource
osterwalderSchraderI = source
  "Konrad Osterwalder and Robert Schrader"
  "Axioms for Euclidean Green's Functions"
  "Communications in Mathematical Physics 31 (1973), 83--112"
  "10.1007/BF01645738"
  ""
  "OS axioms and reconstruction target"
  "continuum Schwinger-function specification"

osterwalderSchraderII : LiteratureSource
osterwalderSchraderII = source
  "Konrad Osterwalder and Robert Schrader"
  "Axioms for Euclidean Green's Functions II"
  "Communications in Mathematical Physics 42 (1975), 281--305"
  "10.1007/BF01608978"
  ""
  "corrected necessary and sufficient reconstruction conditions"
  "continuum topology and reconstruction target"

menottiPelissetto : LiteratureSource
menottiPelissetto = source
  "Pietro Menotti and Andrea Pelissetto"
  "General Proof of Osterwalder-Schrader Positivity for the Wilson Action"
  "Communications in Mathematical Physics 113 (1987), 369--373"
  "10.1007/BF01221251"
  ""
  "finite-lattice Wilson reflection positivity"
  "finite-cutoff positivity input transported by complete Gram-form convergence"

verifiedLiteralFrontierSources : List LiteratureSource
verifiedLiteralFrontierSources =
  balabanPropagatorsI ∷
  balabanPropagatorsII ∷
  balabanAveraging ∷
  balabanBackgroundPropagator ∷
  balabanUltraviolet3D ∷
  balabanVariational ∷
  balabanRGI ∷
  balabanRGII ∷
  dashenGross ∷
  goswamiVariational ∷
  dybalskiStottmeisterTanimoto ∷
  barfootStateEstimation ∷
  hallLieGroups ∷
  simonTraceIdeals ∷
  blanesCasasOteoRos1998 ∷
  blanesCasas2004 ∷
  blanesCasasOteoRos2009 ∷
  deyLonigroYuasaBurgarth ∷
  koteckyPreiss ∷
  fernandezProcacci ∷
  bissacotFernandezProcacci ∷
  osterwalderSchraderI ∷
  osterwalderSchraderII ∷
  menottiPelissetto ∷ []

------------------------------------------------------------------------
-- Explicit correction map for two legacy comment typos encountered during the
-- branch audit.  Canonical provenance consumers must use the corrected values.
------------------------------------------------------------------------

propagatorsILegacyTypo correctedPropagatorsIDoi : String
propagatorsILegacyTypo = "10.1007/BF01215757"
correctedPropagatorsIDoi = "10.1007/BF01215753"

ultraviolet3DLegacyTypo correctedUltraviolet3DDoi : String
ultraviolet3DLegacyTypo = "10.1007/BF01229381"
correctedUltraviolet3DDoi = "10.1007/BF01229380"
