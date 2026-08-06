module DASHI.Visualisation.EventPadicSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Sources for event kernels, filament/ridge extraction, fixed-point feedback,
-- direct volume rendering, p-adic hierarchy, conditional expectation, and
-- Morton-like Euclidean observation.  Every record includes an explicit
-- authority boundary for the finite Agda witnesses.

silvermanDensitySource : Sources.SourceRecord
silvermanDensitySource =
  Sources.sourceRecord
    "Bernard W. Silverman"
    "Density Estimation for Statistics and Data Analysis"
    "Routledge / Chapman and Hall"
    1986
    "10.1201/9781315140919"
    "Supports additive kernel-density fields, bandwidth semantics, and the distinction between kernel scale and observed density."
    "The finite Nat kernel tables are not a statistically calibrated density estimator or consistency theorem."

ozertemErdogmusRidgeSource : Sources.SourceRecord
ozertemErdogmusRidgeSource =
  Sources.sourceRecord
    "Umut Ozertem; Deniz Erdogmus"
    "Locally Defined Principal Curves and Surfaces"
    "Journal of Machine Learning Research 12"
    2011
    "No DOI assigned; JMLR 12(34):1249-1286"
    "Supports Hessian-eigenspace definitions of local principal curves and surfaces."
    "The finite ridge-codimension witness is not a smooth ridge-existence or statistical-recovery theorem."

genoveseRidgeSource : Sources.SourceRecord
genoveseRidgeSource =
  Sources.sourceRecord
    "Christopher R. Genovese; Marco Perone-Pacifico; Isabella Verdinelli; Larry Wasserman"
    "Nonparametric Ridge Estimation"
    "Annals of Statistics"
    2014
    "10.1214/14-AOS1218"
    "Supports density-ridge estimation, stability, and codimension-sensitive normal conditions."
    "No inferred rendered filament is promoted to an observed cognitive trajectory."

levoyVolumeSource : Sources.SourceRecord
levoyVolumeSource =
  Sources.sourceRecord
    "Marc Levoy"
    "Display of Surfaces from Volume Data"
    "IEEE Computer Graphics and Applications"
    1988
    "10.1109/38.511"
    "Supports transfer functions, sampled volume observation, and front-to-back compositing semantics."
    "A finite opacity table is not a calibrated optical or radiative-transfer model."

maxOpticalSource : Sources.SourceRecord
maxOpticalSource =
  Sources.sourceRecord
    "Nelson Max"
    "Optical Models for Direct Volume Rendering"
    "IEEE Transactions on Visualization and Computer Graphics"
    1995
    "10.1109/2945.468400"
    "Supports keeping emission, absorption, opacity, and display polarity as separate rendering choices."
    "The finite renderer does not solve the continuum volume-rendering integral."

banachFixedPointSource : Sources.SourceRecord
banachFixedPointSource =
  Sources.sourceRecord
    "Stefan Banach"
    "Sur les operations dans les ensembles abstraits et leur application aux equations integrales"
    "Fundamenta Mathematicae"
    1922
    "10.4064/fm-3-1-133-181"
    "Supports existence, uniqueness, and iteration convergence under a proved contraction."
    "The finite three-state fixed-point example is not a contraction proof for the continuum self-sharpening renderer."

mortonOrderingSource : Sources.SourceRecord
mortonOrderingSource =
  Sources.sourceRecord
    "G. M. Morton"
    "A Computer Oriented Geodetic Data Base and a New Technique in File Sequencing"
    "IBM Canada Technical Report"
    1966
    "No DOI assigned; IBM technical report"
    "Supports digit-interleaving and Morton-like spatial indexing as an observation layout."
    "The ternary interleaving map is not promoted to an ultrametric isometry or canonical p-adic embedding."

serreArithmeticReuseSource : Sources.SourceRecord
serreArithmeticReuseSource =
  Sources.sourceRecord
    "Jean-Pierre Serre"
    "A Course in Arithmetic"
    "Graduate Texts in Mathematics 7, Springer"
    1973
    "10.1007/978-1-4684-9884-4"
    "Supports finite residues, inverse-limit completions, and the distinction between project address syntax and p-adic numerals."
    "Finite ternary prefixes are not claimed to implement the complete analytic theory of Z_3."

robertPadicReuseSource : Sources.SourceRecord
robertPadicReuseSource =
  Sources.sourceRecord
    "Alain M. Robert"
    "A Course in p-adic Analysis"
    "Graduate Texts in Mathematics 198, Springer"
    2000
    "10.1007/978-1-4757-3254-2"
    "Supports p-adic continuity, ultrametric cylinders, local constancy, and finite-prefix approximation."
    "The Euclidean render image is not identified with the intrinsic p-adic state space."

williamsMartingaleSource : Sources.SourceRecord
williamsMartingaleSource =
  Sources.sourceRecord
    "David Williams"
    "Probability with Martingales"
    "Cambridge University Press"
    1991
    "10.1017/CBO9780511813658"
    "Supports conditional expectation, filtration-consistent coarse approximation, and martingale zoom semantics."
    "The finite three-child average certificate is not a measure-theoretic martingale convergence theorem."

canonicalEventPadicSources : List Sources.SourceRecord
canonicalEventPadicSources =
  silvermanDensitySource
  ∷ ozertemErdogmusRidgeSource
  ∷ genoveseRidgeSource
  ∷ levoyVolumeSource
  ∷ maxOpticalSource
  ∷ banachFixedPointSource
  ∷ mortonOrderingSource
  ∷ serreArithmeticReuseSource
  ∷ robertPadicReuseSource
  ∷ williamsMartingaleSource
  ∷ []

eventPadicSourceCount : List Sources.SourceRecord → Nat
eventPadicSourceCount [] = 0
eventPadicSourceCount (_ ∷ sources) =
  suc (eventPadicSourceCount sources)

canonicalEventPadicSourceCount : Nat
canonicalEventPadicSourceCount =
  eventPadicSourceCount canonicalEventPadicSources

canonicalEventPadicSourceCountIsTen :
  canonicalEventPadicSourceCount ≡ 10
canonicalEventPadicSourceCountIsTen = refl
