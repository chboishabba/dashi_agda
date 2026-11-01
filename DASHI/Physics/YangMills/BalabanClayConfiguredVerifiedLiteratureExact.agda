module DASHI.Physics.YangMills.BalabanClayConfiguredVerifiedLiteratureExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Structured provenance added by the configured analytic tranche.
--
-- A source entry records calibration or proof architecture only.  No entry is
-- imported as a theorem inhabitant.  Unverified completion claims remain in
-- BalabanClayLiteralFrontierQuarantinedClaims and are absent from this list.
------------------------------------------------------------------------

record ConfiguredLiteratureSource : Set where
  constructor configuredSource
  field
    authors : String
    title : String
    venueYear : String
    doi : String
    arxiv : String
    theoremOrSection : String
    relationship : String

open ConfiguredLiteratureSource public

daumasLesterMunoz : ConfiguredLiteratureSource
daumasLesterMunoz = configuredSource
  "Marc Daumas, David Lester and César Muñoz"
  "Verified Real Number Calculations: A Library for Interval Arithmetic"
  "IEEE Transactions on Computers 58 (2009), 226--237"
  "10.1109/TC.2008.213"
  "arXiv:0708.3721"
  "elementary-function enclosures, interval splitting and Taylor evaluation"
  "proof-assistant precedent for DASHI rational interval certificates"

solaDerayAtchuthan : ConfiguredLiteratureSource
solaDerayAtchuthan = configuredSource
  "Joan Solà, Jérémie Deray and Dinesh Atchuthan"
  "A micro Lie theory for state estimation in robotics"
  "arXiv preprint (2018)"
  "No journal DOI assigned in arXiv:1812.01537"
  "arXiv:1812.01537"
  "SO(3) exponential and left/right Jacobian formula tables"
  "independent convention check for the right-Jacobian chart carrier"

dybalskiStottmeisterTanimotoGreen : ConfiguredLiteratureSource
dybalskiStottmeisterTanimotoGreen = configuredSource
  "Wojciech Dybalski, Alexander Stottmeister and Yoh Tanimoto"
  "Lattice Green Functions for Pedestrians: Exponential Decay"
  "Reviews in Mathematical Physics 36 (2024), article 2430005"
  "10.1142/S0129055X2430005X"
  "arXiv:2303.10754"
  "Theorem A / Theorem 2.25; Combes--Thomas, Fourier analyticity, RG equation and images"
  "primary modern architecture for uniform finite-volume Green decay"

combesThomas : ConfiguredLiteratureSource
combesThomas = configuredSource
  "Jean-Michel Combes and Lawrence Thomas"
  "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger Operators"
  "Communications in Mathematical Physics 34 (1973), 251--270"
  "10.1007/BF01646473"
  ""
  "weighted resolvent conjugation estimate"
  "source of the local spectral-gap-to-exponential-decay mechanism"

balaban1987TheoremArchitecture : ConfiguredLiteratureSource
balaban1987TheoremArchitecture = configuredSource
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Communications in Mathematical Physics 109 (1987), 249--301"
  "10.1007/BF01215223"
  ""
  "Introduction, pp. 249--260; Theorems 1--2 and Eqs. (0.22)--(0.31)"
  "architectural template for conditional small-field control and the beta,beta-prime running-coupling endpoint; Theorem 2's perturbative proof is explicitly deferred"

balaban1987LocalizationMetric : ConfiguredLiteratureSource
balaban1987LocalizationMetric = configuredSource
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Communications in Mathematical Physics 109 (1987), 249--301"
  "10.1007/BF01215223"
  ""
  "Introduction, Eqs. (0.24)--(0.27), including the tree-graph size d_j(X) and exp(-kappa d_j(X)) decay"
  "literal localization-domain and collar/tree-size convention for T2 patch and polymer norms"

balaban1987WardVacuumPolarization : ConfiguredLiteratureSource
balaban1987WardVacuumPolarization = configuredSource
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Communications in Mathematical Physics 109 (1987), 249--301"
  "10.1007/BF01215223"
  ""
  "Sections 4--5, pp. 281--298; Eqs. (5.36)--(5.41)"
  "Ward-identity, transverse-kernel and mixed-Laurent-derivative falsification target; not an imported coefficient proof"

simonTraceIdeals : ConfiguredLiteratureSource
simonTraceIdeals = configuredSource
  "Barry Simon"
  "Trace Ideals and Their Applications, Second Edition"
  "American Mathematical Society, Mathematical Surveys and Monographs 120 (2005)"
  "10.1090/surv/120"
  ""
  "trace-class products, determinants and trace-log series"
  "analytic mechanism for the localized fluctuation determinant lane"

wilsonConfinement : ConfiguredLiteratureSource
wilsonConfinement = configuredSource
  "Kenneth G. Wilson"
  "Confinement of Quarks"
  "Physical Review D 10 (1974), 2445--2459"
  "10.1103/PhysRevD.10.2445"
  ""
  "Wilson lattice action"
  "normalization source for the literal background-field vertex expansion"

faddeevPopov : ConfiguredLiteratureSource
faddeevPopov = configuredSource
  "Ludwig D. Faddeev and Victor N. Popov"
  "Feynman Diagrams for the Yang--Mills Field"
  "Physics Letters B 25 (1967), 29--30"
  "10.1016/0370-2693(67)90067-6"
  ""
  "ghost determinant and gauge-fixing diagrammatics"
  "conceptual source; the lattice ghost operator is derived from DASHI's fixed gauge convention"

abbottBackgroundField : ConfiguredLiteratureSource
abbottBackgroundField = configuredSource
  "Luis F. Abbott"
  "The Background Field Method Beyond One Loop"
  "Nuclear Physics B 185 (1981), 189--203"
  "10.1016/0550-3213(81)90371-0"
  ""
  "background-field Ward structure"
  "continuum comparison source for gauge-invariant coupling extraction"

chatterjeeYangMillsForProbabilists : ConfiguredLiteratureSource
chatterjeeYangMillsForProbabilists = configuredSource
  "Sourav Chatterjee"
  "Yang--Mills for Probabilists"
  "Probability and Analysis in Interacting Physical Systems (2019), 1--16"
  "10.1007/978-3-030-15338-0_1"
  "arXiv:1803.01950"
  "survey of rigorous lattice Yang--Mills results and open construction problems"
  "orientation source only; it supplies no missing DASHI estimate"

gopfertMack : ConfiguredLiteratureSource
gopfertMack = configuredSource
  "Markus Göpfert and Gerhard Mack"
  "Proof of Confinement of Static Quarks in Three-Dimensional U(1) Lattice Gauge Theory for All Values of the Coupling Constant"
  "Communications in Mathematical Physics 82 (1982), 545--606"
  "10.1007/BF01961240"
  ""
  "explicit nonperturbative lattice-gauge constant bookkeeping"
  "abelian three-dimensional calibration only; not a Yang--Mills input"

configuredVerifiedLiterature : List ConfiguredLiteratureSource
configuredVerifiedLiterature =
  daumasLesterMunoz ∷
  solaDerayAtchuthan ∷
  dybalskiStottmeisterTanimotoGreen ∷
  combesThomas ∷
  balaban1987TheoremArchitecture ∷
  balaban1987LocalizationMetric ∷
  balaban1987WardVacuumPolarization ∷
  simonTraceIdeals ∷
  wilsonConfinement ∷
  faddeevPopov ∷
  abbottBackgroundField ∷
  chatterjeeYangMillsForProbabilists ∷
  gopfertMack ∷ []
