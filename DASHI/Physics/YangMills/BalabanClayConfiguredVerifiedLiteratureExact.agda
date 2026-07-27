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
  chatterjeeYangMillsForProbabilists ∷
  gopfertMack ∷ []
