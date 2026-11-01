module DASHI.Physics.Foundations.Round5SourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.ConsciousAccessRound5ExtendedSourceAtlas as ExistingRound5Sources

------------------------------------------------------------------------
-- Attributed source atlas.  Every entry records what is imported and what is
-- deliberately not promoted from the citation.

record SourceRecord : Set where
  constructor sourceRecord
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    importedRole : String
    excludedPromotion : String

open SourceRecord public

buckinghamSource : SourceRecord
buckinghamSource =
  sourceRecord
    "E. Buckingham"
    "On Physically Similar Systems; Illustrations of the Use of Dimensional Equations"
    "Physical Review"
    1914
    "10.1103/PhysRev.4.345"
    "Supports reduction of unit-covariant quantities to dimensionless combinations."
    "Dimensional analysis alone does not derive interaction coefficients or realised constants."

wilsonRGSource : SourceRecord
wilsonRGSource =
  sourceRecord
    "Kenneth G. Wilson"
    "The Renormalization Group: Critical Phenomena and the Kondo Problem"
    "Reviews of Modern Physics"
    1975
    "10.1103/RevModPhys.47.773"
    "Supports fixed points, relevant directions, marginal variables, and scale-dependent effective descriptions."
    "The finite RG examples are not a nonperturbative continuum construction of the Standard Model."

informationGeometrySource : SourceRecord
informationGeometrySource =
  sourceRecord
    "Nihat Ay; Juergen Jost; Hong Van Le; Lorenz Schwachhoefer"
    "Information Geometry"
    "Springer"
    2017
    "10.1007/978-3-319-56478-4"
    "Supports treating parameterisations geometrically and using Fisher-type invariant metrics."
    "No physical constant is selected merely by naming a statistical metric."

kolmogorovComplexitySource : SourceRecord
kolmogorovComplexitySource =
  sourceRecord
    "Ming Li; Paul Vitanyi"
    "An Introduction to Kolmogorov Complexity and Its Applications"
    "Texts in Computer Science, Springer"
    2019
    "10.1007/978-3-030-11298-1"
    "Supports machine-relative description length, invariance up to additive translation constants, and precision-sensitive coding."
    "A finite candidate score is not promoted to an absolute machine-independent law of the universe."

causalSetSource : SourceRecord
causalSetSource =
  sourceRecord
    "Sumati Surya"
    "The Causal Set Approach to Quantum Gravity"
    "Living Reviews in Relativity"
    2019
    "10.1007/s41114-019-0023-1"
    "Supports causal order, local finiteness, dimension estimators, and continuum-approximation obligations."
    "Causal order and local finiteness are not promoted to a proof that spacetime is four-dimensional."

hohenbergKohnSource : SourceRecord
hohenbergKohnSource =
  sourceRecord
    "P. Hohenberg; W. Kohn"
    "Inhomogeneous Electron Gas"
    "Physical Review"
    1964
    "10.1103/PhysRev.136.B864"
    "Supports configuration-dependent electronic ground-state functionals beyond independent orbital labels."
    "The finite atomic score is not identified with the exact density functional."

kohnShamSource : SourceRecord
kohnShamSource =
  sourceRecord
    "W. Kohn; L. J. Sham"
    "Self-Consistent Equations Including Exchange and Correlation Effects"
    "Physical Review"
    1965
    "10.1103/PhysRev.140.A1133"
    "Supports self-consistent one-particle equations and interaction-dependent orbital ordering."
    "The toy shell ordering is not a calibrated Kohn-Sham calculation."

mayerShellSource : SourceRecord
mayerShellSource =
  sourceRecord
    "Maria Goeppert Mayer"
    "On Closed Shells in Nuclei. II"
    "Physical Review"
    1949
    "10.1103/PhysRev.75.1969"
    "Supports nuclear shell closure with strong spin-orbit structure."
    "Pauli exclusion or kernel cardinality alone is not asserted to derive empirical magic numbers."

haxelJensenSuessSource : SourceRecord
haxelJensenSuessSource =
  sourceRecord
    "Otto Haxel; J. Hans D. Jensen; Hans E. Suess"
    "On the Magic Numbers in Nuclear Structure"
    "Physical Review"
    1949
    "10.1103/PhysRev.75.1766.2"
    "Supports the operator-dependent shell explanation of nuclear magic numbers."
    "The finite closure witness is not a full nuclear mean-field calculation."

bcsPairingSource : SourceRecord
bcsPairingSource =
  sourceRecord
    "J. Bardeen; L. N. Cooper; J. R. Schrieffer"
    "Theory of Superconductivity"
    "Physical Review"
    1957
    "10.1103/PhysRev.108.1175"
    "Supports pairing as a dynamical consequence of an attractive channel rather than of exclusion alone."
    "The finite nuclear pairing parity model is not identified with microscopic BCS nuclear theory."

bohrWheelerSource : SourceRecord
bohrWheelerSource =
  sourceRecord
    "Niels Bohr; John Archibald Wheeler"
    "The Mechanism of Nuclear Fission"
    "Physical Review"
    1939
    "10.1103/PhysRev.56.426"
    "Supports fission as deformation and barrier competition in a charged finite drop."
    "The finite Nat-valued shape cost is not a quantitative fission-barrier prediction."

cabacSource : SourceRecord
cabacSource =
  sourceRecord
    "Detlev Marpe; Heiko Schwarz; Thomas Wiegand"
    "Context-Based Adaptive Binary Arithmetic Coding in the H.264/AVC Video Compression Standard"
    "IEEE Transactions on Circuits and Systems for Video Technology"
    2003
    "10.1109/TCSVT.2003.815173"
    "Supports forward-decodable adaptive context modelling and arithmetic coding."
    "CABAC is not promoted to a literal cosmological dynamics or a global MDL optimiser by itself."

yangMillsSource : SourceRecord
yangMillsSource =
  sourceRecord
    "C. N. Yang; R. L. Mills"
    "Conservation of Isotopic Spin and Isotopic Gauge Invariance"
    "Physical Review"
    1954
    "10.1103/PhysRev.96.191"
    "Supports local non-Abelian gauge redundancy, connection data, and curvature targets."
    "A finite graph holonomy witness is not promoted to continuum Yang-Mills theory."

fockSecondQuantisationSource : SourceRecord
fockSecondQuantisationSource =
  sourceRecord
    "V. A. Fock"
    "Konfigurationsraum und zweite Quantelung"
    "Zeitschrift fuer Physik"
    1932
    "10.1007/BF01344458"
    "Supports variable-particle-number state spaces and bosonic/fermionic occupation sectors."
    "The finite truncated occupation tables are not promoted to a completed Fock representation or canonical field algebra."

osterwalderSchraderSource : SourceRecord
osterwalderSchraderSource =
  sourceRecord
    "Konrad Osterwalder; Robert Schrader"
    "Axioms for Euclidean Green's Functions"
    "Communications in Mathematical Physics"
    1973
    "10.1007/BF01645738"
    "Supports reflection-positivity and reconstruction obligations for Euclidean quantum fields."
    "Reflection positivity is not inferred from finite algebraic amplitudes."

weinbergLeptonsSource : SourceRecord
weinbergLeptonsSource =
  sourceRecord
    "Steven Weinberg"
    "A Model of Leptons"
    "Physical Review Letters"
    1967
    "10.1103/PhysRevLett.19.1264"
    "Supports the specificity of electroweak gauge and representation content."
    "Naming SU(3) x SU(2) x U(1) does not derive chiral matter, Yukawa data, or anomaly cancellation."

planckCosmologySource : SourceRecord
planckCosmologySource =
  sourceRecord
    "Planck Collaboration"
    "Planck 2018 Results. VI. Cosmological Parameters"
    "Astronomy and Astrophysics"
    2020
    "10.1051/0004-6361/201833910"
    "Supports treating the CMB as an observational constraint on cosmological parameters."
    "The observed CMB sky is not promoted to a lossless global microstate or Cauchy surface."

canonicalRound5Sources : List SourceRecord
canonicalRound5Sources =
  buckinghamSource
  ∷ wilsonRGSource
  ∷ informationGeometrySource
  ∷ kolmogorovComplexitySource
  ∷ causalSetSource
  ∷ hohenbergKohnSource
  ∷ kohnShamSource
  ∷ mayerShellSource
  ∷ haxelJensenSuessSource
  ∷ bcsPairingSource
  ∷ bohrWheelerSource
  ∷ cabacSource
  ∷ yangMillsSource
  ∷ fockSecondQuantisationSource
  ∷ osterwalderSchraderSource
  ∷ weinbergLeptonsSource
  ∷ planckCosmologySource
  ∷ []

sourceCount : List SourceRecord → Nat
sourceCount [] = 0
sourceCount (_ ∷ sources) = suc (sourceCount sources)

canonicalRound5SourceCount : Nat
canonicalRound5SourceCount = sourceCount canonicalRound5Sources

canonicalRound5SourceCountIsSeventeen :
  canonicalRound5SourceCount ≡ 17
canonicalRound5SourceCountIsSeventeen = refl

existingBiologyRound5SourceCountIsTwentyThree :
  ExistingRound5Sources.canonicalRound5ExtendedSourceCount ≡ 23
existingBiologyRound5SourceCountIsTwentyThree =
  ExistingRound5Sources.canonicalRound5ExtendedSourceCountIsTwentyThree
