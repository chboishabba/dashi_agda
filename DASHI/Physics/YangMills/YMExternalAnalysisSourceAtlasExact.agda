module DASHI.Physics.YangMills.YMExternalAnalysisSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EXTERNAL ANALYSIS / YM SOURCE ATTRIBUTION
--
-- These sources calibrate imported mathematical/physical authorities.  They do
-- not inhabit the repo's conditional interfaces or identify the literal DASHI
-- physical carrier without separate same-object receipts.
------------------------------------------------------------------------

kato1966 : Source.AttributedSource
kato1966 =
  Source.mkDOISource
    "Tosio Kato"
    "Perturbation Theory for Linear Operators"
    "Springer, Grundlehren der mathematischen Wissenschaften 132"
    "1966"
    "10.1007/978-3-662-12678-3"
    "https://doi.org/10.1007/978-3-662-12678-3"
    Source.academicBookSource
    "source for the classical representation theory of densely defined closed semibounded sesquilinear forms and associated self-adjoint operators; citation alone does not inhabit the YM Kato authority interface"
    Source.publicAttribution

prokhorov1956 : Source.AttributedSource
prokhorov1956 =
  Source.mkDOISource
    "Yu. V. Prokhorov"
    "Convergence of Random Processes and Limit Theorems in Probability Theory"
    "Theory of Probability and Its Applications 1(2), 157-214"
    "1956"
    "10.1137/1101016"
    "https://doi.org/10.1137/1101016"
    Source.academicArticleSource
    "source for the tightness/relative-compactness theorem family used by the continuum-measure extraction authority; citation does not establish DASHI topology hypotheses or a cluster-point theorem on the selected physical measure sequence"
    Source.publicAttribution

balaban1984 : Source.AttributedSource
balaban1984 =
  Source.mkDOISource
    "Tadeusz Balaban"
    "Propagators and renormalization transformations for lattice gauge theories. I"
    "Communications in Mathematical Physics 95, 17-40"
    "1984"
    "10.1007/BF01215753"
    "https://doi.org/10.1007/BF01215753"
    Source.academicArticleSource
    "source calibration for Balaban lattice-gauge renormalization-group machinery; it does not identify the repo diagonalMeasure with finiteVolumeMeasure nor supply current same-object/coercivity/topology leaves"
    Source.publicAttribution

record YMExternalSourceBoundary : Set where
  constructor ym-external-source-boundary
  field
    katoCitationInhabitsAuthority : Bool
    katoCitationInhabitsAuthorityIsFalse : katoCitationInhabitsAuthority ≡ false
    prokhorovCitationCreatesSelectedTopologyTightness : Bool
    prokhorovCitationCreatesSelectedTopologyTightnessIsFalse :
      prokhorovCitationCreatesSelectedTopologyTightness ≡ false
    balabanCitationCreatesDiagonalFiniteVolumeSameObject : Bool
    balabanCitationCreatesDiagonalFiniteVolumeSameObjectIsFalse :
      balabanCitationCreatesDiagonalFiniteVolumeSameObject ≡ false

canonicalYMExternalSourceBoundary : YMExternalSourceBoundary
canonicalYMExternalSourceBoundary =
  ym-external-source-boundary false refl false refl false refl
