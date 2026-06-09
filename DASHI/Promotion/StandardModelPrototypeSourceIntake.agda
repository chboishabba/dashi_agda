module DASHI.Promotion.StandardModelPrototypeSourceIntake where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Standard Model prototype source intake.
--
-- This module records two cross-repo implementation surfaces that are useful
-- for the SM/Higgs/Yukawa/coupling frontier:
--
--   * ../dashiQ/naw.py: a toy MSSM/Higgs/RG/downward/upward scan scaffold.
--   * ../FRACDASH: executable paired-prime/FRACTRAN bridge and invariant
--     artifacts.
--
-- The purpose is source intake and routing.  These prototypes do not promote
-- Standard Model, QFT observable, empirical, chemistry, stellar, or terminal
-- claims.

data PrototypeRepo : Set where
  dashiQRepo :
    PrototypeRepo

  fracdashRepo :
    PrototypeRepo

repoLabel :
  PrototypeRepo →
  String
repoLabel dashiQRepo =
  "../dashiQ"
repoLabel fracdashRepo =
  "../FRACDASH"

data PrototypeStatus : Set where
  executableToyProxy :
    PrototypeStatus

  formalBridgeArtifact :
    PrototypeStatus

  documentedIntakeSurface :
    PrototypeStatus

statusLabel :
  PrototypeStatus →
  String
statusLabel executableToyProxy =
  "executable toy/proxy"
statusLabel formalBridgeArtifact =
  "formal bridge artifact"
statusLabel documentedIntakeSurface =
  "documented intake surface"

record PrototypeSourceRow : Set where
  field
    sourceRepo :
      PrototypeRepo

    sourcePath :
      String

    sourceStatus :
      PrototypeStatus

    sourceStatusLabel :
      String

    sourceStatusLabelIsCanonical :
      sourceStatusLabel ≡ statusLabel sourceStatus

    sourceRole :
      String

    usefulFor :
      String

    promotionBoundary :
      String

    theoremAuthority :
      Bool

    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

open PrototypeSourceRow public

mkPrototypeSourceRow :
  PrototypeRepo →
  String →
  PrototypeStatus →
  String →
  String →
  String →
  PrototypeSourceRow
mkPrototypeSourceRow repo path status role useful boundary =
  record
    { sourceRepo = repo
    ; sourcePath = path
    ; sourceStatus = status
    ; sourceStatusLabel = statusLabel status
    ; sourceStatusLabelIsCanonical = refl
    ; sourceRole = role
    ; usefulFor = useful
    ; promotionBoundary = boundary
    ; theoremAuthority = false
    ; theoremAuthorityIsFalse = refl
    }

canonicalDashiQPrototypeRows :
  List PrototypeSourceRow
canonicalDashiQPrototypeRows =
  mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py"
    executableToyProxy
    "M6-style MSSM Higgs scan over g1/g2 with stop-scale and mixing argmax"
    "Higgs/Yukawa/gauge-coupling frontier routing"
    "toy Higgs objective only; not FeynHiggs/SoftSUSY/SPheno authority"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:MatterLayer"
    executableToyProxy
    "clopen matter-layer strata with 1-loop beta-coefficient shifts and thresholds"
    "SM uniqueness and vectorlike-matter countermodel boundary"
    "illustrative strata; not an adopted physical alternative"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:run_gauge_1loop"
    executableToyProxy
    "piecewise 1-loop gauge coupling runner in alpha inverse space"
    "gauge-coupling/running authority frontier"
    "requires scheme, threshold, beta-function, and PDG/CODATA authority"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:mh_toy_mssm"
    executableToyProxy
    "toy MSSM Higgs mass proxy with tree term plus stop correction"
    "Higgs mass target and SUSY dial exploration"
    "not a physical Higgs mass derivation or accepted spectrum calculation"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:yukawas_from_gauge_and_tanb_toy"
    executableToyProxy
    "toy first-generation Yukawa proxy from gauge couplings and tan beta"
    "Yukawa hierarchy and mass-basis frontier"
    "not a carrier-derived Yukawa matrix or CKM/PMNS theorem"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:nuclear_stability_from_yukawas_toy"
    executableToyProxy
    "toy neutron-proton, deuteron, and hydrogen stability diagnostics"
    "downward propagation from SM-ish parameters to nuclear checks"
    "requires chiral EFT/lattice/empirical authority before physical use"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:chemistry_window_toy"
    executableToyProxy
    "toy chemistry window over alpha and electron-to-proton mass ratio"
    "chemistry-facing consequence routing"
    "not physical chemistry, spectroscopy, bonding, or wet-lab validation"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:stellar_fusion_window_pp_toy"
    executableToyProxy
    "toy pp-chain stellar-fusion viability gate"
    "stellar consequence routing from parameter bundles"
    "not a stellar-structure model or empirical stellar validation"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:evaluate_bundle_at_point"
    executableToyProxy
    "single-fiber UV-to-IR gauge, Higgs, Yukawa, nuclear, chemistry, and stellar bundle"
    "unified parameter-to-consequence prototype surface"
    "proxy-only; no accepted authority or QFT observable bridge"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw.py:compute_fields_per_layer"
    executableToyProxy
    "full g1/g2 field runner over clopen matter layers"
    "finite scan harness for future authority-backed consumers"
    "scan output is diagnostic, not theorem evidence"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw2.py"
    executableToyProxy
    "3D MSSM base over g1/g2/g3 with intersected Higgs, chemistry, and stellar gates"
    "admissible-volume and boundary-manifold routing for Higgs/SM scans"
    "toy scalar field and gates; not a physical MSSM spectrum calculation"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/naw2.py:marching_cubes"
    executableToyProxy
    "extracts the boundary of the admissible Higgs/chemistry/stellar intersection"
    "geometric boundary surface for future calibrated parameter scans"
    "topological visualization only until calibrated constraints are supplied"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/13tev.py"
    executableToyProxy
    "ATLAS H to gamma gamma 13 TeV full-covariance MDL shape-complexity analysis"
    "empirical observable bridge and covariance-aware Higgs data intake"
    "Path C shape-complexity result; not SM-relative without a theory baseline"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/pseudo_data_harness.py"
    executableToyProxy
    "pseudo-data harness using real ATLAS covariance and controlled injections"
    "detectability thresholds for tilt, curvature, lines, dimension, two-regime, and anisotropy"
    "calibrates inference machinery; not an observed new-physics or SM-derivation result"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/reusable_query.py"
    executableToyProxy
    "HEPData query and reusable table intake helper"
    "provider discovery for SM-template and covariance-bearing observable records"
    "provider lookup helper only; accepted authority still requires checksums and versioned payloads"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/resolve_hepdata_record.py"
    executableToyProxy
    "HEPData record resolver for Higgs/differential datasets"
    "authority-source discovery for ATLAS/CMS SM observable bridges"
    "record discovery only, not authority-token acceptance"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/METHODS.md"
    documentedIntakeSurface
    "formalizes allowed-vs-supported structure, MDL truncation, and constant-atlas mechanics"
    "claim discipline for SM Lagrangian versus empirically supported observable subspace"
    "method note only; does not derive SM parameters"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/CONTEXT.md:Path-A/B/C"
    documentedIntakeSurface
    "records that full-covariance ATLAS data is present while the ideal SM-relative baseline is still missing"
    "empirical promotion blocker for SM-relative deformation claims"
    "contextual decision surface, not checked theorem authority"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/gpt_experiments/topology_sweep_mssm_mh.csv"
    executableToyProxy
    "saved MSSM Higgs topology sweep artifact"
    "evidence of prior Higgs/MSSM parameter-surface exploration"
    "unversioned experiment artifact; not authority-backed physical evidence"
  ∷ mkPrototypeSourceRow
    dashiQRepo
    "/home/c/Documents/code/dashiQ/gpt_experiments/isosurface_geometry_diagnostics.npz"
    executableToyProxy
    "saved isosurface geometry diagnostics for the MSSM/Higgs admissible surface"
    "geometric diagnostics for future calibrated manifold intake"
    "diagnostic artifact only until source script, parameters, and calibration are receipted"
  ∷ []

canonicalFRACDASHPrototypeRows :
  List PrototypeSourceRow
canonicalFRACDASHPrototypeRows =
  mkPrototypeSourceRow
    fracdashRepo
    "/home/c/Documents/code/FRACDASH/AGDAS_FORMALISM_INTAKE.md"
    documentedIntakeSurface
    "maps upstream dashi_agda closure/audit owners into FRACDASH hooks"
    "cross-repo source-of-truth and executable-surrogate separation"
    "does not collapse upstream theorem owners into local executables"
  ∷ mkPrototypeSourceRow
    fracdashRepo
    "/home/c/Documents/code/FRACDASH/CURRENT_FORMAL_RESULT.md"
    documentedIntakeSurface
    "states the current generic macro bridge and numeric closed-family split"
    "paired-prime execution and regime-valid bridge intake"
    "not downstream physics interpretation or SM derivation"
  ∷ mkPrototypeSourceRow
    fracdashRepo
    "/home/c/Documents/code/FRACDASH/formalism/GenericMacroBridge.agda"
    formalBridgeArtifact
    "class-indexed structural FRACTRAN macro bridge"
    "runtime/replay and finite carrier execution support"
    "not QFT, SM, Higgs, or empirical authority"
  ∷ mkPrototypeSourceRow
    fracdashRepo
    "/home/c/Documents/code/FRACDASH/formalism/BridgeInstances.agda"
    formalBridgeArtifact
    "numeric theorem layer for the currently closed slice family"
    "bounded transmutation and residual-decrease bridge support"
    "slice-family theorem only; no terminal unification"
  ∷ mkPrototypeSourceRow
    fracdashRepo
    "/home/c/Documents/code/FRACDASH/PHYSICS_INVARIANT_TARGETS.md"
    documentedIntakeSurface
    "locked physics invariant target suite and widened-family taxonomy"
    "observable-surrogate and invariant comparison support"
    "physics-facing interpretation remains bridge-local"
  ∷ mkPrototypeSourceRow
    fracdashRepo
    "/home/c/Documents/code/FRACDASH/benchmarks/results/2026-03-23-physics22-baseline-delta.json"
    executableToyProxy
    "physics22 recurrent-core baseline-delta artifact"
    "finite carrier comparison and future scan baseline"
    "artifact evidence only, not a physical-law derivation"
  ∷ mkPrototypeSourceRow
    fracdashRepo
    "/home/c/Documents/code/FRACDASH/benchmarks/results/2026-03-23-cross-carrier-baseline-summary.json"
    executableToyProxy
    "cross-carrier physics22 versus carrier8 baseline summary"
    "carrier-width comparison for runtime/prototype routing"
    "not a replacement for known-physics translation"
  ∷ []

canonicalPrototypeSourceRows :
  List PrototypeSourceRow
canonicalPrototypeSourceRows =
  canonicalDashiQPrototypeRows ++ canonicalFRACDASHPrototypeRows
  where
    _++_ : List PrototypeSourceRow → List PrototypeSourceRow → List PrototypeSourceRow
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

rowCount :
  List PrototypeSourceRow →
  Nat
rowCount [] =
  zero
rowCount (_ ∷ xs) =
  suc (rowCount xs)

record StandardModelPrototypeSourceIntakeReceipt : Setω where
  field
    dashiQRows :
      List PrototypeSourceRow

    dashiQRowsAreCanonical :
      dashiQRows ≡ canonicalDashiQPrototypeRows

    dashiQRowCount :
      Nat

    dashiQRowCountIsTwenty :
      dashiQRowCount ≡ 20

    fracdashRows :
      List PrototypeSourceRow

    fracdashRowsAreCanonical :
      fracdashRows ≡ canonicalFRACDASHPrototypeRows

    fracdashRowCount :
      Nat

    fracdashRowCountIsSeven :
      fracdashRowCount ≡ 7

    allRows :
      List PrototypeSourceRow

    allRowsAreCanonical :
      allRows ≡ canonicalPrototypeSourceRows

    allRowCount :
      Nat

    allRowCountIsTwentySeven :
      allRowCount ≡ 27

    dashiQSourcePath :
      String

    fracdashSourceRoot :
      String

    toyProxyOnly :
      Bool

    toyProxyOnlyIsTrue :
      toyProxyOnly ≡ true

    prototypeTheoremAuthorityAccepted :
      Bool

    prototypeTheoremAuthorityAcceptedIsFalse :
      prototypeTheoremAuthorityAccepted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

open StandardModelPrototypeSourceIntakeReceipt public

canonicalStandardModelPrototypeSourceIntakeReceipt :
  StandardModelPrototypeSourceIntakeReceipt
canonicalStandardModelPrototypeSourceIntakeReceipt =
  record
    { dashiQRows =
        canonicalDashiQPrototypeRows
    ; dashiQRowsAreCanonical =
        refl
    ; dashiQRowCount =
        rowCount canonicalDashiQPrototypeRows
    ; dashiQRowCountIsTwenty =
        refl
    ; fracdashRows =
        canonicalFRACDASHPrototypeRows
    ; fracdashRowsAreCanonical =
        refl
    ; fracdashRowCount =
        rowCount canonicalFRACDASHPrototypeRows
    ; fracdashRowCountIsSeven =
        refl
    ; allRows =
        canonicalPrototypeSourceRows
    ; allRowsAreCanonical =
        refl
    ; allRowCount =
        rowCount canonicalPrototypeSourceRows
    ; allRowCountIsTwentySeven =
        refl
    ; dashiQSourcePath =
        "/home/c/Documents/code/dashiQ/naw.py"
    ; fracdashSourceRoot =
        "/home/c/Documents/code/FRACDASH"
    ; toyProxyOnly =
        true
    ; toyProxyOnlyIsTrue =
        refl
    ; prototypeTheoremAuthorityAccepted =
        false
    ; prototypeTheoremAuthorityAcceptedIsFalse =
        refl
    ; standardModelPromoted =
        false
    ; standardModelPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    }

canonicalPrototypeDashiQRowCountIsTwenty :
  dashiQRowCount canonicalStandardModelPrototypeSourceIntakeReceipt ≡ 20
canonicalPrototypeDashiQRowCountIsTwenty =
  refl

canonicalPrototypeFRACDASHRowCountIsSeven :
  fracdashRowCount canonicalStandardModelPrototypeSourceIntakeReceipt ≡ 7
canonicalPrototypeFRACDASHRowCountIsSeven =
  refl

canonicalPrototypeAllRowCountIsTwentySeven :
  allRowCount canonicalStandardModelPrototypeSourceIntakeReceipt ≡ 27
canonicalPrototypeAllRowCountIsTwentySeven =
  refl

canonicalPrototypeDoesNotPromoteStandardModel :
  standardModelPromoted canonicalStandardModelPrototypeSourceIntakeReceipt
  ≡
  false
canonicalPrototypeDoesNotPromoteStandardModel =
  refl

canonicalPrototypeDoesNotPromoteTerminalUnification :
  terminalUnificationPromoted canonicalStandardModelPrototypeSourceIntakeReceipt
  ≡
  false
canonicalPrototypeDoesNotPromoteTerminalUnification =
  refl
