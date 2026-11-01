module DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (List; []; _∷_; _++_)

------------------------------------------------------------------------
-- Photonuclear / LHC empirical constants registry.
--
-- This surface records the reduced surrogate defaults, model parameters, and
-- example-derived constants used by the photonuclear prototype. It is
-- intentionally a registry, not a physics claim: provenance is explicit and
-- every entry carries a boundary tag so downstream code can tell "used as
-- input" from "claimed as established result".

data ClaimBoundary : Set where
  surrogateInput : ClaimBoundary
  exampleDerivedInput : ClaimBoundary
  documentationOnly : ClaimBoundary
  notPhysicsClaim : ClaimBoundary

data ParameterFamily : Set where
  sharedRunnerDefaults : ParameterFamily
  gbwSurrogateFamily : ParameterFamily
  ipsatSurrogateFamily : ParameterFamily
  exampleStateFamily : ParameterFamily

record RegistryEntry : Set₁ where
  field
    family : ParameterFamily
    key : String
    value : String
    provenance : List String
    boundary : ClaimBoundary

mkEntry :
  ParameterFamily →
  String →
  String →
  List String →
  ClaimBoundary →
  RegistryEntry
mkEntry family key value provenance boundary =
  record
    { family = family
    ; key = key
    ; value = value
    ; provenance = provenance
    ; boundary = boundary
    }

record ParameterFamilyRegistry : Set₁ where
  field
    family : ParameterFamily
    familyBoundary : ClaimBoundary
    familyProvenance : List String
    constants : List RegistryEntry

mkFamily :
  ParameterFamily →
  ClaimBoundary →
  List String →
  List RegistryEntry →
  ParameterFamilyRegistry
mkFamily family familyBoundary familyProvenance constants =
  record
    { family = family
    ; familyBoundary = familyBoundary
    ; familyProvenance = familyProvenance
    ; constants = constants
    }

record PhotonuclearConstantsRegistry : Set₁ where
  field
    registryBoundary : ClaimBoundary
    sharedDefaults : ParameterFamilyRegistry
    gbwParameters : ParameterFamilyRegistry
    ipsatParameters : ParameterFamilyRegistry
    exampleStates : ParameterFamilyRegistry

registryEntries :
  PhotonuclearConstantsRegistry →
  List RegistryEntry
registryEntries registry =
  ParameterFamilyRegistry.constants
    (PhotonuclearConstantsRegistry.sharedDefaults registry)
  ++ ParameterFamilyRegistry.constants
    (PhotonuclearConstantsRegistry.gbwParameters registry)
  ++ ParameterFamilyRegistry.constants
    (PhotonuclearConstantsRegistry.ipsatParameters registry)
  ++ ParameterFamilyRegistry.constants
    (PhotonuclearConstantsRegistry.exampleStates registry)

entryCount : List RegistryEntry → Nat
entryCount [] = zero
entryCount (_ ∷ xs) = suc (entryCount xs)

familyEntryCount : ParameterFamilyRegistry → Nat
familyEntryCount familyRegistry =
  entryCount (ParameterFamilyRegistry.constants familyRegistry)

registryEntryCount : PhotonuclearConstantsRegistry → Nat
registryEntryCount registry =
  familyEntryCount (PhotonuclearConstantsRegistry.sharedDefaults registry)
  + familyEntryCount (PhotonuclearConstantsRegistry.gbwParameters registry)
  + familyEntryCount (PhotonuclearConstantsRegistry.ipsatParameters registry)
  + familyEntryCount (PhotonuclearConstantsRegistry.exampleStates registry)

photonuclearConstantsRegistry : PhotonuclearConstantsRegistry
photonuclearConstantsRegistry =
  record
    { registryBoundary = notPhysicsClaim
    ; sharedDefaults =
        mkFamily
          sharedRunnerDefaults
          surrogateInput
          ( "scripts/prototype_runner.py::RunnerConfig"
          ∷ "Docs/NumericObservableInterface.md::prototype interface"
          ∷ []
          )
          ( mkEntry
              sharedRunnerDefaults
              "lambda_gbw"
              "0.3"
              ( "scripts/prototype_runner.py::RunnerConfig.lambda_gbw"
              ∷ "Docs/GBWResponse.md::GBW-inspired response"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "x0"
              "1.0e-3"
              ( "scripts/prototype_runner.py::RunnerConfig.x0"
              ∷ "Docs/GBWResponse.md::GBW-inspired response"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "sigma0"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.sigma0"
              ∷ "scripts/prototype_gbw.py::GBWParameters.sigma0"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "thickness"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.thickness"
              ∷ "Docs/GBWResponse.md::T_A"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "normalization_d0"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.normalization_d0"
              ∷ "Docs/GBWResponse.md::N_D0"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "sqrt_s"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.sqrt_s"
              ∷ "Docs/GBWResponse.md::x_ref"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "mdl_lambda"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.mdl_lambda"
              ∷ "Docs/NumericObservableInterface.md::g_star"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "alpha_qs"
              "0.5"
              ( "scripts/prototype_runner.py::RunnerConfig.alpha_qs"
              ∷ "Docs/NumericObservableInterface.md::Q_s"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              sharedRunnerDefaults
              "defect_floor"
              "1.0e-9"
              ( "scripts/prototype_runner.py::RunnerConfig.defect_floor"
              ∷ "scripts/prototype_gbw.py::GBWParameters.defect_floor"
              ∷ "scripts/prototype_ipsat.py::IPsatParameters.defect_floor"
              ∷ []
              )
              surrogateInput
          ∷ []
          )
    ; gbwParameters =
        mkFamily
          gbwSurrogateFamily
          surrogateInput
          ( "scripts/prototype_gbw.py::GBWParameters"
          ∷ "Docs/GBWResponse.md::GBW-inspired response"
          ∷ "Docs/SaturationLayer.md::GBW"
          ∷ []
          )
          ( mkEntry
              gbwSurrogateFamily
              "lambda_gbw"
              "0.3"
              ( "scripts/prototype_runner.py::RunnerConfig.lambda_gbw"
              ∷ "scripts/prototype_gbw.py::GBWParameters.lambda_gbw"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              gbwSurrogateFamily
              "x0"
              "1.0e-3"
              ( "scripts/prototype_runner.py::RunnerConfig.x0"
              ∷ "scripts/prototype_gbw.py::GBWParameters.x0"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              gbwSurrogateFamily
              "sigma0"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.sigma0"
              ∷ "scripts/prototype_gbw.py::GBWParameters.sigma0"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              gbwSurrogateFamily
              "thickness"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.thickness"
              ∷ "scripts/prototype_gbw.py::GBWParameters.thickness"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              gbwSurrogateFamily
              "normalization_d0"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.normalization_d0"
              ∷ "scripts/prototype_gbw.py::GBWParameters.normalization_d0"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              gbwSurrogateFamily
              "sqrt_s"
              "1.0"
              ( "scripts/prototype_runner.py::RunnerConfig.sqrt_s"
              ∷ "scripts/prototype_gbw.py::GBWParameters.sqrt_s"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              gbwSurrogateFamily
              "defect_floor"
              "1.0e-9"
              ( "scripts/prototype_runner.py::RunnerConfig.defect_floor"
              ∷ "scripts/prototype_gbw.py::GBWParameters.defect_floor"
              ∷ []
              )
              surrogateInput
          ∷ []
          )
    ; ipsatParameters =
        mkFamily
          ipsatSurrogateFamily
          surrogateInput
          ( "scripts/prototype_ipsat.py::IPsatParameters"
          ∷ "Docs/SaturationLayer.md::IPsat"
          ∷ []
          )
          ( mkEntry
              ipsatSurrogateFamily
              "lambda_ipsat"
              "0.3"
              ( "scripts/prototype_matrix.py::GBW/IPsat shared lambda"
              ∷ "scripts/prototype_ipsat.py::IPsatParameters.lambda_ipsat"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              ipsatSurrogateFamily
              "x0"
              "1.0e-3"
              ( "scripts/prototype_ipsat.py::IPsatParameters.x0"
              ∷ "Docs/SaturationLayer.md::IPsat"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              ipsatSurrogateFamily
              "sigma0"
              "1.0"
              ( "scripts/prototype_ipsat.py::IPsatParameters.sigma0"
              ∷ "Docs/SaturationLayer.md::IPsat"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              ipsatSurrogateFamily
              "alpha_s"
              "0.2"
              ( "scripts/prototype_ipsat.py::IPsatParameters.alpha_s"
              ∷ "scripts/compare_surrogate_models.py::ipsat_response(alpha_s=0.2)"
              ∷ "Docs/SaturationLayer.md::IPsat"
              ∷ []
              )
              documentationOnly
          ∷ mkEntry
              ipsatSurrogateFamily
              "thickness"
              "1.0"
              ( "scripts/prototype_ipsat.py::IPsatParameters.thickness"
              ∷ "Docs/SaturationLayer.md::IPsat"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              ipsatSurrogateFamily
              "normalization_d0"
              "1.0"
              ( "scripts/prototype_ipsat.py::IPsatParameters.normalization_d0"
              ∷ "Docs/GBWResponse.md::N_D0"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              ipsatSurrogateFamily
              "sqrt_s"
              "1.0"
              ( "scripts/prototype_ipsat.py::IPsatParameters.sqrt_s"
              ∷ "Docs/GBWResponse.md::x_ref"
              ∷ []
              )
              surrogateInput
          ∷ mkEntry
              ipsatSurrogateFamily
              "defect_floor"
              "1.0e-9"
              ( "scripts/prototype_ipsat.py::IPsatParameters.defect_floor"
              ∷ "scripts/prototype_gbw.py::GBWParameters.defect_floor"
              ∷ []
              )
              surrogateInput
          ∷ []
          )
    ; exampleStates =
        mkFamily
          exampleStateFamily
          exampleDerivedInput
          ( "scripts/examples/near_miss_state.json"
          ∷ "scripts/examples/head_on_state.json"
          ∷ "scripts/emit_shift_prototype_examples.py"
          ∷ []
          )
          ( mkEntry
              exampleStateFamily
              "photon_energy"
              "0.22"
              ( "scripts/examples/near_miss_state.json"
              ∷ "scripts/examples/head_on_state.json"
              ∷ "scripts/prototype_schema.py::DashiStateSchema.photon_energy"
              ∷ "Docs/NumericObservableInterface.md::omega_photon"
              ∷ []
              )
              exampleDerivedInput
          ∷ mkEntry
              exampleStateFamily
              "delta"
              "[1.0,0.0,0.0,0.0]"
              ( "scripts/examples/near_miss_state.json"
              ∷ "scripts/emit_shift_prototype_examples.py::canonical shell1"
              ∷ []
              )
              exampleDerivedInput
          ∷ mkEntry
              exampleStateFamily
              "coarse_head"
              "[1.0]"
              ( "scripts/examples/near_miss_state.json"
              ∷ "scripts/examples/head_on_state.json"
              ∷ "scripts/emit_shift_prototype_examples.py"
              ∷ []
              )
              exampleDerivedInput
          ∷ []
          )
    }

open PhotonuclearConstantsRegistry public
