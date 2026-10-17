module DASHI.Unified.TOEOpenAIMathAcceleratorExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unified.TOESectorRealizationExact

data ExternalFormalAuthority : Set where
  manuscriptOnly : ExternalFormalAuthority
  upstreamLeanDeclaration : ExternalFormalAuthority
  upstreamKernelReceipt : ExternalFormalAuthority
  dashiLeanPort : ExternalFormalAuthority
  dashiLeanKernelReceipt : ExternalFormalAuthority
  importedFormalSource : ExternalFormalAuthority
  agdaTheorem : ExternalFormalAuthority

openAIMaxAuthority : ExternalFormalAuthority
openAIMaxAuthority = importedFormalSource

data TheoremRouteClass : Set where
  directSameObjectCandidate : TheoremRouteClass
  lemmaDonor : TheoremRouteClass
  structuralDonor : TheoremRouteClass
  independentCrossCheck : TheoremRouteClass
  backgroundOnly : TheoremRouteClass

record OpenAITheoremRoute : Set where
  field
    family : String
    upstreamModule : String
    upstreamDeclaration : String
    targetTOELeaf : String
    routeClass : TheoremRouteClass
    authority : ExternalFormalAuthority
    sameObjectTransportPaid : Bool
    sameObjectTransportPaidIsFalse : sameObjectTransportPaid ≡ false
    reading : String
open OpenAITheoremRoute public

route :
  String → String → String → String → TheoremRouteClass → String →
  OpenAITheoremRoute
route family moduleName declaration target classification reading =
  record
    { family = family
    ; upstreamModule = moduleName
    ; upstreamDeclaration = declaration
    ; targetTOELeaf = target
    ; routeClass = classification
    ; authority = importedFormalSource
    ; sameObjectTransportPaid = false
    ; sameObjectTransportPaidIsFalse = refl
    ; reading = reading
    }

quasiRiemannHeckeRoute : OpenAITheoremRoute
quasiRiemannHeckeRoute =
  route "003"
    "OAI.NumberTheory.DirichletL.Nonvanishing"
    "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re"
    "RH analytic leaf and Q(sqrt(-3)) Hecke/Eisenstein-CM continuation"
    lemmaDonor
    "The upstream formalization includes the 7/8 zero-free result and related Dirichlet/finite-order Hecke material. It is a theorem donor/cross-check, not RH closure and not automatically the same j=0 Hecke character."

optimalMaxCutRoute : OpenAITheoremRoute
optimalMaxCutRoute =
  route "102"
    "OAI.Computability.MaxCut.Main"
    "OAI.OptimalMaxCut.main"
    "complexity/P-vs-NP and finite combinatorial reduction infrastructure"
    structuralDonor
    "Optimal Max-Cut hardness can feed the complexity realization/tooling lane; it is not a P!=NP theorem."

vlasovMaxwellRoute : OpenAITheoremRoute
vlasovMaxwellRoute =
  route "362"
    "OAI.Analysis.VlasovMaxwell.Main"
    "OAI.RVM.global_classical_solution"
    "electromagnetic/gauge continuum effective-dynamics realization"
    lemmaDonor
    "Global classical relativistic Vlasov-Maxwell is routed toward the EM/QFT continuum lane as a PDE donor; it does not identify the universal action or the physical TOE carrier."

forcedNavierStokesRoute : OpenAITheoremRoute
forcedNavierStokesRoute =
  route "376"
    "OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MainResult"
    "OAI.BalancedTransport.balanced_three_stack_realization"
    "continuum computation/effective NS realization"
    structuralDonor
    "Forced Navier-Stokes computation is useful for effective dynamics/computation structure but is explicitly distinct from the unforced Clay regularity problem."

canonicalOpenAIRoutes : List OpenAITheoremRoute
canonicalOpenAIRoutes =
  quasiRiemannHeckeRoute
  ∷ optimalMaxCutRoute
  ∷ vlasovMaxwellRoute
  ∷ forcedNavierStokesRoute
  ∷ []

------------------------------------------------------------------------
-- Exact external formal inhabitants.
--
-- The theorem declarations really exist at the pinned upstream commit.  These
-- values make that non-emptiness explicit while keeping proof-term authority
-- outside Agda and keeping same-object TOE transport false.
------------------------------------------------------------------------

record OpenAITheoremInhabitant : Set where
  field
    repository : String
    pinnedCommit : String
    family : String
    moduleName : String
    declarationName : String
    authority : ExternalFormalAuthority
    localAgdaProofTerm : Bool
    localAgdaProofTermIsFalse : localAgdaProofTerm ≡ false
    sameObjectTOETransport : Bool
    sameObjectTOETransportIsFalse : sameObjectTOETransport ≡ false
open OpenAITheoremInhabitant public

inhabitantFromRoute : OpenAITheoremRoute → OpenAITheoremInhabitant
inhabitantFromRoute theoremRoute =
  record
    { repository = "openai/math"
    ; pinnedCommit = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
    ; family = OpenAITheoremRoute.family theoremRoute
    ; moduleName = upstreamModule theoremRoute
    ; declarationName = upstreamDeclaration theoremRoute
    ; authority = importedFormalSource
    ; localAgdaProofTerm = false
    ; localAgdaProofTermIsFalse = refl
    ; sameObjectTOETransport = false
    ; sameObjectTOETransportIsFalse = refl
    }

quasiRiemannFormalInhabitant : OpenAITheoremInhabitant
quasiRiemannFormalInhabitant = inhabitantFromRoute quasiRiemannHeckeRoute

optimalMaxCutFormalInhabitant : OpenAITheoremInhabitant
optimalMaxCutFormalInhabitant = inhabitantFromRoute optimalMaxCutRoute

vlasovMaxwellFormalInhabitant : OpenAITheoremInhabitant
vlasovMaxwellFormalInhabitant = inhabitantFromRoute vlasovMaxwellRoute

forcedNavierStokesFormalInhabitant : OpenAITheoremInhabitant
forcedNavierStokesFormalInhabitant = inhabitantFromRoute forcedNavierStokesRoute

canonicalOpenAITheoremInhabitants : List OpenAITheoremInhabitant
canonicalOpenAITheoremInhabitants =
  quasiRiemannFormalInhabitant
  ∷ optimalMaxCutFormalInhabitant
  ∷ vlasovMaxwellFormalInhabitant
  ∷ forcedNavierStokesFormalInhabitant
  ∷ []

crossKernelPromotionRemainsBlocked : openAIMaxAuthority ≡ importedFormalSource
crossKernelPromotionRemainsBlocked = refl
