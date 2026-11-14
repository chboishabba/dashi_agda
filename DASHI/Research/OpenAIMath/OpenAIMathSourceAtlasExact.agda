module DASHI.Research.OpenAIMath.OpenAIMathSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.String using (String)
open import DASHI.Research.OpenAIMath.OpenAIMathUpstreamReceiptExact
open import DASHI.Research.OpenAIMath.OpenAIMathPriorityAtlasExact

record RoutedSource : Set where
  constructor mkRoutedSource
  field
    familyId : String
    title : String
    authority : UpstreamAuthorityLevel
    solutionModule : String
    declaration : String
    comparator : String
    programme : DASHIProgramme
    relevance : RelevanceClass
    provesFullRiemannHypothesis : Bool
    provesGeneralBSD : Bool
    provesGeneralHodgeConjecture : Bool
    provesPNotEqualsNP : Bool
    provesClayNavierStokes : Bool
    provesYangMillsMassGap : Bool
    sameObjectTransportPaid : Bool
    dashiLeanPortPaid : Bool

quasiRiemann : RoutedSource
quasiRiemann = mkRoutedSource
  "003"
  "The quasi-Riemann hypothesis"
  leanDeclaration
  "OAI.NumberTheory.DirichletL.Nonvanishing"
  "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re"
  "ComparatorChallenges.QuasiRiemannHypothesis"
  riemannHypothesis
  directFrontier
  false false false false false false false false

uniqueGamesMaxCut : RoutedSource
uniqueGamesMaxCut = mkRoutedSource
  "102"
  "The Unique Games Conjecture and optimal approximation thresholds"
  leanDeclaration
  "OAI.Computability.MaxCut.Main"
  "OAI.OptimalMaxCut.main"
  "ComparatorChallenges.OptimalMaxCut"
  pVersusNP
  lemmaDonor
  false false false false false false false false

relativisticVlasovMaxwell : RoutedSource
relativisticVlasovMaxwell = mkRoutedSource
  "362"
  "Global smoothness for relativistic Vlasov-Maxwell"
  leanDeclaration
  "OAI.Analysis.VlasovMaxwell.Main"
  "OAI.RVM.global_classical_solution"
  "ComparatorChallenges.VlasovMaxwell"
  quantumMathematics
  lemmaDonor
  false false false false false false false false

forcedNavierStokesComputation : RoutedSource
forcedNavierStokesComputation = mkRoutedSource
  "376"
  "Universal computation in forced Navier-Stokes flows"
  leanDeclaration
  "OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MainResult"
  "OAI.BalancedTransport.balanced_three_stack_realization"
  "ComparatorChallenges.ForcedNavierStokesComputation"
  navierStokes
  lemmaDonor
  false false false false false false false false

hodgeCM : RoutedSource
hodgeCM = mkRoutedSource
  "032"
  "The rational Hodge conjecture for CM abelian varieties"
  manuscript
  ""
  ""
  ""
  hodge
  directFrontier
  false false false false false false false false

bsdLowSelmer : RoutedSource
bsdLowSelmer = mkRoutedSource
  "002"
  "The full BSD formula from low Selmer corank"
  manuscript
  ""
  ""
  ""
  birchSwinnertonDyer
  directFrontier
  false false false false false false false false

comparatorChallengeIsProofAuthority : Bool
comparatorChallengeIsProofAuthority = false

sourceAtlasPromotesMillenniumClaims : Bool
sourceAtlasPromotesMillenniumClaims = false
