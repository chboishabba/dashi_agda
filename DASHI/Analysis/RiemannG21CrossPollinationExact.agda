module DASHI.Analysis.RiemannG21CrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21PoleQuotientedExteriorExact as G21
import DASHI.Analysis.RiemannG21PrimePairKernelExact as Pair

data DonorLane : Set where
  partitionFiniteReindexPR614 : DonorLane
  coarseFineRechartPR620 : DonorLane
  nonseparableTransitionPR621 : DonorLane

record CrossPollinationRole : Set where
  constructor crossPollinationRole
  field
    donor : DonorLane
    donorPR : Nat
    importedCode : Bool
    importedCodeIsFalse : importedCode ≡ false
    boundedRole : String

open CrossPollinationRole public

pr614Role : CrossPollinationRole
pr614Role =
  crossPollinationRole partitionFiniteReindexPR614 614 false refl
    "Use the exact finite-product/permutation lesson: split the pair carrier into diagonal and swapped off-diagonal fibres and reindex before absolute-value majorization. No draft #614 module is imported."

pr620Role : CrossPollinationRole
pr620Role =
  crossPollinationRole coarseFineRechartPR620 620 false refl
    "Use the observer lesson that a collapsed coordinate is not repaired by post-composition. The literal source audit revealed two pole coordinates, so robust G21 now introduces enough sample dimensions to quotient both rather than pretending one was absent. No draft #620 module is imported."

pr621Role : CrossPollinationRole
pr621Role =
  crossPollinationRole nonseparableTransitionPR621 621 false refl
    "Use the nonseparability lesson: a pair-valued prime kernel must violate endpoint-separable and rank-one identities. G21 instantiates its own narrow arithmetic gate and imports no draft #621 module."

canonicalCrossPollinationRoles : List CrossPollinationRole
canonicalCrossPollinationRoles = pr614Role ∷ pr620Role ∷ pr621Role ∷ []

swapInvolutionReturned :
  {A : Set} → (p : Pair.Pair A) → Pair.swapPair (Pair.swapPair p) ≡ p
swapInvolutionReturned = Pair.swapPairInvolutive

relationalPairAdmissionReturned : Pair.PrimePairRelationalAdmission
relationalPairAdmissionReturned = Pair.canonicalToyPrimePairRelationalAdmission

robustRankTwoExteriorCarrierReturned : Bool
robustRankTwoExteriorCarrierReturned =
  G21.G21CurrentBoundary.robustRankTwoFourSampleCarrierConstructed
    G21.canonicalG21CurrentBoundary

robustRankTwoExteriorCarrierReturnedIsTrue :
  robustRankTwoExteriorCarrierReturned ≡ true
robustRankTwoExteriorCarrierReturnedIsTrue = refl

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    donorArchitectureIsProofOfRiemannClaim : Bool
    donorArchitectureIsProofOfRiemannClaimIsFalse :
      donorArchitectureIsProofOfRiemannClaim ≡ false
    sharedTheoremShapeIdentifiesDomains : Bool
    sharedTheoremShapeIdentifiesDomainsIsFalse :
      sharedTheoremShapeIdentifiesDomains ≡ false
    draftDonorPRCreatesHiddenDependency : Bool
    draftDonorPRCreatesHiddenDependencyIsFalse :
      draftDonorPRCreatesHiddenDependency ≡ false

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  crossPollinationBoundary false refl false refl false refl
