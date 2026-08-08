module DASHI.Physics.YangMills.BalabanP33StrictOwnedMarginExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- Volker Bach, Thomas Chen, Juerg Froehlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tosio Kato and Gustavo Ponce,
-- "Commutator Estimates and the Euler and Navier--Stokes Equations",
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Formalize two proof patterns exported by the Monster and Navier--Stokes
-- lanes into the Yang--Mills RG frontier.
--
-- First, a uniform coercive core is not selected by naming a convenient
-- number.  A decomposition core + residual = available with residual >= 0
-- proves every candidate core is at most available, and the zero-residual
-- decomposition attains that bound.
--
-- Second, every one-step Schur/RG loss has exactly one enumerated owner.  The
-- total is reconstructed from those seven contributions and a strict owned
-- margin records the actual inequality needed by the RG induction.  No
-- physical contribution, contribution-wise bound, or strict inequality is
-- manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (Dec; yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record UniformCoerciveCoreDecomposition (available : ℚ) : Set where
  constructor uniformCoerciveCoreDecomposition
  field
    commonCore : ℚ
    scaleResidual : ℚ
    residualNonnegative : 0ℚ ≤ scaleResidual
    exactReconstruction : commonCore + scaleResidual ≡ available

open UniformCoerciveCoreDecomposition public

uniformCoreBelowAvailable :
  ∀ {available}
    (decomposition : UniformCoerciveCoreDecomposition available) →
  commonCore decomposition ≤ available
uniformCoreBelowAvailable {available} decomposition =
  let
    core = commonCore decomposition
    residual = scaleResidual decomposition

    withResidual : core + 0ℚ ≤ core + residual
    withResidual =
      ℚP.+-mono-≤ ℚP.≤-refl
        (residualNonnegative decomposition)
  in
  subst
    (λ left → left ≤ available)
    (ℚP.+-identityʳ core)
    (subst
      (λ right → core + 0ℚ ≤ right)
      (exactReconstruction decomposition)
      withResidual)

maximalCoreCandidate : ∀ available →
  UniformCoerciveCoreDecomposition available
maximalCoreCandidate available =
  uniformCoerciveCoreDecomposition
    available 0ℚ ℚP.≤-refl (ℚP.+-identityʳ available)

maximalUniformCoerciveCoreAttained : ∀ available →
  commonCore (maximalCoreCandidate available) ≡ available
maximalUniformCoerciveCoreAttained available = refl

everyUniformCoreBelowCandidate :
  ∀ available
    (candidate : UniformCoerciveCoreDecomposition available) →
  commonCore candidate ≤ commonCore (maximalCoreCandidate available)
everyUniformCoreBelowCandidate available candidate =
  uniformCoreBelowAvailable candidate

maximalUniformCoerciveCore :
  ∀ available
    (candidate : UniformCoerciveCoreDecomposition available) →
  commonCore candidate ≤ available
maximalUniformCoerciveCore available candidate =
  everyUniformCoreBelowCandidate available candidate

data SchurLossOwner : Set where
  coarseBlockOwner : SchurLossOwner
  fluctuationInverseOwner : SchurLossOwner
  coarseFineDerivativeOwner : SchurLossOwner
  smallFieldNonlinearOwner : SchurLossOwner
  largeFieldPolymerOwner : SchurLossOwner
  boundaryCollarOwner : SchurLossOwner
  gaugeProjectionOwner : SchurLossOwner

schurLossOwners : List SchurLossOwner
schurLossOwners =
  coarseBlockOwner ∷
  fluctuationInverseOwner ∷
  coarseFineDerivativeOwner ∷
  smallFieldNonlinearOwner ∷
  largeFieldPolymerOwner ∷
  boundaryCollarOwner ∷
  gaugeProjectionOwner ∷ []

schurLossOwnerDecidableEquality :
  (left right : SchurLossOwner) → Dec (left ≡ right)
schurLossOwnerDecidableEquality coarseBlockOwner coarseBlockOwner = yes refl
schurLossOwnerDecidableEquality coarseBlockOwner fluctuationInverseOwner = no (λ ())
schurLossOwnerDecidableEquality coarseBlockOwner coarseFineDerivativeOwner = no (λ ())
schurLossOwnerDecidableEquality coarseBlockOwner smallFieldNonlinearOwner = no (λ ())
schurLossOwnerDecidableEquality coarseBlockOwner largeFieldPolymerOwner = no (λ ())
schurLossOwnerDecidableEquality coarseBlockOwner boundaryCollarOwner = no (λ ())
schurLossOwnerDecidableEquality coarseBlockOwner gaugeProjectionOwner = no (λ ())
schurLossOwnerDecidableEquality fluctuationInverseOwner coarseBlockOwner = no (λ ())
schurLossOwnerDecidableEquality fluctuationInverseOwner fluctuationInverseOwner = yes refl
schurLossOwnerDecidableEquality fluctuationInverseOwner coarseFineDerivativeOwner = no (λ ())
schurLossOwnerDecidableEquality fluctuationInverseOwner smallFieldNonlinearOwner = no (λ ())
schurLossOwnerDecidableEquality fluctuationInverseOwner largeFieldPolymerOwner = no (λ ())
schurLossOwnerDecidableEquality fluctuationInverseOwner boundaryCollarOwner = no (λ ())
schurLossOwnerDecidableEquality fluctuationInverseOwner gaugeProjectionOwner = no (λ ())
schurLossOwnerDecidableEquality coarseFineDerivativeOwner coarseBlockOwner = no (λ ())
schurLossOwnerDecidableEquality coarseFineDerivativeOwner fluctuationInverseOwner = no (λ ())
schurLossOwnerDecidableEquality coarseFineDerivativeOwner coarseFineDerivativeOwner = yes refl
schurLossOwnerDecidableEquality coarseFineDerivativeOwner smallFieldNonlinearOwner = no (λ ())
schurLossOwnerDecidableEquality coarseFineDerivativeOwner largeFieldPolymerOwner = no (λ ())
schurLossOwnerDecidableEquality coarseFineDerivativeOwner boundaryCollarOwner = no (λ ())
schurLossOwnerDecidableEquality coarseFineDerivativeOwner gaugeProjectionOwner = no (λ ())
schurLossOwnerDecidableEquality smallFieldNonlinearOwner coarseBlockOwner = no (λ ())
schurLossOwnerDecidableEquality smallFieldNonlinearOwner fluctuationInverseOwner = no (λ ())
schurLossOwnerDecidableEquality smallFieldNonlinearOwner coarseFineDerivativeOwner = no (λ ())
schurLossOwnerDecidableEquality smallFieldNonlinearOwner smallFieldNonlinearOwner = yes refl
schurLossOwnerDecidableEquality smallFieldNonlinearOwner largeFieldPolymerOwner = no (λ ())
schurLossOwnerDecidableEquality smallFieldNonlinearOwner boundaryCollarOwner = no (λ ())
schurLossOwnerDecidableEquality smallFieldNonlinearOwner gaugeProjectionOwner = no (λ ())
schurLossOwnerDecidableEquality largeFieldPolymerOwner coarseBlockOwner = no (λ ())
schurLossOwnerDecidableEquality largeFieldPolymerOwner fluctuationInverseOwner = no (λ ())
schurLossOwnerDecidableEquality largeFieldPolymerOwner coarseFineDerivativeOwner = no (λ ())
schurLossOwnerDecidableEquality largeFieldPolymerOwner smallFieldNonlinearOwner = no (λ ())
schurLossOwnerDecidableEquality largeFieldPolymerOwner largeFieldPolymerOwner = yes refl
schurLossOwnerDecidableEquality largeFieldPolymerOwner boundaryCollarOwner = no (λ ())
schurLossOwnerDecidableEquality largeFieldPolymerOwner gaugeProjectionOwner = no (λ ())
schurLossOwnerDecidableEquality boundaryCollarOwner coarseBlockOwner = no (λ ())
schurLossOwnerDecidableEquality boundaryCollarOwner fluctuationInverseOwner = no (λ ())
schurLossOwnerDecidableEquality boundaryCollarOwner coarseFineDerivativeOwner = no (λ ())
schurLossOwnerDecidableEquality boundaryCollarOwner smallFieldNonlinearOwner = no (λ ())
schurLossOwnerDecidableEquality boundaryCollarOwner largeFieldPolymerOwner = no (λ ())
schurLossOwnerDecidableEquality boundaryCollarOwner boundaryCollarOwner = yes refl
schurLossOwnerDecidableEquality boundaryCollarOwner gaugeProjectionOwner = no (λ ())
schurLossOwnerDecidableEquality gaugeProjectionOwner coarseBlockOwner = no (λ ())
schurLossOwnerDecidableEquality gaugeProjectionOwner fluctuationInverseOwner = no (λ ())
schurLossOwnerDecidableEquality gaugeProjectionOwner coarseFineDerivativeOwner = no (λ ())
schurLossOwnerDecidableEquality gaugeProjectionOwner smallFieldNonlinearOwner = no (λ ())
schurLossOwnerDecidableEquality gaugeProjectionOwner largeFieldPolymerOwner = no (λ ())
schurLossOwnerDecidableEquality gaugeProjectionOwner boundaryCollarOwner = no (λ ())
schurLossOwnerDecidableEquality gaugeProjectionOwner gaugeProjectionOwner = yes refl

record OwnedSchurLosses : Set where
  constructor ownedSchurLosses
  field
    coarseBlockLoss : ℚ
    fluctuationInverseLoss : ℚ
    coarseFineDerivativeLoss : ℚ
    smallFieldNonlinearLoss : ℚ
    largeFieldPolymerLoss : ℚ
    boundaryCollarLoss : ℚ
    gaugeProjectionLoss : ℚ

open OwnedSchurLosses public

ownedLoss : OwnedSchurLosses → SchurLossOwner → ℚ
ownedLoss losses coarseBlockOwner = coarseBlockLoss losses
ownedLoss losses fluctuationInverseOwner = fluctuationInverseLoss losses
ownedLoss losses coarseFineDerivativeOwner = coarseFineDerivativeLoss losses
ownedLoss losses smallFieldNonlinearOwner = smallFieldNonlinearLoss losses
ownedLoss losses largeFieldPolymerOwner = largeFieldPolymerLoss losses
ownedLoss losses boundaryCollarOwner = boundaryCollarLoss losses
ownedLoss losses gaugeProjectionOwner = gaugeProjectionLoss losses

sumOwnedLoss : OwnedSchurLosses → ℚ
sumOwnedLoss losses =
  coarseBlockLoss losses
  + fluctuationInverseLoss losses
  + coarseFineDerivativeLoss losses
  + smallFieldNonlinearLoss losses
  + largeFieldPolymerLoss losses
  + boundaryCollarLoss losses
  + gaugeProjectionLoss losses

sumOwnerEnumerationExact : ∀ losses →
  sumOwnedLoss losses
  ≡ ownedLoss losses coarseBlockOwner
    + ownedLoss losses fluctuationInverseOwner
    + ownedLoss losses coarseFineDerivativeOwner
    + ownedLoss losses smallFieldNonlinearOwner
    + ownedLoss losses largeFieldPolymerOwner
    + ownedLoss losses boundaryCollarOwner
    + ownedLoss losses gaugeProjectionOwner
sumOwnerEnumerationExact losses = refl

record StrictOwnedMargin : Set where
  constructor strictOwnedMargin
  field
    losses : OwnedSchurLosses
    totalLoss : ℚ
    availableMargin : ℚ
    lossScale : ℚ

    everyContributionNonnegative : ∀ owner →
      0ℚ ≤ ownedLoss losses owner

    eraseOwnershipReconstructsPhysicalRemainder :
      totalLoss ≡ sumOwnedLoss losses

    strictOwnedDiscountedMargin :
      lossScale * totalLoss < availableMargin

open StrictOwnedMargin public

strictMarginAfterErasingOwners :
  (margin : StrictOwnedMargin) →
  lossScale margin * sumOwnedLoss (losses margin)
  < availableMargin margin
strictMarginAfterErasingOwners margin =
  subst
    (λ selected →
      lossScale margin * selected < availableMargin margin)
    (eraseOwnershipReconstructsPhysicalRemainder margin)
    (strictOwnedDiscountedMargin margin)

maximalUniformCoerciveCoreLevel : ProofLevel
maximalUniformCoerciveCoreLevel = machineChecked

schurLossOwnerEnumerationLevel : ProofLevel
schurLossOwnerEnumerationLevel = machineChecked

strictOwnedMarginTransportLevel : ProofLevel
strictOwnedMarginTransportLevel = machineChecked
