module DASHI.Law.AustralianContractsLegalFollowRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.WaltonsEstoppelMaterialisationExact as Waltons
import DASHI.Law.MannPatersonUnseenMatterExact as Mann
import DASHI.Law.AustralianContractsLandscapeControllerExact as Landscape
import DASHI.Law.AustralianContractsReviewedHopCompilerExact as ReviewedHop

contractsBoundaryExists : Set
contractsBoundaryExists = Contracts.AustralianContractsFollowBoundary

contractsBoundaryPaid : contractsBoundaryExists
contractsBoundaryPaid = Contracts.canonicalAustralianContractsFollowBoundary

waltonsBoundaryExists : Set
waltonsBoundaryExists = Waltons.WaltonsEstoppelBoundary

waltonsBoundaryPaid : waltonsBoundaryExists
waltonsBoundaryPaid = Waltons.canonicalWaltonsEstoppelBoundary

mannBoundaryExists : Set
mannBoundaryExists = Mann.MannUnseenMatterAcceptanceBoundary

mannBoundaryPaid : mannBoundaryExists
mannBoundaryPaid = Mann.canonicalMannUnseenMatterAcceptanceBoundary

qldAsAtNonFactorabilityExists :
  NF.FactorsThrough
    Contracts.coarsePrivityProjection
    Contracts.operativePrivityRoute
  → ⊥
qldAsAtNonFactorabilityExists =
  Contracts.coarseDoctrineLabelCannotRecoverAsAtRoute


landscapeControllerBoundaryExists : Set
landscapeControllerBoundaryExists =
  Landscape.AustralianContractsLandscapeControllerBoundary

landscapeControllerBoundaryPaid : landscapeControllerBoundaryExists
landscapeControllerBoundaryPaid =
  Landscape.canonicalAustralianContractsLandscapeControllerBoundary


reviewedHopCompilerBoundaryExists : Set
reviewedHopCompilerBoundaryExists =
  ReviewedHop.AustralianContractsReviewedHopCompilerBoundary

reviewedHopCompilerBoundaryPaid : reviewedHopCompilerBoundaryExists
reviewedHopCompilerBoundaryPaid =
  ReviewedHop.canonicalAustralianContractsReviewedHopCompilerBoundary
