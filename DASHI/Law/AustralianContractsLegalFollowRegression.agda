module DASHI.Law.AustralianContractsLegalFollowRegression where

open import DASHI.Core.Prelude

import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.WaltonsEstoppelMaterialisationExact as Waltons
import DASHI.Law.MannPatersonUnseenMatterExact as Mann

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
  Contracts.NF.FactorsThrough
    Contracts.coarsePrivityProjection
    Contracts.operativePrivityRoute
  → ⊥
qldAsAtNonFactorabilityExists =
  Contracts.coarseDoctrineLabelCannotRecoverAsAtRoute
