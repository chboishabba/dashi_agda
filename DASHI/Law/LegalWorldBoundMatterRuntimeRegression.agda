module DASHI.Law.LegalWorldBoundMatterRuntimeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.LegalWorldBoundMatterRuntimeExact as Bound

boundary : Bound.LegalWorldBoundMatterRuntimeBoundary
boundary = Bound.canonicalLegalWorldBoundMatterRuntimeBoundary

explicitWorld :
  Bound.runtimeCarriesExplicitWorldCoordinate boundary ≡ true
explicitWorld =
  Bound.runtimeCarriesExplicitWorldCoordinateIsTrue boundary

readerCannotMutateWorld :
  Bound.ordinaryReaderCommandMayMutateBoundWorld boundary ≡ false
readerCannotMutateWorld =
  Bound.ordinaryReaderCommandMayMutateBoundWorldIsFalse boundary

timeRequiresRebind :
  Bound.timeChangeRequiresExplicitWorldRebind boundary ≡ true
timeRequiresRebind =
  Bound.timeChangeRequiresExplicitWorldRebindIsTrue boundary

jurisdictionRequiresRebind :
  Bound.jurisdictionChangeRequiresExplicitWorldRebind boundary ≡ true
jurisdictionRequiresRebind =
  Bound.jurisdictionChangeRequiresExplicitWorldRebindIsTrue boundary
