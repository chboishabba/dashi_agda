module DASHI.Physics.CondensedMatter.MATBGInteractingTHFLiteralMatricesExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-EXACT TOPOLOGICAL-HEAVY-FERMION SINGLE-PARTICLE MATRICES
--
-- The K-valley matrices follow the published THF form used by Xiao et al.
-- and written explicitly by Singh et al. (Nature Communications 15, 5257,
-- 2024):
--
-- Hc(K) = [[0,0,v*k,0], [0,0,0,v*kbar],
--          [v*kbar,0,0,M], [0,v*k,M,0]]
--
-- Hcf(K) = [[gamma,v'*kbar], [v'*k,gamma], [0,0], [0,0]].
--
-- The opposite valley is obtained by k <-> -kbar. This module records the
-- literal matrix skeleton only. It does not claim a solved interacting model,
-- sample calibration, or QTM replay.
------------------------------------------------------------------------

data I4 : Set where
  i0 i1 i2 i3 : I4

data I2 : Set where
  j0 j1 : I2

data THFEntry : Set where
  zeroE gammaE massE : THFEntry
  vK vKbar vMinusK vMinusKbar : THFEntry
  vpK vpKbar vpMinusK vpMinusKbar : THFEntry

valleyFlip : THFEntry → THFEntry
valleyFlip zeroE = zeroE
valleyFlip gammaE = gammaE
valleyFlip massE = massE
valleyFlip vK = vMinusKbar
valleyFlip vKbar = vMinusK
valleyFlip vMinusK = vKbar
valleyFlip vMinusKbar = vK
valleyFlip vpK = vpMinusKbar
valleyFlip vpKbar = vpMinusK
valleyFlip vpMinusK = vpKbar
valleyFlip vpMinusKbar = vpK

hcK : I4 → I4 → THFEntry
hcK i0 i0 = zeroE
hcK i0 i1 = zeroE
hcK i0 i2 = vK
hcK i0 i3 = zeroE
hcK i1 i0 = zeroE
hcK i1 i1 = zeroE
hcK i1 i2 = zeroE
hcK i1 i3 = vKbar
hcK i2 i0 = vKbar
hcK i2 i1 = zeroE
hcK i2 i2 = zeroE
hcK i2 i3 = massE
hcK i3 i0 = zeroE
hcK i3 i1 = vK
hcK i3 i2 = massE
hcK i3 i3 = zeroE

hcfK : I4 → I2 → THFEntry
hcfK i0 j0 = gammaE
hcfK i0 j1 = vpKbar
hcfK i1 j0 = vpK
hcfK i1 j1 = gammaE
hcfK i2 j0 = zeroE
hcfK i2 j1 = zeroE
hcfK i3 j0 = zeroE
hcfK i3 j1 = zeroE

hcKPrime : I4 → I4 → THFEntry
hcKPrime r c = valleyFlip (hcK r c)

hcfKPrime : I4 → I2 → THFEntry
hcfKPrime r c = valleyFlip (hcfK r c)

record THFLiteralMatrixSourceReceipt : Set where
  constructor thf-literal-matrix-source-receipt
  field
    sourceDOI : String
    xiaoDOI : String
    hcDimension : String
    hcfDimension : String
    oppositeValleyRule : String

open THFLiteralMatrixSourceReceipt public

canonicalTHFLiteralMatrixSourceReceipt : THFLiteralMatrixSourceReceipt
canonicalTHFLiteralMatrixSourceReceipt =
  thf-literal-matrix-source-receipt
    "10.1038/s41467-024-49531-3"
    "10.1038/s41586-026-10378-x"
    "4x4"
    "4x2"
    "K' obtained from K by k <-> -kbar"

record THFLiteralMatrixBoundary : Set where
  constructor thf-literal-matrix-boundary
  field
    literalMatrixShapesPaid : Bool
    literalKValleyEntriesPaid : Bool
    literalKPrimeTransformationPaid : Bool
    xiaoParameterCompatibilitySourcePaid : Bool
    interactingSelfConsistencyPaid : Bool
    qtmDataReplayPaid : Bool
    sameSampleEntropyPaid : Bool

open THFLiteralMatrixBoundary public

canonicalTHFLiteralMatrixBoundary : THFLiteralMatrixBoundary
canonicalTHFLiteralMatrixBoundary =
  thf-literal-matrix-boundary true true true true false false false

record THFLiteralMatrixAttributionBoundary : Set where
  constructor thf-literal-matrix-attribution-boundary
  field
    songBernevigLineageOwnsTHFMatrixArchitecture : Bool
    singhEtAlOwnExplicitPublishedMatrixForm : Bool
    xiaoEtAlOwn2026ParameterUseAndQTMComparison : Bool
    dashiOwnsTypedLiteralizationAndValleyMap : Bool
    literalizationDoesNotCreateSolvedInteractingModel : Bool

open THFLiteralMatrixAttributionBoundary public

canonicalTHFLiteralMatrixAttributionBoundary : THFLiteralMatrixAttributionBoundary
canonicalTHFLiteralMatrixAttributionBoundary =
  thf-literal-matrix-attribution-boundary true true true true true
