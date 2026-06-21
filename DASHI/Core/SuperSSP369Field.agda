module DASHI.Core.SuperSSP369Field where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import MonsterOntos using (SSP; p3; p7)

open import DASHI.Foundations.FifteenSSP369Forest using
  ( FifteenSSP369Forest
  ; constantForest
  )
open import DASHI.Foundations.FifteenSSPSurface using
  ( FifteenSSPSurface
  ; canonicalExampleFifteenSSPSurface
  ; canonicalNegativeFifteenSSPSurface
  ; canonicalPositiveFifteenSSPSurface
  ; canonicalZeroFifteenSSPSurface
  )
open import DASHI.Foundations.SSPPrimeLane369Refinement using
  ( SSPPrimeLane369Refinement
  ; Lane369Address
  ; root
  ; canonicalThreeSixNineAddress
  ; mkSSPPrimeLane369Refinement
  )
open import DASHI.Foundations.SSPPrimeLane369Signature using
  ( Prime369Signature
  ; prime369Signature
  )
open import DASHI.Foundations.SSPPrimeLaneSymmetryProfile using
  ( PrimeLaneSymmetryProfile
  ; primeLaneSymmetryProfile
  )

------------------------------------------------------------------------
-- Typed field/supervoxel lift over the 15SSP-369 carrier spine.

data SSPFieldParity : Set where
  evenParity : SSPFieldParity
  oddParity : SSPFieldParity

record SuperSSP369Supervoxel (d : Nat) : Set where
  constructor mkSuperSSP369Supervoxel
  field
    primeLane : SSP
    signature : Prime369Signature
    signatureMatchesPrime :
      Prime369Signature.prime signature ≡ primeLane
    refinement : SSPPrimeLane369Refinement d
    refinementMatchesPrime :
      SSPPrimeLane369Refinement.primeLane refinement ≡ primeLane
    symmetryProfile : PrimeLaneSymmetryProfile
    symmetryMatchesPrime :
      PrimeLaneSymmetryProfile.primeIdentity symmetryProfile ≡ primeLane
    parity : SSPFieldParity
    bodySurface : FifteenSSPSurface
    residueSurface : FifteenSSPSurface

open SuperSSP369Supervoxel public

record SuperSSP369Field (d : Nat) : Set where
  constructor mkSuperSSP369Field
  field
    bodyField : FifteenSSP369Forest FifteenSSPSurface
    residueField : FifteenSSP369Forest FifteenSSPSurface
    focus : SuperSSP369Supervoxel d
    promoted : Bool
    promotedIsFalse : promoted ≡ false

open SuperSSP369Field public

focusPrimeLane :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  SSP
focusPrimeLane f = primeLane (focus f)

focusSignature :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  Prime369Signature
focusSignature f = signature (focus f)

focusRefinementAddress :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  Lane369Address d
focusRefinementAddress f = SSPPrimeLane369Refinement.address (refinement (focus f))

focusParity :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  SSPFieldParity
focusParity f = parity (focus f)

focusBodySurface :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSPSurface
focusBodySurface f = bodySurface (focus f)

focusResidueSurface :
  ∀ {d : Nat} →
  SuperSSP369Field d →
  FifteenSSPSurface
focusResidueSurface f = residueSurface (focus f)

rootP3Supervoxel : SuperSSP369Supervoxel zero
rootP3Supervoxel =
  mkSuperSSP369Supervoxel
    p3
    (prime369Signature p3)
    refl
    (mkSSPPrimeLane369Refinement p3 root)
    refl
    (primeLaneSymmetryProfile p3)
    refl
    evenParity
    canonicalZeroFifteenSSPSurface
    canonicalExampleFifteenSSPSurface

depth3P7Supervoxel : SuperSSP369Supervoxel (suc (suc (suc zero)))
depth3P7Supervoxel =
  mkSuperSSP369Supervoxel
    p7
    (prime369Signature p7)
    refl
    (mkSSPPrimeLane369Refinement p7 canonicalThreeSixNineAddress)
    refl
    (primeLaneSymmetryProfile p7)
    refl
    oddParity
    canonicalExampleFifteenSSPSurface
    canonicalNegativeFifteenSSPSurface

rootField : SuperSSP369Field zero
rootField =
  mkSuperSSP369Field
    (constantForest zero canonicalZeroFifteenSSPSurface)
    (constantForest zero canonicalExampleFifteenSSPSurface)
    rootP3Supervoxel
    false
    refl

depth3Field : SuperSSP369Field (suc (suc (suc zero)))
depth3Field =
  mkSuperSSP369Field
    (constantForest (suc (suc (suc zero))) canonicalExampleFifteenSSPSurface)
    (constantForest (suc (suc (suc zero))) canonicalNegativeFifteenSSPSurface)
    depth3P7Supervoxel
    false
    refl

canonicalSuperSSP369Fields : List (SuperSSP369Field zero)
canonicalSuperSSP369Fields =
  rootField ∷ []

rootFieldPrimeIsP3 : focusPrimeLane rootField ≡ p3
rootFieldPrimeIsP3 = refl

depth3FieldPrimeIsP7 : focusPrimeLane depth3Field ≡ p7
depth3FieldPrimeIsP7 = refl

rootFieldParityIsEven : focusParity rootField ≡ evenParity
rootFieldParityIsEven = refl

depth3FieldParityIsOdd : focusParity depth3Field ≡ oddParity
depth3FieldParityIsOdd = refl

depth3FieldBodyProjection :
  focusBodySurface depth3Field ≡ canonicalExampleFifteenSSPSurface
depth3FieldBodyProjection = refl

depth3FieldResidueProjection :
  focusResidueSurface depth3Field ≡ canonicalNegativeFifteenSSPSurface
depth3FieldResidueProjection = refl

rootFieldResidueProjection :
  focusResidueSurface rootField ≡ canonicalExampleFifteenSSPSurface
rootFieldResidueProjection = refl

depth3FieldBodyForestIsCandidate :
  promoted depth3Field ≡ false
depth3FieldBodyForestIsCandidate = refl
