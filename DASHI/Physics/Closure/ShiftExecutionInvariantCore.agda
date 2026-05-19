module DASHI.Physics.Closure.ShiftExecutionInvariantCore where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Properties as NatP using (_≟_)
open import Data.Integer using (ℤ; +_; _-_)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Nullary.Decidable.Core using (yes; no)

import Data.Integer as Int

open import DASHI.Physics.Signature31InstanceShiftZ as S31Z
open import DASHI.Physics.SignedPerm4 as SP
open import Ontology.GodelLattice as GL
open import Ontology.Hecke.Scan as HS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM
open import MonsterOntos using (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)

ShiftGeoV : Set
ShiftGeoV = Vec ℤ S31Z.m

timeCoord : ShiftGeoV → ℤ
timeCoord (t ∷ _ ∷ _ ∷ _ ∷ []) = t

space1Coord : ShiftGeoV → ℤ
space1Coord (_ ∷ s1 ∷ _ ∷ _ ∷ []) = s1

space2Coord : ShiftGeoV → ℤ
space2Coord (_ ∷ _ ∷ s2 ∷ _ ∷ []) = s2

space3Coord : ShiftGeoV → ℤ
space3Coord (_ ∷ _ ∷ _ ∷ s3 ∷ []) = s3

isZeroℤ : ℤ → Bool
isZeroℤ z with Int._≟_ z (+ 0)
... | yes _ = true
... | no _ = false

boolToNat : Bool → Nat
boolToNat true = suc zero
boolToNat false = zero

shiftIsoWitnessCore : SP.SignedPerm4
shiftIsoWitnessCore =
  record
    { perm = SP.p012
    ; flipT = true
    ; flipS = true ∷ true ∷ true ∷ []
    }

timeFlipIso : SP.SignedPerm4
timeFlipIso =
  record
    { perm = SP.p012
    ; flipT = false
    ; flipS = true ∷ true ∷ true ∷ []
    }

shiftHeckeAction : SSP → ShiftGeoV → ShiftGeoV
shiftHeckeAction p x with p
... | p2  = x
... | p3  = x
... | p5  = x
... | p7  = x
... | p11 = x
... | p13 = S31Z.actIso4 shiftIsoWitnessCore x
... | p17 = S31Z.actIso4 shiftIsoWitnessCore x
... | p19 = S31Z.actIso4 shiftIsoWitnessCore x
... | p23 = S31Z.actIso4 shiftIsoWitnessCore x
... | p29 = S31Z.actIso4 shiftIsoWitnessCore x
... | p31 = S31Z.actIso4 timeFlipIso x
... | p41 = S31Z.actIso4 timeFlipIso x
... | p47 = S31Z.actIso4 timeFlipIso x
... | p59 = S31Z.actIso4 timeFlipIso x
... | p71 = S31Z.actIso4 timeFlipIso x

shiftCompat : SSP → ShiftGeoV → Bool
shiftCompat p x with p
... | p2  = isZeroℤ (timeCoord x)
... | p3  = isZeroℤ (space1Coord x)
... | p5  = isZeroℤ (space2Coord x)
... | p7  = isZeroℤ (space3Coord x)
... | p11 = isZeroℤ (timeCoord (shiftHeckeAction p x) - timeCoord x)
... | p13 = isZeroℤ (space1Coord (shiftHeckeAction p x) - space1Coord x)
... | p17 = isZeroℤ (space2Coord (shiftHeckeAction p x) - space2Coord x)
... | p19 = isZeroℤ (space3Coord (shiftHeckeAction p x) - space3Coord x)
... | p23 = isZeroℤ (timeCoord (shiftHeckeAction p x))
... | p29 = isZeroℤ (space1Coord (shiftHeckeAction p x))
... | p31 = isZeroℤ (timeCoord (shiftHeckeAction p x) - timeCoord x)
... | p41 = isZeroℤ (space1Coord (shiftHeckeAction p x) - space1Coord x)
... | p47 = isZeroℤ (space2Coord (shiftHeckeAction p x) - space2Coord x)
... | p59 = isZeroℤ (space3Coord (shiftHeckeAction p x) - space3Coord x)
... | p71 = isZeroℤ (timeCoord (shiftHeckeAction p x))

shiftPrimeEmbedding : ShiftGeoV → GL.FactorVec
shiftPrimeEmbedding x =
  GL.v15
    (boolToNat (shiftCompat p2 x))
    (boolToNat (shiftCompat p3 x))
    (boolToNat (shiftCompat p5 x))
    (boolToNat (shiftCompat p7 x))
    (boolToNat (shiftCompat p11 x))
    (boolToNat (shiftCompat p13 x))
    (boolToNat (shiftCompat p17 x))
    (boolToNat (shiftCompat p19 x))
    (boolToNat (shiftCompat p23 x))
    (boolToNat (shiftCompat p29 x))
    (boolToNat (shiftCompat p31 x))
    (boolToNat (shiftCompat p41 x))
    (boolToNat (shiftCompat p47 x))
    (boolToNat (shiftCompat p59 x))
    (boolToNat (shiftCompat p71 x))

shiftHeckeFamily : HS.HeckeFamilyOn ShiftGeoV
shiftHeckeFamily =
  record
    { T = shiftHeckeAction
    ; compat = shiftCompat
    }

shiftSignature : ShiftGeoV → HS.Sig15
shiftSignature = HS.scanOn shiftHeckeFamily

shiftSignatureEigenProfile : HS.Sig15 → PHEM.EigenProfile
shiftSignatureEigenProfile sig =
  PHEM.eigenProfile
    (boolToNat (HS.Sig15.b2 sig)
      + boolToNat (HS.Sig15.b3 sig)
      + boolToNat (HS.Sig15.b5 sig)
      + boolToNat (HS.Sig15.b7 sig)
      + boolToNat (HS.Sig15.b11 sig))
    (boolToNat (HS.Sig15.b13 sig)
      + boolToNat (HS.Sig15.b17 sig)
      + boolToNat (HS.Sig15.b19 sig)
      + boolToNat (HS.Sig15.b23 sig)
      + boolToNat (HS.Sig15.b29 sig))
    (boolToNat (HS.Sig15.b31 sig)
      + boolToNat (HS.Sig15.b41 sig)
      + boolToNat (HS.Sig15.b47 sig)
      + boolToNat (HS.Sig15.b59 sig)
      + boolToNat (HS.Sig15.b71 sig))

shiftExecutionEigenProfile : ShiftGeoV → PHEM.EigenProfile
shiftExecutionEigenProfile x =
  shiftSignatureEigenProfile (shiftSignature x)

zeroEigenProfile : PHEM.EigenProfile
zeroEigenProfile = PHEM.eigenProfile zero zero zero

countMatch : Nat → Nat → Nat
countMatch m n with m NatP.≟ n
... | yes _ = suc zero
... | no _ = zero

shiftEigenOverlap : PHEM.EigenProfile → PHEM.EigenProfile → Nat
shiftEigenOverlap a b =
  suc
    (countMatch (PHEM.EigenProfile.earth a) (PHEM.EigenProfile.earth b)
      + countMatch (PHEM.EigenProfile.spoke a) (PHEM.EigenProfile.spoke b)
      + countMatch (PHEM.EigenProfile.hub a) (PHEM.EigenProfile.hub b))

canonicalShiftSignature : HS.Sig15
canonicalShiftSignature =
  shiftSignature S31Z.shell1ConePoint

canonicalShiftEigenProfile : PHEM.EigenProfile
canonicalShiftEigenProfile =
  shiftExecutionEigenProfile S31Z.shell1ConePoint
