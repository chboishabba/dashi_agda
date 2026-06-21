module DASHI.Foundations.SSPPrimeLaneSymmetryProfile where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

open import DASHI.Foundations.Base369Nat using (_%_)
open import DASHI.Foundations.SSPPrimeLane369Signature using
  ( Prime369Signature
  ; prime369Signature
  )
open import DASHI.Foundations.StageAtlasZeroToEleven using
  ( StageAtlasZeroToEleven
  ; StageAtlasTopologicalReading
  ; atlas-0 ; atlas-1 ; atlas-2 ; atlas-3 ; atlas-4 ; atlas-5
  ; atlas-6 ; atlas-7 ; atlas-8 ; atlas-9 ; atlas-10 ; atlas-11
  ; topological-reading-of
  )
open import DASHI.TrackedPrimes using
  ( SSP
  ; toNat
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )

------------------------------------------------------------------------
-- Prime-lane local symmetry chamber.
--
-- Each tracked SSP prime now carries:
--   * its typed 369 residue fingerprint,
--   * its prime-identity stage coordinate/reading,
--   * its unit-symmetry order p - 1,
--   * its unit-symmetry stage coordinate/reading.

stageCoordinateFromNatModulo12 : Nat → StageAtlasZeroToEleven
stageCoordinateFromNatModulo12 n with n % 12
... | 0 = atlas-0
... | 1 = atlas-1
... | 2 = atlas-2
... | 3 = atlas-3
... | 4 = atlas-4
... | 5 = atlas-5
... | 6 = atlas-6
... | 7 = atlas-7
... | 8 = atlas-8
... | 9 = atlas-9
... | 10 = atlas-10
... | _ = atlas-11

primeIdentityStage : SSP → StageAtlasZeroToEleven
primeIdentityStage p =
  stageCoordinateFromNatModulo12 (toNat p)

primeIdentityReading : SSP → StageAtlasTopologicalReading
primeIdentityReading p =
  topological-reading-of (primeIdentityStage p)

unitSymmetryOrder : SSP → Nat
unitSymmetryOrder p = toNat p - 1

unitSymmetryStage : SSP → StageAtlasZeroToEleven
unitSymmetryStage p =
  stageCoordinateFromNatModulo12 (unitSymmetryOrder p)

unitSymmetryReading : SSP → StageAtlasTopologicalReading
unitSymmetryReading p =
  topological-reading-of (unitSymmetryStage p)

record PrimeLaneSymmetryProfile : Set where
  constructor mkPrimeLaneSymmetryProfile
  field
    primeIdentity : SSP
    residueSignature : Prime369Signature
    residueSignatureMatchesPrime :
      Prime369Signature.prime residueSignature ≡ primeIdentity
    additiveStage : StageAtlasZeroToEleven
    additiveStageMatches :
      additiveStage ≡ primeIdentityStage primeIdentity
    additiveReading : StageAtlasTopologicalReading
    additiveReadingMatches :
      additiveReading ≡ primeIdentityReading primeIdentity
    unitOrder : Nat
    unitOrderMatchesPrimeMinusOne :
      unitOrder ≡ unitSymmetryOrder primeIdentity
    unitStage : StageAtlasZeroToEleven
    unitStageMatches :
      unitStage ≡ unitSymmetryStage primeIdentity
    unitReading : StageAtlasTopologicalReading
    unitReadingMatches :
      unitReading ≡ unitSymmetryReading primeIdentity

open PrimeLaneSymmetryProfile public

primeLaneSymmetryProfile : SSP → PrimeLaneSymmetryProfile
primeLaneSymmetryProfile p =
  mkPrimeLaneSymmetryProfile
    p
    (prime369Signature p)
    refl
    (primeIdentityStage p)
    refl
    (primeIdentityReading p)
    refl
    (unitSymmetryOrder p)
    refl
    (unitSymmetryStage p)
    refl
    (unitSymmetryReading p)
    refl

canonicalPrimeLaneSymmetryProfiles : List PrimeLaneSymmetryProfile
canonicalPrimeLaneSymmetryProfiles =
  primeLaneSymmetryProfile p2
  ∷ primeLaneSymmetryProfile p3
  ∷ primeLaneSymmetryProfile p5
  ∷ primeLaneSymmetryProfile p7
  ∷ primeLaneSymmetryProfile p11
  ∷ primeLaneSymmetryProfile p13
  ∷ primeLaneSymmetryProfile p17
  ∷ primeLaneSymmetryProfile p19
  ∷ primeLaneSymmetryProfile p23
  ∷ primeLaneSymmetryProfile p29
  ∷ primeLaneSymmetryProfile p31
  ∷ primeLaneSymmetryProfile p41
  ∷ primeLaneSymmetryProfile p47
  ∷ primeLaneSymmetryProfile p59
  ∷ primeLaneSymmetryProfile p71
  ∷ []

p7PrimeLaneSymmetryProfile : PrimeLaneSymmetryProfile
p7PrimeLaneSymmetryProfile = primeLaneSymmetryProfile p7

p11PrimeLaneSymmetryProfile : PrimeLaneSymmetryProfile
p11PrimeLaneSymmetryProfile = primeLaneSymmetryProfile p11

p7UnitOrderIs6 : unitOrder p7PrimeLaneSymmetryProfile ≡ 6
p7UnitOrderIs6 = refl

p11UnitOrderIs10 : unitOrder p11PrimeLaneSymmetryProfile ≡ 10
p11UnitOrderIs10 = refl

p7AdditiveStageIs7 : additiveStage p7PrimeLaneSymmetryProfile ≡ atlas-7
p7AdditiveStageIs7 = refl

p7UnitStageIs6 : unitStage p7PrimeLaneSymmetryProfile ≡ atlas-6
p7UnitStageIs6 = refl

p11AdditiveStageIs11 : additiveStage p11PrimeLaneSymmetryProfile ≡ atlas-11
p11AdditiveStageIs11 = refl

p11UnitStageIs10 : unitStage p11PrimeLaneSymmetryProfile ≡ atlas-10
p11UnitStageIs10 = refl
