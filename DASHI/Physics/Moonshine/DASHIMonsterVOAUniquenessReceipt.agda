module DASHI.Physics.Moonshine.DASHIMonsterVOAUniquenessReceipt where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- DASHI Monster VOA uniqueness receipt surface.
--
-- Paper 2 P2-B records only an authority route:
--
--   FLM construct the Monster VOA V^natural.
--   van Ekeren-Moller-Scheithauer 2017 classify the relevant c=24
--   holomorphic VOA/orbifold uniqueness route.
--
-- This module is deliberately a citation/receipt surface.  It does not
-- construct a VOA, prove the FLM construction, prove the EMS classification,
-- identify a DASHI prime lane by theorem, or flip any terminal/Clay status.

data DASHIMonsterVOAUniquenessStatus : Set where
  authorityReceiptOnlyNoTerminalPromotion :
    DASHIMonsterVOAUniquenessStatus

data DASHIMonsterVOAUniquenessPromotionAuthorityToken : Set where

data DASHIMonsterVOAUniquenessCitation : Set where
  flmMonsterVOAConstructionCitation :
    DASHIMonsterVOAUniquenessCitation

  vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessCitation :
    DASHIMonsterVOAUniquenessCitation

data DASHIMonsterVOAUniquenessBoundary : Set where
  boundaryAuthorityCitationOnly :
    DASHIMonsterVOAUniquenessBoundary

  boundaryNoVOAConstruction :
    DASHIMonsterVOAUniquenessBoundary

  boundaryNoFLMProof :
    DASHIMonsterVOAUniquenessBoundary

  boundaryNoEMS2017ClassificationProof :
    DASHIMonsterVOAUniquenessBoundary

  boundaryNoPrimeLaneEquivalencePromotion :
    DASHIMonsterVOAUniquenessBoundary

  boundaryNoTerminalClaimPromotion :
    DASHIMonsterVOAUniquenessBoundary

  boundaryNoClayStatusFlip :
    DASHIMonsterVOAUniquenessBoundary

canonicalDASHIMonsterVOAUniquenessBoundaries :
  List DASHIMonsterVOAUniquenessBoundary
canonicalDASHIMonsterVOAUniquenessBoundaries =
  boundaryAuthorityCitationOnly
  ∷ boundaryNoVOAConstruction
  ∷ boundaryNoFLMProof
  ∷ boundaryNoEMS2017ClassificationProof
  ∷ boundaryNoPrimeLaneEquivalencePromotion
  ∷ boundaryNoTerminalClaimPromotion
  ∷ boundaryNoClayStatusFlip
  ∷ []

record DASHIMonsterVOAUniquenessAuthorityReceipt : Set where
  field
    citation :
      DASHIMonsterVOAUniquenessCitation

    authorityLabel :
      String

    acceptedAsExternalAuthority :
      Bool

    acceptedAsExternalAuthorityIsTrue :
      acceptedAsExternalAuthority ≡ true

open DASHIMonsterVOAUniquenessAuthorityReceipt public

postulate
  flmMonsterVOAConstructionAuthority :
    DASHIMonsterVOAUniquenessAuthorityReceipt

  vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessAuthority :
    DASHIMonsterVOAUniquenessAuthorityReceipt

data C24HolomorphicVOATarget : Set where
  c24HolomorphicVOA :
    C24HolomorphicVOATarget

data MonsterVOATarget : Set where
  flmMonsterVOAVNatural :
    MonsterVOATarget

data MonsterOrbifoldTarget : Set where
  vNaturalOrbifoldC24Target :
    MonsterOrbifoldTarget

data C24VOAOrbifoldUniquenessRoute : Set where
  flmMonsterVOAThenEMS2017C24OrbifoldRoute :
    C24VOAOrbifoldUniquenessRoute

record C24VOAIsMonsterOrbifoldAuthority : Set where
  field
    c24VOA :
      C24HolomorphicVOATarget

    monsterVOA :
      MonsterVOATarget

    monsterOrbifold :
      MonsterOrbifoldTarget

    uniquenessRoute :
      C24VOAOrbifoldUniquenessRoute

    flmAuthority :
      DASHIMonsterVOAUniquenessAuthorityReceipt

    ems2017Authority :
      DASHIMonsterVOAUniquenessAuthorityReceipt

    authorityCitations :
      List DASHIMonsterVOAUniquenessCitation

    authorityCitationsAreCanonical :
      authorityCitations
      ≡
      (flmMonsterVOAConstructionCitation
       ∷
       vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessCitation
       ∷
       [])

    identifiesC24VOAWithMonsterOrbifold :
      Bool

    identifiesC24VOAWithMonsterOrbifoldIsTrue :
      identifiesC24VOAWithMonsterOrbifold ≡ true

    authorityCitationOnly :
      Bool

    authorityCitationOnlyIsTrue :
      authorityCitationOnly ≡ true

open C24VOAIsMonsterOrbifoldAuthority public

c24VOAIsMonsterOrbifoldAuthority :
  C24VOAIsMonsterOrbifoldAuthority
c24VOAIsMonsterOrbifoldAuthority =
  record
    { c24VOA =
        c24HolomorphicVOA
    ; monsterVOA =
        flmMonsterVOAVNatural
    ; monsterOrbifold =
        vNaturalOrbifoldC24Target
    ; uniquenessRoute =
        flmMonsterVOAThenEMS2017C24OrbifoldRoute
    ; flmAuthority =
        flmMonsterVOAConstructionAuthority
    ; ems2017Authority =
        vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessAuthority
    ; authorityCitations =
        flmMonsterVOAConstructionCitation
        ∷ vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessCitation
        ∷ []
    ; authorityCitationsAreCanonical =
        refl
    ; identifiesC24VOAWithMonsterOrbifold =
        true
    ; identifiesC24VOAWithMonsterOrbifoldIsTrue =
        refl
    ; authorityCitationOnly =
        true
    ; authorityCitationOnlyIsTrue =
        refl
    }

record DASHIMonsterVOAUniquenessReceipt : Set where
  field
    status :
      DASHIMonsterVOAUniquenessStatus

    c24VOAIsMonsterOrbifold :
      C24VOAIsMonsterOrbifoldAuthority

    canonicalRoute :
      C24VOAOrbifoldUniquenessRoute

    canonicalRoute-v :
      canonicalRoute
      ≡
      flmMonsterVOAThenEMS2017C24OrbifoldRoute

    citedAuthorities :
      List DASHIMonsterVOAUniquenessAuthorityReceipt

    c24VOA :
      C24HolomorphicVOATarget

    monsterVOA :
      MonsterVOATarget

    monsterOrbifold :
      MonsterOrbifoldTarget

    reusableByPrimeLaneVOAEquivalenceReceiptSurface :
      Bool

    reusableByPrimeLaneVOAEquivalenceReceiptSurfaceIsTrue :
      reusableByPrimeLaneVOAEquivalenceReceiptSurface ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayStatusFlipped :
      Bool

    clayStatusFlippedIsFalse :
      clayStatusFlipped ≡ false

    boundaries :
      List DASHIMonsterVOAUniquenessBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalDASHIMonsterVOAUniquenessBoundaries

    noPromotionWithoutAuthority :
      DASHIMonsterVOAUniquenessPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open DASHIMonsterVOAUniquenessReceipt public

canonicalDASHIMonsterVOAUniquenessReceipt :
  DASHIMonsterVOAUniquenessReceipt
canonicalDASHIMonsterVOAUniquenessReceipt =
  record
    { status =
        authorityReceiptOnlyNoTerminalPromotion
    ; c24VOAIsMonsterOrbifold =
        c24VOAIsMonsterOrbifoldAuthority
    ; canonicalRoute =
        flmMonsterVOAThenEMS2017C24OrbifoldRoute
    ; canonicalRoute-v =
        refl
    ; citedAuthorities =
        flmMonsterVOAConstructionAuthority
        ∷ vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessAuthority
        ∷ []
    ; c24VOA =
        c24HolomorphicVOA
    ; monsterVOA =
        flmMonsterVOAVNatural
    ; monsterOrbifold =
        vNaturalOrbifoldC24Target
    ; reusableByPrimeLaneVOAEquivalenceReceiptSurface =
        true
    ; reusableByPrimeLaneVOAEquivalenceReceiptSurfaceIsTrue =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayStatusFlipped =
        false
    ; clayStatusFlippedIsFalse =
        refl
    ; boundaries =
        canonicalDASHIMonsterVOAUniquenessBoundaries
    ; boundariesAreCanonical =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "P2-B records the external uniqueness route only: FLM Monster VOA plus van Ekeren-Moller-Scheithauer 2017 c=24 holomorphic VOA/orbifold uniqueness"
        ∷ "c24VOAIsMonsterOrbifoldAuthority is an authority-citation receipt, not a local VOA construction or classification proof"
        ∷ "The receipt is reusable by PrimeLaneVOAEquivalenceReceiptSurface as a named authority input"
        ∷ "No DASHI prime-lane equivalence theorem, terminal claim promotion, or Clay-status flip is exported here"
        ∷ []
    }

DASHIMonsterVOAUniquenessReceiptSurface :
  Set
DASHIMonsterVOAUniquenessReceiptSurface =
  DASHIMonsterVOAUniquenessReceipt

canonicalDASHIMonsterVOAUniquenessReceiptSurface :
  DASHIMonsterVOAUniquenessReceiptSurface
canonicalDASHIMonsterVOAUniquenessReceiptSurface =
  canonicalDASHIMonsterVOAUniquenessReceipt

monsterVOAUniquenessReusableByPrimeLaneVOAEquivalence :
  Bool
monsterVOAUniquenessReusableByPrimeLaneVOAEquivalence =
  reusableByPrimeLaneVOAEquivalenceReceiptSurface
    canonicalDASHIMonsterVOAUniquenessReceipt

monsterVOAUniquenessReusableByPrimeLaneVOAEquivalenceIsTrue :
  monsterVOAUniquenessReusableByPrimeLaneVOAEquivalence ≡ true
monsterVOAUniquenessReusableByPrimeLaneVOAEquivalenceIsTrue =
  refl

monsterVOAUniquenessTheoremPromoted :
  Bool
monsterVOAUniquenessTheoremPromoted =
  theoremPromoted canonicalDASHIMonsterVOAUniquenessReceipt

monsterVOAUniquenessTheoremPromotedIsFalse :
  monsterVOAUniquenessTheoremPromoted ≡ false
monsterVOAUniquenessTheoremPromotedIsFalse =
  refl

monsterVOAUniquenessTerminalClaimPromoted :
  Bool
monsterVOAUniquenessTerminalClaimPromoted =
  terminalClaimPromoted canonicalDASHIMonsterVOAUniquenessReceipt

monsterVOAUniquenessTerminalClaimPromotedIsFalse :
  monsterVOAUniquenessTerminalClaimPromoted ≡ false
monsterVOAUniquenessTerminalClaimPromotedIsFalse =
  refl

monsterVOAUniquenessClayStatusFlipped :
  Bool
monsterVOAUniquenessClayStatusFlipped =
  clayStatusFlipped canonicalDASHIMonsterVOAUniquenessReceipt

monsterVOAUniquenessClayStatusFlippedIsFalse :
  monsterVOAUniquenessClayStatusFlipped ≡ false
monsterVOAUniquenessClayStatusFlippedIsFalse =
  refl
