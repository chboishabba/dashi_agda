module DASHI.Law.SensibLawWrongTypeGenericHyperfabricAdapterExact where

-- Thin adapter only. McNamara's (violated, imposed) claim is a source-
-- attributed observer, not the owner of the ontology hyperfabric.
-- Attribution: Rob McNamara, A System of Wrong, ep. 4, user-supplied
-- transcript 2026-09-30. Forrest Landry attribution as narrated only.
-- All extra coordinates, factorisation and compatibility demands are DASHI.
-- Classification alone creates no WrongType liability / custodial permission.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.SensibLawWrongTypeCareTransactionPowerGridExact as Grid
import DASHI.Interop.SensibLawOntologyTopology as Ontology

ModeAddress : Nat → Set
ModeAddress k = Core.Address Grid.Mode k

canonicalNineCount : Core.siteCount 3 2 ≡ 9
canonicalNineCount = Core.threeAxis9

canonicalCubeCount : Core.siteCount 3 3 ≡ 27
canonicalCubeCount = Core.threeAxis27

canonicalFourthAxisCount : Core.siteCount 3 4 ≡ 81
canonicalFourthAxisCount = Core.threeAxis81

-- No semantics are silently attached to later coordinates.
originalGridCell : ∀ {n} → ModeAddress (suc (suc n)) → Grid.Cell
originalGridCell (violated ∷ imposed ∷ rest) =
  Grid.cell violated imposed

record WrongTypeSituatedFibre (k : Nat) : Set₁ where
  field
    wrongType : Ontology.WrongType
    -- Actual classifications require separately proven event/context.
    Context : ModeAddress k → Set
    -- These producer interfaces cannot be filled from frame labels alone.
    SourceAuthority : ModeAddress k → Set
    LegalElements : ModeAddress k → Set
    CustodialAuthority : ModeAddress k → Set
    evidenceReference : String

-- Query-specific legal consumer over the generic spine.
record LegalConsumer
    {S V A : Set}
    (observe : S → V)
    (answer : S → A) : Set₁ where
  field
    adequate : Core.ConsumerSufficient observe answer
    LegalAuthority : Set
    authorityReceipt : LegalAuthority
    SourceRevision : Set
    sourceReceipt : SourceRevision

noGridOnlyPromotion :
  ∀ {S A : Set}
    (observe : S → Grid.Cell)
    (answer : S → A) →
  Core.ConsumerCollision observe answer →
  Core.ConsumerSufficient observe answer → ⊥
noGridOnlyPromotion observe answer witness =
  Core.collisionRefutesSufficiency witness

-- The generic length-k carrier is reusable for Care/Transaction/Power;
-- additional protected interests, traditions and historical measures
-- live in indexed fibres instead of forcibly becoming ternary modes.
