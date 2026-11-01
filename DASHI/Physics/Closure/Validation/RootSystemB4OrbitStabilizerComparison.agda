module DASHI.Physics.Closure.Validation.RootSystemB4OrbitStabilizerComparison where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; map; filterᵇ; length)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Integer.Base using (ℤ)
open import Relation.Nullary using (Dec; yes; no)

open import DASHI.Physics.OrbitProfileComputed as OPC using (nub)
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPSP hiding (nub)
open import DASHI.Physics.RootSystemB4Carrier as B4
open import DASHI.Physics.RootSystemB4WeylAction as W
open import DASHI.Physics.SignedPerm4 as SP

data ShiftShellClass : Set where
  shiftShell1-24 : ShiftShellClass
  shiftShell1-6 : ShiftShellClass
  shiftShell1-2 : ShiftShellClass
  shiftShell2-16 : ShiftShellClass
  shiftShell2-12 : ShiftShellClass

shiftRepresentative : ShiftShellClass → B4.B4Point
shiftRepresentative shiftShell1-24 = B4.pt B4.p1 B4.p1 B4.n1 B4.z
shiftRepresentative shiftShell1-6 = B4.pt B4.z B4.n1 B4.z B4.z
shiftRepresentative shiftShell1-2 = B4.pt B4.p1 B4.z B4.z B4.z
shiftRepresentative shiftShell2-16 = B4.pt B4.p1 B4.n1 B4.n1 B4.n1
shiftRepresentative shiftShell2-12 = B4.pt B4.z B4.n1 B4.z B4.p1

flipBy3Shift : Vec Bool 3 → Vec ℤ 3 → Vec ℤ 3
flipBy3Shift (f1 ∷ f2 ∷ f3 ∷ []) (a ∷ b ∷ c ∷ []) =
  W.flipInt f1 a ∷ W.flipInt f2 b ∷ W.flipInt f3 c ∷ []

actShift : SP.SignedPerm4 → B4.B4Point → B4.B4Point
actShift sp (t ∷ s1 ∷ s2 ∷ s3 ∷ []) =
  W.flipInt (SP.SignedPerm4.flipT sp) t ∷
  flipBy3Shift
    (SP.SignedPerm4.flipS sp)
    (SP.permute3 (SP.SignedPerm4.perm sp) (s1 ∷ s2 ∷ s3 ∷ []))

orbitUnder :
  ∀ {G X : Set} →
  ((x y : X) → Dec (x ≡ y)) →
  List G →
  (G → X → X) →
  X →
  List X
orbitUnder dec gs act x = nub dec (map (λ g → act g x) gs)

fixesPoint :
  ∀ {G X : Set} →
  ((x y : X) → Dec (x ≡ y)) →
  (G → X → X) →
  G →
  X →
  Bool
fixesPoint dec act g x with dec (act g x) x
... | yes _ = true
... | no _ = false

stabilizerUnder :
  ∀ {G X : Set} →
  ((x y : X) → Dec (x ≡ y)) →
  List G →
  (G → X → X) →
  X →
  List G
stabilizerUnder dec gs act x = filterᵇ (λ g → fixesPoint dec act g x) gs

shiftOrbit : ShiftShellClass → List B4.B4Point
shiftOrbit c =
  orbitUnder B4.decEqB4Point OPSP.allSignedPerm4 actShift (shiftRepresentative c)

shiftStabilizer : ShiftShellClass → List SP.SignedPerm4
shiftStabilizer c =
  stabilizerUnder B4.decEqB4Point OPSP.allSignedPerm4 actShift (shiftRepresentative c)

b4Orbit : ShiftShellClass → List B4.B4Point
b4Orbit c =
  orbitUnder B4.decEqB4Point W.allWeylB4 W.actWeyl (shiftRepresentative c)

b4Stabilizer : ShiftShellClass → List W.WeylB4
b4Stabilizer c =
  stabilizerUnder B4.decEqB4Point W.allWeylB4 W.actWeyl (shiftRepresentative c)

shiftOrbitSize : ShiftShellClass → Nat
shiftOrbitSize c = length (shiftOrbit c)

shiftStabilizerSize : ShiftShellClass → Nat
shiftStabilizerSize c = length (shiftStabilizer c)

b4OrbitSize : ShiftShellClass → Nat
b4OrbitSize c = length (b4Orbit c)

b4StabilizerSize : ShiftShellClass → Nat
b4StabilizerSize c = length (b4Stabilizer c)

shiftGroupOrder : Nat
shiftGroupOrder = length OPSP.allSignedPerm4

b4GroupOrder : Nat
b4GroupOrder = length W.allWeylB4

record OrbitStabilizerComparison : Set₁ where
  field
    class : ShiftShellClass
    representative : B4.B4Point
    shiftOrbitStates : List B4.B4Point
    shiftStabilizerStates : List SP.SignedPerm4
    b4OrbitStates : List B4.B4Point
    b4StabilizerStates : List W.WeylB4
    shiftOrbitCardinality : Nat
    shiftStabilizerCardinality : Nat
    b4OrbitCardinality : Nat
    b4StabilizerCardinality : Nat

comparison : ShiftShellClass → OrbitStabilizerComparison
comparison c =
  record
    { class = c
    ; representative = shiftRepresentative c
    ; shiftOrbitStates = shiftOrbit c
    ; shiftStabilizerStates = shiftStabilizer c
    ; b4OrbitStates = b4Orbit c
    ; b4StabilizerStates = b4Stabilizer c
    ; shiftOrbitCardinality = shiftOrbitSize c
    ; shiftStabilizerCardinality = shiftStabilizerSize c
    ; b4OrbitCardinality = b4OrbitSize c
    ; b4StabilizerCardinality = b4StabilizerSize c
    }

shiftOrbitStabilizerLaw :
  ∀ c →
  shiftOrbitSize c * shiftStabilizerSize c ≡ shiftGroupOrder
shiftOrbitStabilizerLaw shiftShell1-24 = refl
shiftOrbitStabilizerLaw shiftShell1-6 = refl
shiftOrbitStabilizerLaw shiftShell1-2 = refl
shiftOrbitStabilizerLaw shiftShell2-16 = refl
shiftOrbitStabilizerLaw shiftShell2-12 = refl

b4OrbitStabilizerLaw :
  ∀ c →
  b4OrbitSize c * b4StabilizerSize c ≡ b4GroupOrder
b4OrbitStabilizerLaw shiftShell1-24 = refl
b4OrbitStabilizerLaw shiftShell1-6 = refl
b4OrbitStabilizerLaw shiftShell1-2 = refl
b4OrbitStabilizerLaw shiftShell2-16 = refl
b4OrbitStabilizerLaw shiftShell2-12 = refl
