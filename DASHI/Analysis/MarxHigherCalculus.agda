module DASHI.Analysis.MarxHigherCalculus where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)

open import DASHI.Analysis.MarxDifferentialCore public
open import DASHI.Algebra.Jacobian.InvertibilityStrata
  using (PromotionBoundary; canonicalPromotionBoundary)
open import Verification.JacobianCounterexampleKernel
  using (¬_; JacobianConjectureDimension3; jacobianConjectureDimension3False)

------------------------------------------------------------------------
-- Iterated scalar derivatives.

iterateDerivative :
  {A : MarxAlgebra} →
  (D : Function A → Function A) →
  Nat → Function A → Function A
iterateDerivative D zero f = f
iterateDerivative D (suc n) f = D (iterateDerivative D n f)

iterateDerivativeZero :
  {A : MarxAlgebra} →
  (D : Function A → Function A) →
  (f : Function A) →
  iterateDerivative D zero f ≡ f
iterateDerivativeZero D f = refl

iterateDerivativeSuccessor :
  {A : MarxAlgebra} →
  (D : Function A → Function A) →
  (n : Nat) →
  (f : Function A) →
  iterateDerivative D (suc n) f ≡ D (iterateDerivative D n f)
iterateDerivativeSuccessor D n f = refl

record ClosedMarxDifferentialFamily
  (A : MarxAlgebra)
  : Set₁ where
  field
    admissible : Function A → Set
    factorise :
      (f : Function A) →
      admissible f →
      MarxFactorisation A f
    derivativeClosed :
      (f : Function A) →
      (pf : admissible f) →
      admissible (marxDerivative (factorise f pf))

open ClosedMarxDifferentialFamily public

familyDerivative :
  {A : MarxAlgebra} →
  (C : ClosedMarxDifferentialFamily A) →
  (f : Function A) →
  admissible C f →
  Function A
familyDerivative C f pf = marxDerivative (factorise C f pf)

record HigherDerivativeTower
  {A : MarxAlgebra}
  (C : ClosedMarxDifferentialFamily A)
  (f : Function A)
  : Set₁ where
  field
    baseAdmissible : admissible C f
    derivativeAtOrder : Nat → Function A
    admissibleAtOrder :
      (n : Nat) → admissible C (derivativeAtOrder n)
    orderZero : derivativeAtOrder zero ≡ f
    orderSuccessor :
      ∀ n →
      derivativeAtOrder (suc n)
      ≡ familyDerivative C
          (derivativeAtOrder n)
          (admissibleAtOrder n)

------------------------------------------------------------------------
-- Taylor coefficient carrier.

record TaylorCoefficientStructure
  (A : MarxAlgebra)
  : Set₁ where
  field
    factorial : Nat → Carrier A
    divide : Carrier A → Carrier A → Carrier A
    denominatorAdmissible : Nat → Set

open TaylorCoefficientStructure public

record TaylorExpansionData
  {A : MarxAlgebra}
  (T : TaylorCoefficientStructure A)
  (derivativeAtOrder : Nat → Function A)
  (centre : Carrier A)
  : Set₁ where
  field
    coefficient : Nat → Carrier A
    coefficientLaw :
      ∀ n →
      coefficient n
      ≡ divide T
          (derivativeAtOrder n centre)
          (factorial T n)

------------------------------------------------------------------------
-- Modules and genuine linear maps.

record Module
  (A : MarxAlgebra)
  : Set₁ where
  infixl 20 _+V_
  infixr 30 _•_
  field
    Vector : Set
    zeroV : Vector
    _+V_ : Vector → Vector → Vector
    _•_ : Carrier A → Vector → Vector

    addZeroLeftV : ∀ v → zeroV +V v ≡ v
    addZeroRightV : ∀ v → v +V zeroV ≡ v
    addAssocV : ∀ u v w → (u +V v) +V w ≡ u +V (v +V w)
    addInterchangeV :
      ∀ a b c d →
      (a +V b) +V (c +V d)
      ≡ (a +V c) +V (b +V d)

    scaleZeroV : ∀ scalar → scalar • zeroV ≡ zeroV
    scaleOneV : ∀ v → one A • v ≡ v
    scaleDistributesAddV :
      ∀ scalar u v →
      scalar • (u +V v) ≡ (scalar • u) +V (scalar • v)

open Module public

record LinearMap
  (A : MarxAlgebra)
  (V W : Module A)
  : Set₁ where
  field
    apply : Vector V → Vector W
    mapZero : apply (zeroV V) ≡ zeroV W
    mapAdd :
      ∀ u v →
      apply (_+V_ V u v)
      ≡ _+V_ W (apply u) (apply v)
    mapScale :
      ∀ scalar v →
      apply (_•_ V scalar v)
      ≡ _•_ W scalar (apply v)

open LinearMap public

linearIdentity :
  {A : MarxAlgebra} →
  (V : Module A) →
  LinearMap A V V
linearIdentity V =
  record
    { apply = λ v → v
    ; mapZero = refl
    ; mapAdd = λ _ _ → refl
    ; mapScale = λ _ _ → refl
    }

linearCompose :
  {A : MarxAlgebra} →
  {U V W : Module A} →
  LinearMap A V W →
  LinearMap A U V →
  LinearMap A U W
linearCompose F G =
  record
    { apply = λ u → apply F (apply G u)
    ; mapZero = trans (cong (apply F) (mapZero G)) (mapZero F)
    ; mapAdd = λ u v →
        trans
          (cong (apply F) (mapAdd G u v))
          (mapAdd F (apply G u) (apply G v))
    ; mapScale = λ scalar u →
        trans
          (cong (apply F) (mapScale G scalar u))
          (mapScale F scalar (apply G u))
    }

linearZero :
  {A : MarxAlgebra} →
  {V W : Module A} →
  LinearMap A V W
linearZero {W = W} =
  record
    { apply = λ _ → zeroV W
    ; mapZero = refl
    ; mapAdd = λ _ _ → sym (addZeroLeftV W (zeroV W))
    ; mapScale = λ scalar _ → sym (scaleZeroV W scalar)
    }

linearAdd :
  {A : MarxAlgebra} →
  {V W : Module A} →
  LinearMap A V W →
  LinearMap A V W →
  LinearMap A V W
linearAdd {W = W} F G =
  record
    { apply = λ v → _+V_ W (apply F v) (apply G v)
    ; mapZero =
        trans
          (cong₂ (_+V_ W) (mapZero F) (mapZero G))
          (addZeroLeftV W (zeroV W))
    ; mapAdd = λ u v →
        trans
          (cong₂ (_+V_ W) (mapAdd F u v) (mapAdd G u v))
          (addInterchangeV W
            (apply F u) (apply F v)
            (apply G u) (apply G v))
    ; mapScale = λ scalar v →
        trans
          (cong₂ (_+V_ W)
            (mapScale F scalar v)
            (mapScale G scalar v))
          (sym
            (scaleDistributesAddV W scalar (apply F v) (apply G v)))
    }

------------------------------------------------------------------------
-- Normed modules and bounded operators.

record OrderedScalar
  (A : MarxAlgebra)
  : Set₁ where
  infix 15 _≤S_
  field
    _≤S_ : Carrier A → Carrier A → Set
    leRefl : ∀ x → x ≤S x
    leTrans : ∀ {x y z} → x ≤S y → y ≤S z → x ≤S z

open OrderedScalar public

record NormedModule
  (A : MarxAlgebra)
  (O : OrderedScalar A)
  (V : Module A)
  : Set₁ where
  field
    norm : Vector V → Carrier A
    normNonnegative : ∀ v → _≤S_ O (zero A) (norm v)
    normZero : norm (zeroV V) ≡ zero A
    normTriangle :
      ∀ u v →
      _≤S_ O
        (norm (_+V_ V u v))
        (_+_ A (norm u) (norm v))

open NormedModule public

record BoundedLinearMap
  {A : MarxAlgebra}
  {O : OrderedScalar A}
  {V W : Module A}
  (NV : NormedModule A O V)
  (NW : NormedModule A O W)
  : Set₁ where
  field
    linear : LinearMap A V W
    bound : Carrier A
    boundNonnegative : _≤S_ O (zero A) bound
    applyBound :
      ∀ v →
      _≤S_ O
        (norm NW (apply linear v))
        (_*_ A bound (norm NV v))

open BoundedLinearMap public

record OperatorNormReceipt
  {A : MarxAlgebra}
  {O : OrderedScalar A}
  {V W : Module A}
  (NV : NormedModule A O V)
  (NW : NormedModule A O W)
  (F : LinearMap A V W)
  : Set₁ where
  field
    operatorNorm : Carrier A
    operatorNormNonnegative : _≤S_ O (zero A) operatorNorm
    operatorApplyBound :
      ∀ v →
      _≤S_ O
        (norm NW (apply F v))
        (_*_ A operatorNorm (norm NV v))
    leastOperatorBound :
      ∀ candidate →
      (∀ v →
        _≤S_ O
          (norm NW (apply F v))
          (_*_ A candidate (norm NV v))) →
      _≤S_ O operatorNorm candidate

open OperatorNormReceipt public

record OperatorNormCompositionLaws
  {A : MarxAlgebra}
  {O : OrderedScalar A}
  {U V W : Module A}
  (NU : NormedModule A O U)
  (NV : NormedModule A O V)
  (NW : NormedModule A O W)
  (F : LinearMap A V W)
  (G : LinearMap A U V)
  : Set₁ where
  field
    composeOperatorNorm :
      OperatorNormReceipt NV NW F →
      OperatorNormReceipt NU NV G →
      OperatorNormReceipt NU NW (linearCompose F G)

------------------------------------------------------------------------
-- Vector little-o and Frechet differentiation.

record VectorLittleOStructure
  (A : MarxAlgebra)
  (V W : Module A)
  : Set₁ where
  field
    LittleO : (Vector V → Vector W) → Set
    zeroLittleO : LittleO (λ _ → zeroV W)
    addLittleO :
      ∀ {r s} →
      LittleO r →
      LittleO s →
      LittleO (λ h → _+V_ W (r h) (s h))
    linearImageLittleO :
      ∀ {Z : Module A}
        (L : LinearMap A W Z)
        {r : Vector V → Vector W} →
      LittleO r →
      VectorLittleOStructure.LittleO
        (record
          { LittleO = λ q → Set
          ; zeroLittleO = Set
          ; addLittleO = λ _ _ → Set
          ; linearImageLittleO = λ _ _ → Set
          })
        (λ h → apply L (r h))

-- The generic linear-image field above cannot be inhabited without selecting
-- a target little-o structure.  The usable cross-space version is explicit:
record LittleOTransport
  {A : MarxAlgebra}
  {U V W : Module A}
  (RUV : VectorLittleOStructure A U V)
  (RUW : VectorLittleOStructure A U W)
  (L : LinearMap A V W)
  : Set₁ where
  field
    transportLittleO :
      ∀ {r} →
      VectorLittleOStructure.LittleO RUV r →
      VectorLittleOStructure.LittleO RUW (λ h → apply L (r h))

open VectorLittleOStructure public
open LittleOTransport public

record FrechetDerivativeAt
  {A : MarxAlgebra}
  {V W : Module A}
  (R : VectorLittleOStructure A V W)
  (f : Vector V → Vector W)
  (x : Vector V)
  : Set₁ where
  field
    derivative : LinearMap A V W
    remainder : Vector V → Vector W
    expansion :
      ∀ h →
      f (_+V_ V x h)
      ≡ _+V_ W
          (f x)
          (_+V_ W (apply derivative h) (remainder h))
    remainderLittleO : LittleO R remainder

open FrechetDerivativeAt public

frechetIdentity :
  {A : MarxAlgebra} →
  {V : Module A} →
  (R : VectorLittleOStructure A V V) →
  (x : Vector V) →
  FrechetDerivativeAt R (λ v → v) x
frechetIdentity {V = V} R x =
  record
    { derivative = linearIdentity V
    ; remainder = λ _ → zeroV V
    ; expansion = λ h →
        cong (λ tail → _+V_ V x tail)
          (sym (addZeroRightV V h))
    ; remainderLittleO = zeroLittleO R
    }

frechetConstant :
  {A : MarxAlgebra} →
  {V W : Module A} →
  (R : VectorLittleOStructure A V W) →
  (constant : Vector W) →
  (x : Vector V) →
  FrechetDerivativeAt R (λ _ → constant) x
frechetConstant {W = W} R constant x =
  record
    { derivative = linearZero
    ; remainder = λ _ → zeroV W
    ; expansion = λ h →
        sym
          (trans
            (cong (λ tail → _+V_ W constant tail)
              (addZeroLeftV W (zeroV W)))
            (addZeroRightV W constant))
    ; remainderLittleO = zeroLittleO R
    }

record FrechetAddExpansionLaws
  {A : MarxAlgebra}
  {V W : Module A}
  (R : VectorLittleOStructure A V W)
  : Set₁ where
  field
    combineSumExpansion :
      {f g : Vector V → Vector W} →
      {x : Vector V} →
      (F : FrechetDerivativeAt R f x) →
      (G : FrechetDerivativeAt R g x) →
      ∀ h →
      _+V_ W (f (_+V_ V x h)) (g (_+V_ V x h))
      ≡ _+V_ W
          (_+V_ W (f x) (g x))
          (_+V_ W
            (apply (linearAdd (derivative F) (derivative G)) h)
            (_+V_ W (remainder F h) (remainder G h)))

open FrechetAddExpansionLaws public

frechetSum :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  FrechetAddExpansionLaws R →
  {f g : Vector V → Vector W} →
  {x : Vector V} →
  FrechetDerivativeAt R f x →
  FrechetDerivativeAt R g x →
  FrechetDerivativeAt R (λ y → _+V_ W (f y) (g y)) x
frechetSum laws F G =
  record
    { derivative = linearAdd (derivative F) (derivative G)
    ; remainder = λ h → _+V_ _ (remainder F h) (remainder G h)
    ; expansion = combineSumExpansion laws F G
    ; remainderLittleO = addLittleO _ (remainderLittleO F) (remainderLittleO G)
    }

record FrechetDerivativeUniqueness
  {A : MarxAlgebra}
  {V W : Module A}
  (R : VectorLittleOStructure A V W)
  : Set₁ where
  field
    frechetDerivativeUnique :
      {f : Vector V → Vector W} →
      {x : Vector V} →
      (F G : FrechetDerivativeAt R f x) →
      derivative F ≡ derivative G

open FrechetDerivativeUniqueness public

record FrechetChainRuleData
  {A : MarxAlgebra}
  {U V W : Module A}
  (RUV : VectorLittleOStructure A U V)
  (RVW : VectorLittleOStructure A V W)
  (RUW : VectorLittleOStructure A U W)
  {f : Vector V → Vector W}
  {g : Vector U → Vector V}
  {x : Vector U}
  (F : FrechetDerivativeAt RVW f (g x))
  (G : FrechetDerivativeAt RUV g x)
  : Set₁ where
  field
    chainRemainder : Vector U → Vector W
    chainExpansion :
      ∀ h →
      f (g (_+V_ U x h))
      ≡ _+V_ W
          (f (g x))
          (_+V_ W
            (apply (linearCompose (derivative F) (derivative G)) h)
            (chainRemainder h))
    chainRemainderLittleO : LittleO RUW chainRemainder

open FrechetChainRuleData public

frechetChainRule :
  {A : MarxAlgebra} →
  {U V W : Module A} →
  {RUV : VectorLittleOStructure A U V} →
  {RVW : VectorLittleOStructure A V W} →
  {RUW : VectorLittleOStructure A U W} →
  {f : Vector V → Vector W} →
  {g : Vector U → Vector V} →
  {x : Vector U} →
  (F : FrechetDerivativeAt RVW f (g x)) →
  (G : FrechetDerivativeAt RUV g x) →
  FrechetChainRuleData RUV RVW RUW F G →
  FrechetDerivativeAt RUW (λ u → f (g u)) x
frechetChainRule F G data =
  record
    { derivative = linearCompose (derivative F) (derivative G)
    ; remainder = chainRemainder data
    ; expansion = chainExpansion data
    ; remainderLittleO = chainRemainderLittleO data
    }

------------------------------------------------------------------------
-- Directional derivatives are applications of the Frechet derivative.

DirectionalDerivativeAt :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  {f : Vector V → Vector W} →
  {x : Vector V} →
  FrechetDerivativeAt R f x →
  Vector V → Vector W
DirectionalDerivativeAt F direction = apply (derivative F) direction

directionalAdd :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  {f : Vector V → Vector W} →
  {x : Vector V} →
  (F : FrechetDerivativeAt R f x) →
  ∀ u v →
  DirectionalDerivativeAt F (_+V_ V u v)
  ≡ _+V_ W (DirectionalDerivativeAt F u) (DirectionalDerivativeAt F v)
directionalAdd F = mapAdd (derivative F)

directionalScale :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  {f : Vector V → Vector W} →
  {x : Vector V} →
  (F : FrechetDerivativeAt R f x) →
  ∀ scalar v →
  DirectionalDerivativeAt F (_•_ V scalar v)
  ≡ _•_ W scalar (DirectionalDerivativeAt F v)
directionalScale F = mapScale (derivative F)

------------------------------------------------------------------------
-- Finite-coordinate Jacobians.

record FiniteBasis
  {A : MarxAlgebra}
  (V : Module A)
  : Set₁ where
  field
    Index : Set
    basis : Index → Vector V

open FiniteBasis public

record CoordinateFunctional
  {A : MarxAlgebra}
  (W : Module A)
  : Set₁ where
  field
    Row : Set
    coordinate : Row → Vector W → Carrier A

open CoordinateFunctional public

record JacobianAt
  {A : MarxAlgebra}
  {V W : Module A}
  (BV : FiniteBasis V)
  (CW : CoordinateFunctional W)
  : Set₁ where
  field
    entry : Row CW → Index BV → Carrier A

open JacobianAt public

jacobianFromFrechet :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  {f : Vector V → Vector W} →
  {x : Vector V} →
  (BV : FiniteBasis V) →
  (CW : CoordinateFunctional W) →
  FrechetDerivativeAt R f x →
  JacobianAt BV CW
jacobianFromFrechet BV CW F =
  record
    { entry = λ row column →
        coordinate CW row
          (apply (derivative F) (basis BV column))
    }

jacobianRepresentsFrechet :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  {f : Vector V → Vector W} →
  {x : Vector V} →
  (BV : FiniteBasis V) →
  (CW : CoordinateFunctional W) →
  (F : FrechetDerivativeAt R f x) →
  ∀ row column →
  entry (jacobianFromFrechet BV CW F) row column
  ≡ coordinate CW row
      (apply (derivative F) (basis BV column))
jacobianRepresentsFrechet BV CW F row column = refl

record JacobianChainRuleReceipt
  {A : MarxAlgebra}
  {U V W : Module A}
  (BU : FiniteBasis U)
  (BV : FiniteBasis V)
  (CW : CoordinateFunctional W)
  (composite : JacobianAt BU CW)
  : Set₁ where
  field
    MiddleIndex : Set
    matrixProductEntry : Row CW → Index BU → Carrier A
    jacobianChainRule :
      ∀ row column →
      entry composite row column ≡ matrixProductEntry row column

-- Repository-wide boundary: a nonsingular/constant Jacobian remains local
-- differential data.  The checked three-dimensional collision refutes the
-- promotion to global injectivity.

constantJacobianDoesNotEntailGlobalInjectivity :
  ¬ JacobianConjectureDimension3
constantJacobianDoesNotEntailGlobalInjectivity =
  jacobianConjectureDimension3False

jacobianPromotionBoundary : PromotionBoundary
jacobianPromotionBoundary = canonicalPromotionBoundary

------------------------------------------------------------------------
-- Higher-calculus completion bundle.

record MarxHigherCalculusBundle : Set₁ where
  field
    algebra : MarxAlgebra
    closedFamily : ClosedMarxDifferentialFamily algebra
    taylor : TaylorCoefficientStructure algebra
    vectorModule : Module algebra
    vectorLittleO : VectorLittleOStructure algebra vectorModule vectorModule
    frechetFamily :
      (f : Vector vectorModule → Vector vectorModule) →
      (x : Vector vectorModule) →
      FrechetDerivativeAt vectorLittleO f x
