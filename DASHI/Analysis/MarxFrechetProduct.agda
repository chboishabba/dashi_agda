module DASHI.Analysis.MarxFrechetProduct where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxHigherCalculus

------------------------------------------------------------------------
-- A bilinear multiplication on the codomain.  This is separate from the
-- scalar multiplication of a Module: vector-valued product rules require an
-- actual selected bilinear product such as scalar multiplication, matrix
-- multiplication, convolution, or an algebra product.

record BilinearProduct
  (A : MarxAlgebra)
  (W : Module A)
  : Set₁ where
  field
    product : Vector W → Vector W → Vector W

    productZeroLeft :
      ∀ w → product (zeroV W) w ≡ zeroV W

    productZeroRight :
      ∀ w → product w (zeroV W) ≡ zeroV W

    productAddLeft :
      ∀ u v w →
      product (_+V_ W u v) w
      ≡ _+V_ W (product u w) (product v w)

    productAddRight :
      ∀ u v w →
      product u (_+V_ W v w)
      ≡ _+V_ W (product u v) (product u w)

    productScaleLeft :
      ∀ scalar u v →
      product (_•_ W scalar u) v
      ≡ _•_ W scalar (product u v)

    productScaleRight :
      ∀ scalar u v →
      product u (_•_ W scalar v)
      ≡ _•_ W scalar (product u v)

open BilinearProduct public

multiplyVectorFunctions :
  {A : MarxAlgebra} →
  {V W : Module A} →
  BilinearProduct A W →
  (Vector V → Vector W) →
  (Vector V → Vector W) →
  Vector V → Vector W
multiplyVectorFunctions B f g x = product B (f x) (g x)

------------------------------------------------------------------------
-- The derivative is h |-> Df(h)*g(x) + f(x)*Dg(h).
--
-- The linearity proof and second-order/little-o remainder proof are packaged as
-- explicit construction data because they depend on the selected bilinear
-- product and little-o closure laws.  The resulting theorem itself is an exact
-- constructor, not a marker proposition.

record FrechetProductConstruction
  {A : MarxAlgebra}
  {V W : Module A}
  (R : VectorLittleOStructure A V W)
  (B : BilinearProduct A W)
  {f g : Vector V → Vector W}
  {x : Vector V}
  (F : FrechetDerivativeAt R f x)
  (G : FrechetDerivativeAt R g x)
  : Set₁ where
  field
    productLinear : LinearMap A V W

    productLinearPointwise :
      ∀ h →
      apply productLinear h
      ≡ _+V_ W
          (product B (apply (derivative F) h) (g x))
          (product B (f x) (apply (derivative G) h))

    productRemainder : Vector V → Vector W

    productExpansion :
      ∀ h →
      product B
        (f (_+V_ V x h))
        (g (_+V_ V x h))
      ≡ _+V_ W
          (product B (f x) (g x))
          (_+V_ W
            (apply productLinear h)
            (productRemainder h))

    productRemainderLittleO : LittleO R productRemainder

open FrechetProductConstruction public

frechetProduct :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  (B : BilinearProduct A W) →
  {f g : Vector V → Vector W} →
  {x : Vector V} →
  (F : FrechetDerivativeAt R f x) →
  (G : FrechetDerivativeAt R g x) →
  FrechetProductConstruction R B F G →
  FrechetDerivativeAt R (multiplyVectorFunctions B f g) x
frechetProduct B F G construction =
  record
    { derivative = productLinear construction
    ; remainder = productRemainder construction
    ; expansion = productExpansion construction
    ; remainderLittleO = productRemainderLittleO construction
    }

frechetProductDerivativeFormula :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  (B : BilinearProduct A W) →
  {f g : Vector V → Vector W} →
  {x : Vector V} →
  (F : FrechetDerivativeAt R f x) →
  (G : FrechetDerivativeAt R g x) →
  (construction : FrechetProductConstruction R B F G) →
  ∀ h →
  apply
    (derivative (frechetProduct B F G construction))
    h
  ≡ _+V_ W
      (product B (apply (derivative F) h) (g x))
      (product B (f x) (apply (derivative G) h))
frechetProductDerivativeFormula B F G construction =
  productLinearPointwise construction
