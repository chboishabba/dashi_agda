# Square versus Apollonian Packing Comparison

`DASHI.Biology.SquareApollonianPackingComparison` makes the competing hall-of-halls reconstructions mathematically distinguishable.

## Signature comparison

The square packing carries:

```text
global translation periodicity = true
orthogonal axes                = true
local tangency law             = false
curved triangular gaps         = false
equal first-generation radii   = true
```

The Apollonian sphere family carries:

```text
global translation periodicity = false
orthogonal axes                = false
local tangency law             = true
curved triangular gaps         = true
branching gap genealogy        = true
```

The square-seeded Apollonian hybrid carries both global square order and local tangency order. This formalises the possibility that the remembered large-scale room was periodic while the smaller residual perforations were curved, branching, and tangency-driven.

The square and Apollonian signature records are proved unequal.

## Exact Descartes identity

The signed circle-curvature example is:

```text
(-1, 2, 2, 3)
```

The module proves by normalization:

```text
(-1 + 2 + 2 + 3)^2
= 2 (1^2 + 2^2 + 2^2 + 3^2)
= 36.
```

In the constructive Nat representation, the negative enclosing curvature is separated before subtraction.

## Exact Soddy–Gosset identity

The signed sphere-curvature example is:

```text
(-4, 8, 8, 12, 12)
```

The module proves:

```text
(-4 + 8 + 8 + 12 + 12)^2
= 3 (4^2 + 8^2 + 8^2 + 12^2 + 12^2)
= 1296.
```

This is an exact finite witness of the three-dimensional Soddy–Gosset relation.

## Gap geometry

The comparison consumes the recursive-perforation module and proves:

```text
square grid seed   -> curved-square/four-arc gap
tangent triple     -> curved-triangular/three-arc gap
```

It also carries the theorem that tangency regularity can be present while global periodicity is absent.

## Boundary

The exact curvature identities do not establish that the remembered vision was uniquely Apollonian. The implementation explicitly preserves:

```text
exact curvature identity
!= recovered historical scene
```

and permits square order at one scale together with Apollonian order at another.
