# Representable functors between precategories

```agda
module category-theory.representable-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.copresheaf-categories
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import foundation.equality-dependent-pair-types
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories

open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.propositions
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C` and an object `c`,
there is a [functor](category-theory.functors-precategories.md) from `C` to the
[precategory of sets](foundation.category-of-sets.md) **represented** by `c`
that:

- sends an object `x` of `C` to the [set](foundation-core.sets.md) `hom c x` and
- sends a morphism `f : hom x y` of `C` to the function `hom c x → hom c y`
  defined by postcomposition with `f`.

The functoriality axioms follow from associativity and the left unit law for the
precategory `C` using the
[function extensionality axiom](foundation.function-extensionality.md).

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (c : obj-Precategory C)
  where

  obj-representable-functor-Precategory : obj-Precategory C → Set l2
  obj-representable-functor-Precategory = hom-set-Precategory C c

  hom-representable-functor-Precategory :
    {x y : obj-Precategory C} (f : hom-Precategory C x y) →
    hom-Precategory C c x → hom-Precategory C c y
  hom-representable-functor-Precategory f = postcomp-hom-Precategory C f c

  representable-map-Precategory : map-Precategory C (Set-Precategory l2)
  pr1 representable-map-Precategory = obj-representable-functor-Precategory
  pr2 representable-map-Precategory = hom-representable-functor-Precategory

  preserves-comp-representable-functor-Precategory :
    preserves-comp-hom-map-Precategory
      ( C)
      ( Set-Precategory l2)
      ( representable-map-Precategory)
  preserves-comp-representable-functor-Precategory g f =
    eq-htpy (associative-comp-hom-Precategory C g f)

  preserves-id-representable-functor-Precategory :
    preserves-id-hom-map-Precategory
      ( C)
      ( Set-Precategory l2)
      ( representable-map-Precategory)
  preserves-id-representable-functor-Precategory x =
    eq-htpy (left-unit-law-comp-hom-Precategory C)

  representable-functor-Precategory : functor-Precategory C (Set-Precategory l2)
  pr1 representable-functor-Precategory =
    obj-representable-functor-Precategory
  pr1 (pr2 representable-functor-Precategory) =
    hom-representable-functor-Precategory
  pr1 (pr2 (pr2 representable-functor-Precategory)) =
    preserves-comp-representable-functor-Precategory
  pr2 (pr2 (pr2 representable-functor-Precategory)) =
    preserves-id-representable-functor-Precategory
```

## Natural transformations between representable functors

A morphism `f : hom b c` in a precategory `C` defines a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
from the functor represented by `c` to the functor represented by `b`. Its
components `hom c x → hom b x` are defined by precomposition with `f`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {b c : obj-Precategory C} (f : hom-Precategory C b c)
  where

  hom-family-representable-natural-transformation-Precategory :
    hom-family-functor-Precategory
      ( C)
      ( Set-Precategory l2)
      ( representable-functor-Precategory C c)
      ( representable-functor-Precategory C b)
  hom-family-representable-natural-transformation-Precategory =
    precomp-hom-Precategory C f

  is-natural-transformation-representable-natural-transformation-Precategory :
    is-natural-transformation-Precategory
      ( C)
      ( Set-Precategory l2)
      ( representable-functor-Precategory C c)
      ( representable-functor-Precategory C b)
      ( hom-family-representable-natural-transformation-Precategory)
  is-natural-transformation-representable-natural-transformation-Precategory h =
    eq-htpy (inv-htpy (λ g → associative-comp-hom-Precategory C h g f))

  representable-natural-transformation-Precategory :
    natural-transformation-Precategory
      ( C)
      ( Set-Precategory l2)
      ( representable-functor-Precategory C c)
      ( representable-functor-Precategory C b)
  pr1 (representable-natural-transformation-Precategory) =
    hom-family-representable-natural-transformation-Precategory
  pr2 (representable-natural-transformation-Precategory) =
    is-natural-transformation-representable-natural-transformation-Precategory
```

## Properties

### Taking representable functors defines a functor into the copresheaf category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  map-representable-functor-copresheaf-Precategory :
    map-Precategory
      ( opposite-Precategory C)
      ( copresheaf-precategory-Precategory C l2)
  pr1 map-representable-functor-copresheaf-Precategory =
    representable-functor-Precategory C
  pr2 map-representable-functor-copresheaf-Precategory =
    representable-natural-transformation-Precategory C

  preserves-comp-map-representable-functor-copresheaf-Precategory :
    preserves-comp-hom-map-Precategory
      ( opposite-Precategory C)
      ( copresheaf-precategory-Precategory C l2)
      ( map-representable-functor-copresheaf-Precategory)
  preserves-comp-map-representable-functor-copresheaf-Precategory
    { x} {y} {z} f g =
    eq-type-subtype
      ( is-natural-transformation-prop-Precategory
        ( C)
        ( Set-Precategory l2)
        ( representable-functor-Precategory C x)
        ( representable-functor-Precategory C z))
      ( eq-htpy
        ( λ _ → eq-htpy (λ h → inv (associative-comp-hom-Precategory C h g f))))

  preserves-id-map-representable-functor-copresheaf-Precategory :
    preserves-id-hom-map-Precategory
      ( opposite-Precategory C)
      ( copresheaf-precategory-Precategory C l2)
      ( map-representable-functor-copresheaf-Precategory)
  preserves-id-map-representable-functor-copresheaf-Precategory x =
    eq-type-subtype
     ( is-natural-transformation-prop-Precategory
        ( C)
        ( Set-Precategory l2)
        ( representable-functor-Precategory C x)
        ( representable-functor-Precategory C x))
      ( eq-htpy (λ _ → eq-htpy (right-unit-law-comp-hom-Precategory C)))

  is-functor-emb-yoneda-copresheaf-Precategory :
    is-functor-map-Precategory
      ( opposite-Precategory C)
      ( copresheaf-precategory-Precategory C l2)
      ( map-representable-functor-copresheaf-Precategory)
  is-functor-emb-yoneda-copresheaf-Precategory =
    ( preserves-comp-map-representable-functor-copresheaf-Precategory ,
      preserves-id-map-representable-functor-copresheaf-Precategory)

  functor-emb-yoneda-copresheaf-Precategory :
    functor-Precategory
      ( opposite-Precategory C)
      ( copresheaf-precategory-Precategory C l2)
  functor-emb-yoneda-copresheaf-Precategory =
    ( representable-functor-Precategory C ,
      representable-natural-transformation-Precategory C ,
      is-functor-emb-yoneda-copresheaf-Precategory)
```
