# The terminal category

```agda
module category-theory.terminal-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.functors-precategories
open import category-theory.gaunt-categories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories
open import category-theory.strict-categories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **terminal category** is the [category](category-theory.categories.md) with
one object and only the identity on that object. This category
[represents](category-theory.representable-functors-categories.md) objects.

## Definition

### The objects and hom-sets of the terminal category

```agda
obj-terminal-Category : UU lzero
obj-terminal-Category = unit

hom-set-terminal-Category :
  obj-terminal-Category → obj-terminal-Category → Set lzero
hom-set-terminal-Category _ _ = unit-Set

hom-terminal-Category :
  obj-terminal-Category → obj-terminal-Category → UU lzero
hom-terminal-Category x y = type-Set (hom-set-terminal-Category x y)
```

### The underlying precategory of the terminal category

```agda
comp-hom-terminal-Category :
  {x y z : obj-terminal-Category} →
  hom-terminal-Category y z →
  hom-terminal-Category x y →
  hom-terminal-Category x z
comp-hom-terminal-Category _ _ = star

associative-comp-hom-terminal-Category :
  {x y z w : obj-terminal-Category} →
  (h : hom-terminal-Category z w)
  (g : hom-terminal-Category y z)
  (f : hom-terminal-Category x y) →
  comp-hom-terminal-Category {x} (comp-hom-terminal-Category {y} h g) f ＝
  comp-hom-terminal-Category {x} h (comp-hom-terminal-Category {x} g f)
associative-comp-hom-terminal-Category h g f = refl

associative-composition-operation-terminal-Category :
  associative-composition-operation-binary-family-Set hom-set-terminal-Category
pr1 associative-composition-operation-terminal-Category =
  comp-hom-terminal-Category
pr2 associative-composition-operation-terminal-Category =
  associative-comp-hom-terminal-Category

id-hom-terminal-Category :
  {x : obj-terminal-Category} → hom-terminal-Category x x
id-hom-terminal-Category = star

left-unit-law-comp-hom-terminal-Category :
  {x y : obj-terminal-Category} →
  (f : hom-terminal-Category x y) →
  comp-hom-terminal-Category {x} (id-hom-terminal-Category {y}) f ＝ f
left-unit-law-comp-hom-terminal-Category f = refl

right-unit-law-comp-hom-terminal-Category :
  {x y : obj-terminal-Category} →
  (f : hom-terminal-Category x y) →
  comp-hom-terminal-Category {x} f (id-hom-terminal-Category {x}) ＝ f
right-unit-law-comp-hom-terminal-Category f = refl

is-unital-composition-operation-terminal-Category :
  is-unital-composition-operation-binary-family-Set
    ( hom-set-terminal-Category)
    ( λ {x} {y} {z} → comp-hom-terminal-Category {x} {y} {z})
pr1 is-unital-composition-operation-terminal-Category _ =
  id-hom-terminal-Category
pr1 (pr2 is-unital-composition-operation-terminal-Category) =
  left-unit-law-comp-hom-terminal-Category
pr2 (pr2 is-unital-composition-operation-terminal-Category) =
  right-unit-law-comp-hom-terminal-Category

terminal-Precategory : Precategory lzero lzero
pr1 terminal-Precategory = obj-terminal-Category
pr1 (pr2 terminal-Precategory) = hom-set-terminal-Category
pr1 (pr2 (pr2 terminal-Precategory)) =
  associative-composition-operation-terminal-Category
pr2 (pr2 (pr2 terminal-Precategory)) =
  is-unital-composition-operation-terminal-Category
```

### The terminal category

```agda
is-category-terminal-Category :
  is-category-Precategory terminal-Precategory
is-category-terminal-Category x y =
  is-equiv-is-contr
    ( iso-eq-Precategory terminal-Precategory x y)
    ( is-prop-is-contr is-contr-unit x y)
    ( is-contr-Σ is-contr-unit star
      ( is-proof-irrelevant-is-prop
        ( is-prop-is-iso-Precategory terminal-Precategory star)
        ( star , refl , refl)))

terminal-Category : Category lzero lzero
pr1 terminal-Category = terminal-Precategory
pr2 terminal-Category = is-category-terminal-Category
```

### The terminal preunivalent category

```agda
is-preunivalent-terminal-Category :
  is-preunivalent-Precategory terminal-Precategory
is-preunivalent-terminal-Category =
  is-preunivalent-category-Category terminal-Category

terminal-Preunivalent-Category : Preunivalent-Category lzero lzero
terminal-Preunivalent-Category =
  preunivalent-category-Category terminal-Category
```

### The terminal strict category

```agda
is-strict-category-terminal-Category :
  is-strict-category-Precategory terminal-Precategory
is-strict-category-terminal-Category = is-set-unit

terminal-Strict-Category : Strict-Category lzero lzero
pr1 terminal-Strict-Category = terminal-Precategory
pr2 terminal-Strict-Category = is-strict-category-terminal-Category
```

### The terminal gaunt category

```agda
is-gaunt-terminal-Category : is-gaunt-Category terminal-Category
is-gaunt-terminal-Category _ _ =
  is-prop-Σ is-prop-unit (λ _ → is-prop-is-iso-Category terminal-Category star)

terminal-Gaunt-Category : Gaunt-Category lzero lzero
pr1 terminal-Gaunt-Category = terminal-Category
pr2 terminal-Gaunt-Category = is-gaunt-terminal-Category
```

### Points in a precategory

Using the terminal category as the representing category of objects, we can
define, given an object in a category `x ∈ C`, the _point_ at `x` as the
constant functor from the terminal category to `C` at `x`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (x : obj-Precategory C)
  where

  point-Precategory : functor-Precategory terminal-Precategory C
  pr1 point-Precategory _ = x
  pr1 (pr2 point-Precategory) _ = id-hom-Precategory C
  pr1 (pr2 (pr2 point-Precategory)) _ _ =
    inv (left-unit-law-comp-hom-Precategory C (id-hom-Precategory C))
  pr2 (pr2 (pr2 point-Precategory)) _ = refl
```

## Properties

### The terminal category represents objects

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-equiv-point-Precategory : is-equiv (point-Precategory C)
  is-equiv-point-Precategory =
    is-equiv-is-invertible
      ( λ F → obj-functor-Precategory terminal-Precategory C F star)
      ( λ F →
        eq-htpy-functor-Precategory terminal-Precategory C _ F
          ( refl-htpy ,
            ( λ _ →
              ap
                ( λ f → comp-hom-Precategory C f (id-hom-Precategory C))
                ( preserves-id-functor-Precategory terminal-Precategory C F
                  ( star)))))
      ( refl-htpy)

  equiv-point-Precategory :
    obj-Precategory C ≃ functor-Precategory terminal-Precategory C
  pr1 equiv-point-Precategory = point-Precategory C
  pr2 equiv-point-Precategory = is-equiv-point-Precategory

  inv-equiv-point-Precategory :
    functor-Precategory terminal-Precategory C ≃ obj-Precategory C
  inv-equiv-point-Precategory = inv-equiv equiv-point-Precategory
```

It remains to show functoriality of `point-Precategory`.

### The terminal category is terminal

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  terminal-functor-Precategory : functor-Precategory C terminal-Precategory
  pr1 terminal-functor-Precategory _ = star
  pr1 (pr2 terminal-functor-Precategory) _ = star
  pr1 (pr2 (pr2 terminal-functor-Precategory)) _ _ = refl
  pr2 (pr2 (pr2 terminal-functor-Precategory)) _ = refl

  uniqueness-terminal-functor-Precategory :
    (F : functor-Precategory C terminal-Precategory) →
    terminal-functor-Precategory ＝ F
  uniqueness-terminal-functor-Precategory F =
    eq-htpy-functor-Precategory
      ( C)
      ( terminal-Precategory)
      ( terminal-functor-Precategory)
      ( F)
      ((λ _ → refl) , (λ _ → refl))

  is-contr-functor-terminal-Precategory :
    is-contr (functor-Precategory C terminal-Precategory)
  pr1 is-contr-functor-terminal-Precategory =
    terminal-functor-Precategory
  pr2 is-contr-functor-terminal-Precategory =
    uniqueness-terminal-functor-Precategory
```

## See also

- [The initial category](category-theory.initial-category.md)

## External links

- [Terminal category](https://1lab.dev/Cat.Instances.Shape.Terminal.html) at
  1lab
- [Terminal category](https://ncatlab.org/nlab/show/terminal+category) at $n$Lab

A wikidata identifier was not available for this concept.
