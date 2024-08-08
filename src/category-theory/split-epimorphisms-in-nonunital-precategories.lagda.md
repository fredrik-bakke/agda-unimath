# Split epimorphisms in nonunital precategories

```agda
module category-theory.split-epimorphisms-in-nonunital-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.nonunital-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "split epimorphism" Disambiguation="in a nonunital precategory" Agda=split-epi-Nonunital-Precategory}}
in a [nonunital precategory](category-theory.nonunital-precategory.md) `𝒞` is a
morphism `f : x → y` in `𝒞` such that there is a family of left inverse maps to
precomposition

```text
  g z : hom(x, z) → hom(y, z)
```

such that

```text
  g z ∘ hom(f, z) ~ id
```

and a family of right inverse maps to postcomposition

```text
  h z : hom(z, y) → hom(z, x)
```

such that

```text
  hom(z, f) ∘ h z ~ id
```

for all objects `z` in `𝒞`.

Note that unlike the predicate of being a split epimorphism in a unital
[precategory](category-theory.precategories.md), the
[proposition](foundation-core.propositions.md) considered here is large with
respect to the collection of objects.

## Definitions

### The predicate of being a split epimorphism in a nonunital precategory

```agda
module _
  {l1 l2 : Level}
  (𝒞 : Nonunital-Precategory l1 l2)
  {x y : obj-Nonunital-Precategory 𝒞}
  (f : hom-Nonunital-Precategory 𝒞 x y)
  where

  is-split-epi-Nonunital-Precategory : UU (l1 ⊔ l2)
  is-split-epi-Nonunital-Precategory =
    ( (z : obj-Nonunital-Precategory 𝒞) →
      retraction (precomp-hom-Nonunital-Precategory 𝒞 f z)) ×
    ( (z : obj-Nonunital-Precategory 𝒞) →
      section (postcomp-hom-Nonunital-Precategory 𝒞 f z))

  is-set-is-split-epi-Nonunital-Precategory :
    is-set is-split-epi-Nonunital-Precategory
  is-set-is-split-epi-Nonunital-Precategory =
    is-set-product
      ( is-set-Π
        ( λ z →
          is-set-Σ
            ( is-set-function-type (is-set-hom-Nonunital-Precategory 𝒞 y z))
            ( λ g →
              is-set-is-prop
                ( is-prop-Π
                  ( λ h →
                    is-set-hom-Nonunital-Precategory 𝒞 y z
                      ( g (comp-hom-Nonunital-Precategory 𝒞 h f))
                      ( h))))))
      ( is-set-Π
        ( λ z →
          is-set-Σ
            ( is-set-function-type (is-set-hom-Nonunital-Precategory 𝒞 z x))
            ( λ g →
              is-set-is-prop
                ( is-prop-Π
                  ( λ h →
                    is-set-hom-Nonunital-Precategory 𝒞 z y
                      ( comp-hom-Nonunital-Precategory 𝒞 f (g h))
                      ( h))))))
```

We observe that the previous argument generalizes to conclude that if the
hom-types are 𝑛-truncated, then the type of splittings is too.

```agda
module _
  {l1 l2 : Level}
  (𝒞 : Nonunital-Precategory l1 l2)
  {x y : obj-Nonunital-Precategory 𝒞}
  {f : hom-Nonunital-Precategory 𝒞 x y}
  (H : is-split-epi-Nonunital-Precategory 𝒞 f)
  where

  retraction-precomp-is-split-epi-Nonunital-Precategory :
    (z : obj-Nonunital-Precategory 𝒞) →
    retraction (precomp-hom-Nonunital-Precategory 𝒞 f z)
  retraction-precomp-is-split-epi-Nonunital-Precategory = pr1 H

  map-retraction-precomp-is-split-epi-Nonunital-Precategory :
    (z : obj-Nonunital-Precategory 𝒞) →
    hom-Nonunital-Precategory 𝒞 x z → hom-Nonunital-Precategory 𝒞 y z
  map-retraction-precomp-is-split-epi-Nonunital-Precategory z =
    map-retraction
      ( precomp-hom-Nonunital-Precategory 𝒞 f z)
      ( retraction-precomp-is-split-epi-Nonunital-Precategory z)

  section-postcomp-is-split-epi-Nonunital-Precategory :
    (z : obj-Nonunital-Precategory 𝒞) →
    section (postcomp-hom-Nonunital-Precategory 𝒞 f z)
  section-postcomp-is-split-epi-Nonunital-Precategory = pr2 H

  map-section-postcomp-is-split-epi-Nonunital-Precategory :
    (z : obj-Nonunital-Precategory 𝒞) →
    hom-Nonunital-Precategory 𝒞 z y → hom-Nonunital-Precategory 𝒞 z x
  map-section-postcomp-is-split-epi-Nonunital-Precategory z =
    map-section
      ( postcomp-hom-Nonunital-Precategory 𝒞 f z)
      ( section-postcomp-is-split-epi-Nonunital-Precategory z)
```

### The set of split epimorphisms between two objects in a nonunital precategory

```agda
module _
  {l1 l2 : Level}
  (𝒞 : Nonunital-Precategory l1 l2)
  (x y : obj-Nonunital-Precategory 𝒞)
  where

  split-epi-Nonunital-Precategory : UU (l1 ⊔ l2)
  split-epi-Nonunital-Precategory =
    Σ (hom-Nonunital-Precategory 𝒞 x y) (is-split-epi-Nonunital-Precategory 𝒞)

  is-set-split-epi-Nonunital-Precategory :
    is-set split-epi-Nonunital-Precategory
  is-set-split-epi-Nonunital-Precategory =
    is-set-Σ
      ( is-set-hom-Nonunital-Precategory 𝒞 x y)
      ( is-set-is-split-epi-Nonunital-Precategory 𝒞)

  split-epi-set-Nonunital-Precategory : Set (l1 ⊔ l2)
  split-epi-set-Nonunital-Precategory =
    ( split-epi-Nonunital-Precategory ,
      is-set-split-epi-Nonunital-Precategory)

module _
  {l1 l2 : Level}
  (𝒞 : Nonunital-Precategory l1 l2)
  {x y : obj-Nonunital-Precategory 𝒞}
  (f : split-epi-Nonunital-Precategory 𝒞 x y)
  where

  hom-split-epi-Nonunital-Precategory : hom-Nonunital-Precategory 𝒞 x y
  hom-split-epi-Nonunital-Precategory = pr1 f

  is-split-epi-split-epi-Nonunital-Precategory :
    is-split-epi-Nonunital-Precategory 𝒞 hom-split-epi-Nonunital-Precategory
  is-split-epi-split-epi-Nonunital-Precategory = pr2 f
```

## Properties

### Composition of split epimorphisms

```agda
module _
  {l1 l2 : Level}
  (𝒞 : Nonunital-Precategory l1 l2)
  {x y z : obj-Nonunital-Precategory 𝒞}
  (g : hom-Nonunital-Precategory 𝒞 y z)
  (f : hom-Nonunital-Precategory 𝒞 x y)
  (G : is-split-epi-Nonunital-Precategory 𝒞 g)
  (F : is-split-epi-Nonunital-Precategory 𝒞 f)
  where

  is-split-epi-comp-hom-Nonunital-Precategory :
    is-split-epi-Nonunital-Precategory 𝒞 (comp-hom-Nonunital-Precategory 𝒞 g f)
  pr1 is-split-epi-comp-hom-Nonunital-Precategory z =
    retraction-left-map-triangle'
      ( precomp-hom-Nonunital-Precategory 𝒞
        ( comp-hom-Nonunital-Precategory 𝒞 g f)
        ( z))
      ( precomp-hom-Nonunital-Precategory 𝒞 f z)
      ( precomp-hom-Nonunital-Precategory 𝒞 g z)
      ( λ h → associative-comp-hom-Nonunital-Precategory 𝒞 h g f)
      ( retraction-precomp-is-split-epi-Nonunital-Precategory 𝒞 F z)
      ( retraction-precomp-is-split-epi-Nonunital-Precategory 𝒞 G z)
  pr2 is-split-epi-comp-hom-Nonunital-Precategory z =
    section-left-map-triangle
      ( postcomp-hom-Nonunital-Precategory 𝒞
        ( comp-hom-Nonunital-Precategory 𝒞 g f)
        ( z))
      ( postcomp-hom-Nonunital-Precategory 𝒞 g z)
      ( postcomp-hom-Nonunital-Precategory 𝒞 f z)
      ( associative-comp-hom-Nonunital-Precategory 𝒞 g f)
      ( section-postcomp-is-split-epi-Nonunital-Precategory 𝒞 F z)
      ( section-postcomp-is-split-epi-Nonunital-Precategory 𝒞 G z)

module _
  {l1 l2 : Level}
  (𝒞 : Nonunital-Precategory l1 l2)
  {x y z : obj-Nonunital-Precategory 𝒞}
  (g : split-epi-Nonunital-Precategory 𝒞 y z)
  (f : split-epi-Nonunital-Precategory 𝒞 x y)
  where

  comp-split-epi-Nonunital-Precategory :
    split-epi-Nonunital-Precategory 𝒞 x z
  comp-split-epi-Nonunital-Precategory =
    ( comp-hom-Nonunital-Precategory 𝒞
      ( hom-split-epi-Nonunital-Precategory 𝒞 g)
      ( hom-split-epi-Nonunital-Precategory 𝒞 f)) ,
    ( is-split-epi-comp-hom-Nonunital-Precategory 𝒞
      ( hom-split-epi-Nonunital-Precategory 𝒞 g)
      ( hom-split-epi-Nonunital-Precategory 𝒞 f)
      ( is-split-epi-split-epi-Nonunital-Precategory 𝒞 g)
      ( is-split-epi-split-epi-Nonunital-Precategory 𝒞 f))
```

### Right cancellation of split epimorphisms

```agda
module _
  {l1 l2 : Level}
  (𝒞 : Nonunital-Precategory l1 l2)
  {x y z : obj-Nonunital-Precategory 𝒞}
  (g : hom-Nonunital-Precategory 𝒞 y z)
  (f : hom-Nonunital-Precategory 𝒞 x y)
  (GF :
    is-split-epi-Nonunital-Precategory 𝒞 (comp-hom-Nonunital-Precategory 𝒞 g f))
  where

  is-split-epi-left-factor-Nonunital-Precategory :
    is-split-epi-Nonunital-Precategory 𝒞 g
  pr1 is-split-epi-left-factor-Nonunital-Precategory z =
    retraction-top-map-triangle'
      ( precomp-hom-Nonunital-Precategory 𝒞
        ( comp-hom-Nonunital-Precategory 𝒞 g f)
        ( z))
      ( precomp-hom-Nonunital-Precategory 𝒞 f z)
      ( precomp-hom-Nonunital-Precategory 𝒞 g z)
      ( λ h → associative-comp-hom-Nonunital-Precategory 𝒞 h g f)
      ( retraction-precomp-is-split-epi-Nonunital-Precategory 𝒞 GF z)
  pr2 is-split-epi-left-factor-Nonunital-Precategory z =
    section-right-map-triangle
      ( postcomp-hom-Nonunital-Precategory 𝒞
        ( comp-hom-Nonunital-Precategory 𝒞 g f)
        ( z))
      ( postcomp-hom-Nonunital-Precategory 𝒞 g z)
      ( postcomp-hom-Nonunital-Precategory 𝒞 f z)
      ( associative-comp-hom-Nonunital-Precategory 𝒞 g f)
      ( section-postcomp-is-split-epi-Nonunital-Precategory 𝒞 GF z)
```
