# Noncoherent retracts of maps

```agda
module foundation.noncoherent-retracts-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-prisms-of-maps
open import foundation.commuting-triangles-of-morphisms-arrows
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-action-on-identifications-functions
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies-morphisms-arrows
open import foundation.morphisms-arrows
open import foundation.path-algebra
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.retracts-of-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A map `f : A → B` is said to be a {{#concept "noncoherent retract"}} of a map
`g : X → Y` if there are [morphisms of arrows](foundation.morphisms-arrows.md)
`i : f → g` and `r : g → f` that fit into a commutative diagram

```text
         i₀        r₀
    A ------> X ------> A
    |         |         |
  f |    I    | g  R    | f
    ∨         ∨         ∨
    B ------> Y ------> B
         i₁        r₁
```

with coherences

```text
  I : i₁ ∘ f ~ g ∘ i₀  and   R : r₁ ∘ g ~ f ∘ r₀
```

witnessing that the left and right
[squares commute](foundation-core.commuting-squares-of-maps.md). A noncoherent
retract of maps is not a retract in the arrow category of types, as we do _not_
require a full homotopy of morphisms of arrows `r ∘ i ~ id`. I.e, the following
square need not be commutative

```text
                     R ·r i₀
       r₁ ∘ g ∘ i₀ ----------> f ∘ r₀ ∘ i₀
            |                      |
            |                      |
  r₁ ·l I⁻¹ |                      | f ·l H₀
            |                      |
            ∨                      ∨
      r₁ ∘ i₁ ∘ f ---------------> f.
                       H₁ ·r f
```

## Definition

### The predicate of being a noncoherent retraction of a morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g) (r : hom-arrow g f)
  where

  is-noncoherent-retraction-hom-arrow : UU (l1 ⊔ l2)
  is-noncoherent-retraction-hom-arrow =
    is-retraction (map-domain-hom-arrow f g i) (map-domain-hom-arrow g f r) ×
    is-retraction (map-codomain-hom-arrow f g i) (map-codomain-hom-arrow g f r)
```

### The type of noncoherent retractions of a morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g)
  where

  noncoherent-retraction-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  noncoherent-retraction-hom-arrow =
    Σ (hom-arrow g f) (is-noncoherent-retraction-hom-arrow f g i)

  module _
    (r : noncoherent-retraction-hom-arrow)
    where

    hom-noncoherent-retraction-hom-arrow : hom-arrow g f
    hom-noncoherent-retraction-hom-arrow = pr1 r

    is-noncoherent-retraction-hom-noncoherent-retraction-hom-arrow :
      is-noncoherent-retraction-hom-arrow f g i hom-noncoherent-retraction-hom-arrow
    is-noncoherent-retraction-hom-noncoherent-retraction-hom-arrow = pr2 r
```

### The predicate that a morphism `f` is a noncoherent retract of a morphism `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  noncoherent-retract-map : (g : X → Y) (f : A → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  noncoherent-retract-map g f =
    Σ (hom-arrow f g) (noncoherent-retraction-hom-arrow f g)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : noncoherent-retract-map g f)
  where

  inclusion-noncoherent-retract-map : hom-arrow f g
  inclusion-noncoherent-retract-map = pr1 R

  map-domain-inclusion-noncoherent-retract-map : A → X
  map-domain-inclusion-noncoherent-retract-map =
    map-domain-hom-arrow f g inclusion-noncoherent-retract-map

  map-codomain-inclusion-noncoherent-retract-map : B → Y
  map-codomain-inclusion-noncoherent-retract-map =
    map-codomain-hom-arrow f g inclusion-noncoherent-retract-map

  coh-inclusion-noncoherent-retract-map :
    coherence-square-maps
      ( map-domain-inclusion-noncoherent-retract-map)
      ( f)
      ( g)
      ( map-codomain-inclusion-noncoherent-retract-map)
  coh-inclusion-noncoherent-retract-map =
    coh-hom-arrow f g inclusion-noncoherent-retract-map

  retraction-noncoherent-retract-map :
    noncoherent-retraction-hom-arrow f g inclusion-noncoherent-retract-map
  retraction-noncoherent-retract-map = pr2 R

  hom-retraction-noncoherent-retract-map : hom-arrow g f
  hom-retraction-noncoherent-retract-map =
    hom-noncoherent-retraction-hom-arrow f g inclusion-noncoherent-retract-map retraction-noncoherent-retract-map

  map-domain-hom-retraction-noncoherent-retract-map : X → A
  map-domain-hom-retraction-noncoherent-retract-map =
    map-domain-hom-arrow g f hom-retraction-noncoherent-retract-map

  map-codomain-hom-retraction-noncoherent-retract-map : Y → B
  map-codomain-hom-retraction-noncoherent-retract-map =
    map-codomain-hom-arrow g f hom-retraction-noncoherent-retract-map

  coh-hom-retraction-noncoherent-retract-map :
    coherence-square-maps
      ( map-domain-hom-retraction-noncoherent-retract-map)
      ( g)
      ( f)
      ( map-codomain-hom-retraction-noncoherent-retract-map)
  coh-hom-retraction-noncoherent-retract-map =
    coh-hom-arrow g f hom-retraction-noncoherent-retract-map

  is-noncoherent-retraction-hom-retraction-noncoherent-retract-map :
    is-noncoherent-retraction-hom-arrow f g inclusion-noncoherent-retract-map hom-retraction-noncoherent-retract-map
  is-noncoherent-retraction-hom-retraction-noncoherent-retract-map =
    is-noncoherent-retraction-hom-noncoherent-retraction-hom-arrow f g
      ( inclusion-noncoherent-retract-map)
      ( retraction-noncoherent-retract-map)

  is-retraction-map-domain-hom-retraction-noncoherent-retract-map :
    is-retraction
      ( map-domain-inclusion-noncoherent-retract-map)
      ( map-domain-hom-retraction-noncoherent-retract-map)
  is-retraction-map-domain-hom-retraction-noncoherent-retract-map =
    pr1 is-noncoherent-retraction-hom-retraction-noncoherent-retract-map

  retraction-domain-noncoherent-retract-map :
    retraction map-domain-inclusion-noncoherent-retract-map
  pr1 retraction-domain-noncoherent-retract-map =
    map-domain-hom-retraction-noncoherent-retract-map
  pr2 retraction-domain-noncoherent-retract-map =
    is-retraction-map-domain-hom-retraction-noncoherent-retract-map

  retract-domain-noncoherent-retract-map : A retract-of X
  pr1 retract-domain-noncoherent-retract-map =
    map-domain-inclusion-noncoherent-retract-map
  pr2 retract-domain-noncoherent-retract-map =
    retraction-domain-noncoherent-retract-map

  is-retraction-map-codomain-hom-retraction-noncoherent-retract-map :
    is-retraction
      ( map-codomain-inclusion-noncoherent-retract-map)
      ( map-codomain-hom-retraction-noncoherent-retract-map)
  is-retraction-map-codomain-hom-retraction-noncoherent-retract-map =
    pr2 is-noncoherent-retraction-hom-retraction-noncoherent-retract-map

  retraction-codomain-noncoherent-retract-map :
    retraction map-codomain-inclusion-noncoherent-retract-map
  pr1 retraction-codomain-noncoherent-retract-map =
    map-codomain-hom-retraction-noncoherent-retract-map
  pr2 retraction-codomain-noncoherent-retract-map =
    is-retraction-map-codomain-hom-retraction-noncoherent-retract-map

  retract-codomain-noncoherent-retract-map : B retract-of Y
  pr1 retract-codomain-noncoherent-retract-map =
    map-codomain-inclusion-noncoherent-retract-map
  pr2 retract-codomain-noncoherent-retract-map =
    retraction-codomain-noncoherent-retract-map
```

## Properties

### Noncoherent retracts of maps with sections have sections

We only need the following data to show this:

```text
                 r₀
            X ------> A
            |         |
          g |    R    | f
            ∨         ∨
  B ------> Y ------> B.
       i₁   H₁   r₁
```

**Proof:** Note that `f` is the right map of a triangle

```text
            r₀
       X ------> A
        \       /
  r₁ ∘ g \     / f
          \   /
           ∨ ∨
            B.
```

Since both `r₁` and `g` are assumed to have
[sections](foundation-core.sections.md), it follows that the composite `r₁ ∘ g`
has a section, and therefore `f` has a section.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (r₀ : X → A) (R₁ : B retract-of Y)
  (r : coherence-square-maps r₀ g f (map-retraction-retract R₁))
  (s : section g)
  where

  section-noncoherent-retract-map-section' : section f
  section-noncoherent-retract-map-section' =
    section-right-map-triangle
      ( map-retraction-retract R₁ ∘ g)
      ( f)
      ( r₀)
      ( r)
      ( section-comp (map-retraction-retract R₁) g s (section-retract R₁))
```

### Noncoherent retracts of maps with retractions have retractions

We only need the following data to show this:

```text
         i₀   H   r₀
    A ------> X ------> A
    |         |
  f |    I    | g
    ∨         ∨
    B ------> Y.
         i₁
```

**Proof:** Note that `f` is the top map in the triangle

```text
            f
       A ------> B
        \       /
  g ∘ i₀ \     / i₁
          \   /
           ∨ ∨
            Y.
```

Since both `g` and `i₀` are assumed to have retractions, it follows that
`g ∘ i₀` has a retraction, and hence that `f` has a retraction.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : A retract-of X) (i₁ : B → Y)
  (i : coherence-square-maps (inclusion-retract R₀) f g i₁)
  (s : retraction g)
  where

  retraction-noncoherent-retract-map-retraction' : retraction f
  retraction-noncoherent-retract-map-retraction' =
    retraction-top-map-triangle
      ( g ∘ inclusion-retract R₀)
      ( i₁)
      ( f)
      ( inv-htpy i)
      ( retraction-comp g (inclusion-retract R₀) s (retraction-retract R₀))
```

### Equivalences are closed under noncoherent retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : noncoherent-retract-map g f)
  where

  is-equiv-noncoherent-retract-map-is-equiv : is-equiv g → is-equiv f
  pr1 (is-equiv-noncoherent-retract-map-is-equiv G) =
    section-noncoherent-retract-map-section' f g
      ( map-domain-hom-retraction-noncoherent-retract-map f g R)
      ( retract-codomain-noncoherent-retract-map f g R)
      ( coh-hom-retraction-noncoherent-retract-map f g R)
      ( section-is-equiv G)
  pr2 (is-equiv-noncoherent-retract-map-is-equiv G) =
    retraction-noncoherent-retract-map-retraction' f g
      ( retract-domain-noncoherent-retract-map f g R)
      ( map-codomain-inclusion-noncoherent-retract-map f g R)
      ( coh-inclusion-noncoherent-retract-map f g R)
      ( retraction-is-equiv G)
```

### If `f` is a noncoherent retract of `g`, then `- ∘ f` is a noncoherent retract of `- ∘ g`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : noncoherent-retract-map g f) (S : UU l5)
  where

  inclusion-precomp-noncoherent-retract-map :
    hom-arrow (precomp f S) (precomp g S)
  inclusion-precomp-noncoherent-retract-map =
    precomp-hom-arrow g f (hom-retraction-noncoherent-retract-map f g R) S

  hom-retraction-precomp-noncoherent-retract-map :
    hom-arrow (precomp g S) (precomp f S)
  hom-retraction-precomp-noncoherent-retract-map =
    precomp-hom-arrow f g (inclusion-noncoherent-retract-map f g R) S

  is-retraction-map-domain-precomp-noncoherent-retract-map :
    is-retraction
      ( map-domain-hom-arrow
        ( precomp f S)
        ( precomp g S)
        ( inclusion-precomp-noncoherent-retract-map))
      ( map-domain-hom-arrow
        ( precomp g S)
        ( precomp f S)
        ( hom-retraction-precomp-noncoherent-retract-map))
  is-retraction-map-domain-precomp-noncoherent-retract-map =
    htpy-precomp (is-retraction-map-codomain-hom-retraction-noncoherent-retract-map f g R) S

  is-retraction-map-codomain-precomp-noncoherent-retract-map :
    is-retraction
      ( map-codomain-hom-arrow
        ( precomp f S)
        ( precomp g S)
        ( inclusion-precomp-noncoherent-retract-map))
      ( map-codomain-hom-arrow
        ( precomp g S)
        ( precomp f S)
        ( hom-retraction-precomp-noncoherent-retract-map))
  is-retraction-map-codomain-precomp-noncoherent-retract-map =
    htpy-precomp (is-retraction-map-domain-hom-retraction-noncoherent-retract-map f g R) S

  is-noncoherent-retraction-hom-retraction-precomp-noncoherent-retract-map :
    is-noncoherent-retraction-hom-arrow
      ( precomp f S)
      ( precomp g S)
      ( inclusion-precomp-noncoherent-retract-map)
      ( hom-retraction-precomp-noncoherent-retract-map)
  pr1 is-noncoherent-retraction-hom-retraction-precomp-noncoherent-retract-map =
    is-retraction-map-domain-precomp-noncoherent-retract-map
  pr2 is-noncoherent-retraction-hom-retraction-precomp-noncoherent-retract-map =
    is-retraction-map-codomain-precomp-noncoherent-retract-map

  retraction-precomp-noncoherent-retract-map :
    noncoherent-retraction-hom-arrow
      ( precomp f S)
      ( precomp g S)
      ( inclusion-precomp-noncoherent-retract-map)
  pr1 retraction-precomp-noncoherent-retract-map =
    hom-retraction-precomp-noncoherent-retract-map
  pr2 retraction-precomp-noncoherent-retract-map =
    is-noncoherent-retraction-hom-retraction-precomp-noncoherent-retract-map

  noncoherent-retract-map-precomp-noncoherent-retract-map :
    noncoherent-retract-map (precomp g S) (precomp f S)
  pr1 noncoherent-retract-map-precomp-noncoherent-retract-map =
    inclusion-precomp-noncoherent-retract-map
  pr2 noncoherent-retract-map-precomp-noncoherent-retract-map =
    retraction-precomp-noncoherent-retract-map
```

### If `f` is a retract of `g`, then `f ∘ -` is a retract of `g ∘ -`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : noncoherent-retract-map g f) (S : UU l5)
  where

  inclusion-postcomp-noncoherent-retract-map :
    hom-arrow (postcomp S f) (postcomp S g)
  inclusion-postcomp-noncoherent-retract-map =
    postcomp-hom-arrow f g (inclusion-noncoherent-retract-map f g R) S

  hom-retraction-postcomp-noncoherent-retract-map :
    hom-arrow (postcomp S g) (postcomp S f)
  hom-retraction-postcomp-noncoherent-retract-map =
    postcomp-hom-arrow g f (hom-retraction-noncoherent-retract-map f g R) S

  is-retraction-map-domain-postcomp-noncoherent-retract-map :
    is-retraction
      ( map-domain-hom-arrow
        ( postcomp S f)
        ( postcomp S g)
        ( inclusion-postcomp-noncoherent-retract-map))
      ( map-domain-hom-arrow
        ( postcomp S g)
        ( postcomp S f)
        ( hom-retraction-postcomp-noncoherent-retract-map))
  is-retraction-map-domain-postcomp-noncoherent-retract-map =
    htpy-postcomp S (is-retraction-map-domain-hom-retraction-noncoherent-retract-map f g R)

  is-retraction-map-codomain-postcomp-noncoherent-retract-map :
    is-retraction
      ( map-codomain-hom-arrow
        ( postcomp S f)
        ( postcomp S g)
        ( inclusion-postcomp-noncoherent-retract-map))
      ( map-codomain-hom-arrow
        ( postcomp S g)
        ( postcomp S f)
        ( hom-retraction-postcomp-noncoherent-retract-map))
  is-retraction-map-codomain-postcomp-noncoherent-retract-map =
    htpy-postcomp S
      ( is-retraction-map-codomain-hom-retraction-noncoherent-retract-map f g R)

  is-noncoherent-retraction-hom-retraction-postcomp-noncoherent-retract-map :
    is-noncoherent-retraction-hom-arrow
      ( postcomp S f)
      ( postcomp S g)
      ( inclusion-postcomp-noncoherent-retract-map)
      ( hom-retraction-postcomp-noncoherent-retract-map)
  pr1
    is-noncoherent-retraction-hom-retraction-postcomp-noncoherent-retract-map =
    is-retraction-map-domain-postcomp-noncoherent-retract-map
  pr2
    is-noncoherent-retraction-hom-retraction-postcomp-noncoherent-retract-map =
    is-retraction-map-codomain-postcomp-noncoherent-retract-map

  retraction-postcomp-noncoherent-retract-map :
    noncoherent-retraction-hom-arrow
      ( postcomp S f)
      ( postcomp S g)
      ( inclusion-postcomp-noncoherent-retract-map)
  pr1 retraction-postcomp-noncoherent-retract-map =
    hom-retraction-postcomp-noncoherent-retract-map
  pr2 retraction-postcomp-noncoherent-retract-map =
    is-noncoherent-retraction-hom-retraction-postcomp-noncoherent-retract-map

  noncoherent-retract-map-postcomp-noncoherent-retract-map :
    noncoherent-retract-map (postcomp S g) (postcomp S f)
  pr1 noncoherent-retract-map-postcomp-noncoherent-retract-map =
    inclusion-postcomp-noncoherent-retract-map
  pr2 noncoherent-retract-map-postcomp-noncoherent-retract-map =
    retraction-postcomp-noncoherent-retract-map
```

### If `f` is a noncoherent retract of `g`, then `ap f` is a noncoherent retract of `ap g`

```text
               ap i₀                     ap r₀                                 ≃
    (x ＝ y) ---------> (i₀ x ＝ i₀ y) ---------> (r₀ (i₀ x) ＝ r₀ (i₀ y)) ---------> (x ＝ y)
       |                      |                              |                          |
  ap f |                 ap g |                         ap f |                     ap f |
       ∨                      ∨                              ∨                 ≃        ∨
  (f x ＝ f y) ---> (g (i₀ x) ＝ g (i₀ y)) -> (f (r₀ (i₀ x)) ＝ f (r₀ (i₀ y))) ---> (f x ＝ f y)
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : noncoherent-retract-map g f) {x y : A}
  where

  inclusion-ap-noncoherent-retract-map : hom-arrow (ap f {x} {y}) (ap g)
  inclusion-ap-noncoherent-retract-map =
    ap-hom-arrow f g (inclusion-noncoherent-retract-map f g R)

  hom-correction-retraction-ap-noncoherent-retract-map :
    hom-arrow (ap f) (ap f {x} {y})
  hom-correction-retraction-ap-noncoherent-retract-map =
    tr-ap-hom-arrow f
      ( inv
        ( is-retraction-map-domain-hom-retraction-noncoherent-retract-map
            f g R x))
      ( is-retraction-map-domain-hom-retraction-noncoherent-retract-map f g R y)

  hom-retraction-ap-noncoherent-retract-map :
    hom-arrow
      ( ap g
        { map-domain-inclusion-noncoherent-retract-map f g R x}
        { map-domain-inclusion-noncoherent-retract-map f g R y})
      ( ap f {x} {y})
  hom-retraction-ap-noncoherent-retract-map =
    comp-hom-arrow
      ( ap g)
      ( ap f)
      ( ap f)
      ( hom-correction-retraction-ap-noncoherent-retract-map)
      ( ap-hom-arrow g f (hom-retraction-noncoherent-retract-map f g R))

  is-retraction-map-domain-ap-noncoherent-retract-map :
    is-retraction
      ( map-domain-hom-arrow
        ( ap f)
        ( ap g)
        ( inclusion-ap-noncoherent-retract-map))
      ( map-domain-hom-arrow
        ( ap g)
        ( ap f)
        ( hom-retraction-ap-noncoherent-retract-map))
  is-retraction-map-domain-ap-noncoherent-retract-map refl =
    left-inv
      ( is-retraction-map-domain-hom-retraction-noncoherent-retract-map f g R x)

  is-retraction-map-codomain-ap-noncoherent-retract-map :
    is-retraction
      ( map-codomain-hom-arrow
        ( ap f)
        ( ap g)
        ( inclusion-ap-noncoherent-retract-map))
      ( map-codomain-hom-arrow
        ( ap g)
        ( ap f)
        ( hom-retraction-ap-noncoherent-retract-map))
  is-retraction-map-codomain-ap-noncoherent-retract-map p =
    equational-reasoning
    ( ap f
      ( inv
        ( is-retraction-map-domain-hom-retraction-noncoherent-retract-map f g R x))) ∙
    ( ( inv
        ( coh-hom-retraction-noncoherent-retract-map f g R
          ( map-domain-inclusion-noncoherent-retract-map f g R x))) ∙
      ( ( ap
          ( map-codomain-hom-retraction-noncoherent-retract-map f g R)
          ( ( inv (coh-inclusion-noncoherent-retract-map f g R x)) ∙
            ( ( ap (map-codomain-inclusion-noncoherent-retract-map f g R) p) ∙
              ( coh-inclusion-noncoherent-retract-map f g R y)))) ∙
        ( coh-hom-retraction-noncoherent-retract-map f g R
          ( map-domain-inclusion-noncoherent-retract-map f g R y))) ∙
      ( ap f
        ( is-retraction-map-domain-hom-retraction-noncoherent-retract-map f g R y)))
    ＝ {!   !}
      by {!   !}
    ＝ {!   !}
      by {!   !}
    ＝
      {! inv (pr2 (pr2 (pr2 R)) (f x)) ∙\n (ap (λ z → (map-codomain-hom-retraction-noncoherent-retract-map f g R ∘\n map-codomain-inclusion-noncoherent-retract-map f g R) \n z) \n p\n ∙ pr2 (pr2 (pr2 R)) (f y)) !}
      by {!   !}
    ＝ p
      by inv (left-transpose-eq-concat _ p _ (nat-htpy-id (is-retraction-map-codomain-hom-retraction-noncoherent-retract-map f g R) p))

  is-noncoherent-retraction-hom-retraction-ap-noncoherent-retract-map :
    is-noncoherent-retraction-hom-arrow
      ( ap f)
      ( ap g)
      ( inclusion-ap-noncoherent-retract-map)
      ( hom-retraction-ap-noncoherent-retract-map)
  pr1 is-noncoherent-retraction-hom-retraction-ap-noncoherent-retract-map =
    is-retraction-map-domain-ap-noncoherent-retract-map
  pr2 is-noncoherent-retraction-hom-retraction-ap-noncoherent-retract-map =
    is-retraction-map-codomain-ap-noncoherent-retract-map

  retraction-ap-noncoherent-retract-map :
    noncoherent-retraction-hom-arrow
      ( ap f)
      ( ap g)
      ( inclusion-ap-noncoherent-retract-map)
  pr1 retraction-ap-noncoherent-retract-map =
    hom-retraction-ap-noncoherent-retract-map
  pr2 retraction-ap-noncoherent-retract-map =
    is-noncoherent-retraction-hom-retraction-ap-noncoherent-retract-map

  noncoherent-retract-map-ap-noncoherent-retract-map :
    noncoherent-retract-map (ap g) (ap f)
  pr1 noncoherent-retract-map-ap-noncoherent-retract-map =
    inclusion-ap-noncoherent-retract-map
  pr2 noncoherent-retract-map-ap-noncoherent-retract-map =
    retraction-ap-noncoherent-retract-map
```

## References

{{#bibliography}} {{#reference UF13}}

## External links

- [Retracts in arrow categories](https://ncatlab.org/nlab/show/retract#in_arrow_categories)
  at $n$Lab

A wikidata identifier was not available for this concept.
