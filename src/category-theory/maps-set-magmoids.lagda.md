# Maps between set-magmoids

```agda
module category-theory.maps-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.set-magmoids

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.commuting-pentagons-of-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [set-magmoid](category-theory.set-magmoids.md) `C` to a
set-magmoid `D` consists of:

- a map `F₀ : C → D` on objects, and
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms.

## Definitions

### Maps between set-magmoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Set-Magmoid l1 l2)
  (D : Set-Magmoid l3 l4)
  where

  map-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Set-Magmoid =
    Σ ( obj-Set-Magmoid C → obj-Set-Magmoid D)
      ( λ F₀ →
        {x y : obj-Set-Magmoid C} →
        hom-Set-Magmoid C x y →
        hom-Set-Magmoid D (F₀ x) (F₀ y))

  obj-map-Set-Magmoid :
    (F : map-Set-Magmoid) → obj-Set-Magmoid C → obj-Set-Magmoid D
  obj-map-Set-Magmoid = pr1

  hom-map-Set-Magmoid :
    (F : map-Set-Magmoid) {x y : obj-Set-Magmoid C} →
    hom-Set-Magmoid C x y →
    hom-Set-Magmoid D (obj-map-Set-Magmoid F x) (obj-map-Set-Magmoid F y)
  hom-map-Set-Magmoid = pr2
```

### The identity map on a set-magmoid

```agda
module _
  {l1 l2 : Level} (A : Set-Magmoid l1 l2)
  where

  id-map-Set-Magmoid : map-Set-Magmoid A A
  pr1 id-map-Set-Magmoid = id
  pr2 id-map-Set-Magmoid = id
```

### Composition of maps on set-magmoids

Any two compatible maps can be composed to a new map.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Set-Magmoid l1 l2)
  (B : Set-Magmoid l3 l4)
  (C : Set-Magmoid l5 l6)
  (G : map-Set-Magmoid B C)
  (F : map-Set-Magmoid A B)
  where

  obj-comp-map-Set-Magmoid : obj-Set-Magmoid A → obj-Set-Magmoid C
  obj-comp-map-Set-Magmoid =
    obj-map-Set-Magmoid B C G ∘ obj-map-Set-Magmoid A B F

  hom-comp-map-Set-Magmoid :
    {x y : obj-Set-Magmoid A} →
    hom-Set-Magmoid A x y →
    hom-Set-Magmoid C (obj-comp-map-Set-Magmoid x) (obj-comp-map-Set-Magmoid y)
  hom-comp-map-Set-Magmoid =
    hom-map-Set-Magmoid B C G ∘ hom-map-Set-Magmoid A B F

  comp-map-Set-Magmoid : map-Set-Magmoid A C
  pr1 comp-map-Set-Magmoid = obj-comp-map-Set-Magmoid
  pr2 comp-map-Set-Magmoid = hom-comp-map-Set-Magmoid
```

## Properties

### Categorical laws for map composition

#### Unit laws for map composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : map-Set-Magmoid A B)
  where

  left-unit-law-comp-map-Set-Magmoid :
    comp-map-Set-Magmoid A B B (id-map-Set-Magmoid B) F ＝ F
  left-unit-law-comp-map-Set-Magmoid = refl

  right-unit-law-comp-map-Set-Magmoid :
    comp-map-Set-Magmoid A A B F (id-map-Set-Magmoid A) ＝ F
  right-unit-law-comp-map-Set-Magmoid = refl
```

#### Associativity of map composition

```agda
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Set-Magmoid l1 l1')
  (B : Set-Magmoid l2 l2')
  (C : Set-Magmoid l3 l3')
  (D : Set-Magmoid l4 l4')
  (F : map-Set-Magmoid A B)
  (G : map-Set-Magmoid B C)
  (H : map-Set-Magmoid C D)
  where

  associative-comp-map-Set-Magmoid :
    comp-map-Set-Magmoid A B D (comp-map-Set-Magmoid B C D H G) F ＝
    comp-map-Set-Magmoid A C D H (comp-map-Set-Magmoid A B C G F)
  associative-comp-map-Set-Magmoid = refl
```

#### The Mac Lane pentagon for map composition

The Mac Lane pentagon is a higher coherence of the associator for map
composition. Since map composition is strictly associative, the Mac Lane
pentagon also follows by reflexivity.

```text
    (I(GH))F ---- I((GH)F)
          /        \
         /          \
  ((IH)G)F          I(H(GF))
          \        /
            \    /
           (IH)(GF)
```

```agda
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Set-Magmoid l1 l1')
  (B : Set-Magmoid l2 l2')
  (C : Set-Magmoid l3 l3')
  (D : Set-Magmoid l4 l4')
  (E : Set-Magmoid l4 l4')
  (F : map-Set-Magmoid A B)
  (G : map-Set-Magmoid B C)
  (H : map-Set-Magmoid C D)
  (I : map-Set-Magmoid D E)
  where

  mac-lane-pentagon-comp-map-Set-Magmoid :
    coherence-pentagon-identifications
      { x =
        comp-map-Set-Magmoid A B E
        ( comp-map-Set-Magmoid B D E I
          ( comp-map-Set-Magmoid B C D H G))
        ( F)}
      { comp-map-Set-Magmoid A D E I
        ( comp-map-Set-Magmoid A B D
          ( comp-map-Set-Magmoid B C D H G)
          ( F))}
      { comp-map-Set-Magmoid A B E
        ( comp-map-Set-Magmoid B C E
          ( comp-map-Set-Magmoid C D E I H)
          ( G))
        ( F)}
      { comp-map-Set-Magmoid A D E
        ( I)
        ( comp-map-Set-Magmoid A C D
          ( H)
          ( comp-map-Set-Magmoid A B C G F))}
      { comp-map-Set-Magmoid A C E
        ( comp-map-Set-Magmoid C D E I H)
        ( comp-map-Set-Magmoid A B C G F)}
      ( associative-comp-map-Set-Magmoid A B D E
        ( F) (comp-map-Set-Magmoid B C D H G) (I))
      ( ap
        ( λ p → comp-map-Set-Magmoid A B E p F)
        ( inv (associative-comp-map-Set-Magmoid B C D E G H I)))
      ( ap
        ( λ p → comp-map-Set-Magmoid A D E I p)
        ( associative-comp-map-Set-Magmoid A B C D F G H))
      ( associative-comp-map-Set-Magmoid A B C E
        ( F) (G) (comp-map-Set-Magmoid C D E I H))
      ( inv
        ( associative-comp-map-Set-Magmoid A C D E
          (comp-map-Set-Magmoid A B C G F) H I))
  mac-lane-pentagon-comp-map-Set-Magmoid = refl
```

### Computing transport in the hom-family

```agda
module _
  {l1 l2 : Level} (C : Set-Magmoid l1 l2)
  {x x' y y' : obj-Set-Magmoid C}
  where

  compute-binary-tr-hom-Set-Magmoid :
    (p : x ＝ x') (q : y ＝ y') (f : hom-Set-Magmoid C x y) →
    left-whisker-hom-Set-Magmoid C
      ( q)
      ( right-whisker-hom-Set-Magmoid C f (inv p)) ＝
    ( binary-tr (hom-Set-Magmoid C) p q f)
  compute-binary-tr-hom-Set-Magmoid refl refl f = refl

  naturality-binary-tr-hom-Set-Magmoid :
    (p : x ＝ x') (q : y ＝ y')
    (f : hom-Set-Magmoid C x y) →
    right-whisker-hom-Set-Magmoid C
      ( binary-tr (hom-Set-Magmoid C) p q f) p ＝
    left-whisker-hom-Set-Magmoid C q f
  naturality-binary-tr-hom-Set-Magmoid refl refl f = refl

  naturality-binary-tr-hom-Set-Magmoid' :
    (p : x ＝ x') (q : y ＝ y')
    (f : hom-Set-Magmoid C x y) →
    left-whisker-hom-Set-Magmoid C q f ＝
    right-whisker-hom-Set-Magmoid C
      ( binary-tr (hom-Set-Magmoid C) p q f) p
  naturality-binary-tr-hom-Set-Magmoid' refl refl f = refl
```

### Characterization of equality of maps between set-magmoids

Equalities of maps between set-magmoids `f ＝ g` are characterized by a homotopy
of the underlying maps on objects `H : f₀ ~ g₀`, such that for every morphism
`a : hom(x, y)` in `C` we have a degenerate commuting square

```text
          Hx
    f₀x ====== g₀x
     |          |
 f₁a |          | g₁a
     ∨          ∨
    f₀y ====== g₀y.
          Hy
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Set-Magmoid l1 l2)
  (D : Set-Magmoid l3 l4)
  where

  coherence-htpy-map-Set-Magmoid :
    (f g : map-Set-Magmoid C D) →
    obj-map-Set-Magmoid C D f ~ obj-map-Set-Magmoid C D g →
    UU (l1 ⊔ l2 ⊔ l4)
  coherence-htpy-map-Set-Magmoid f g H =
    {x y : obj-Set-Magmoid C}
    (a : hom-Set-Magmoid C x y) →
    right-whisker-hom-Set-Magmoid D (hom-map-Set-Magmoid C D g a) (H x) ＝
    left-whisker-hom-Set-Magmoid D (H y) (hom-map-Set-Magmoid C D f a)

  htpy-map-Set-Magmoid :
    (f g : map-Set-Magmoid C D) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-map-Set-Magmoid f g =
    Σ ( obj-map-Set-Magmoid C D f ~ obj-map-Set-Magmoid C D g)
      ( coherence-htpy-map-Set-Magmoid f g)

  refl-htpy-map-Set-Magmoid :
    (f : map-Set-Magmoid C D) → htpy-map-Set-Magmoid f f
  pr1 (refl-htpy-map-Set-Magmoid f) = refl-htpy
  pr2 (refl-htpy-map-Set-Magmoid f) a =
    naturality-binary-tr-hom-Set-Magmoid D
      ( refl)
      ( refl)
      ( hom-map-Set-Magmoid C D f a)

  htpy-eq-map-Set-Magmoid :
    (f g : map-Set-Magmoid C D) → f ＝ g → htpy-map-Set-Magmoid f g
  htpy-eq-map-Set-Magmoid f .f refl = refl-htpy-map-Set-Magmoid f

  is-torsorial-htpy-map-Set-Magmoid :
    (f : map-Set-Magmoid C D) →
    is-torsorial (htpy-map-Set-Magmoid f)
  is-torsorial-htpy-map-Set-Magmoid f =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (obj-map-Set-Magmoid C D f))
      ( obj-map-Set-Magmoid C D f , refl-htpy)
      ( is-torsorial-Eq-implicit-Π
        ( λ x →
          is-torsorial-Eq-implicit-Π
            ( λ y → is-torsorial-htpy' (hom-map-Set-Magmoid C D f))))

  is-equiv-htpy-eq-map-Set-Magmoid :
    (f g : map-Set-Magmoid C D) → is-equiv (htpy-eq-map-Set-Magmoid f g)
  is-equiv-htpy-eq-map-Set-Magmoid f =
    fundamental-theorem-id
      ( is-torsorial-htpy-map-Set-Magmoid f)
      ( htpy-eq-map-Set-Magmoid f)

  equiv-htpy-eq-map-Set-Magmoid :
    (f g : map-Set-Magmoid C D) → (f ＝ g) ≃ htpy-map-Set-Magmoid f g
  pr1 (equiv-htpy-eq-map-Set-Magmoid f g) =
    htpy-eq-map-Set-Magmoid f g
  pr2 (equiv-htpy-eq-map-Set-Magmoid f g) =
    is-equiv-htpy-eq-map-Set-Magmoid f g

  eq-htpy-map-Set-Magmoid :
    (f g : map-Set-Magmoid C D) →
    htpy-map-Set-Magmoid f g → f ＝ g
  eq-htpy-map-Set-Magmoid f g =
    map-inv-equiv (equiv-htpy-eq-map-Set-Magmoid f g)
```

## See also

- [Functors between set-magmoids](category-theory.maps-set-magmoids.md)
- [The precategory of maps and natural transformations between precategories](category-theory.precategory-of-maps-precategories.md)

## External links

A wikidata identifier was not available for this concept.
