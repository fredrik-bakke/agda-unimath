# Large nonunital precategories

```agda
module category-theory.large-nonunital-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.nonunital-precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large nonunital precategory" Agda=Large-Nonunital-Precategory}} is
a [nonunital precategory](category-theory.nonunital-precategories.md) where we
don't fix a universe for the type of objects or morphisms. (This cannot be done
with Σ-types, we must use a record type.)

## Definition

### The large type of large nonunital precategories

```agda
record
  Large-Nonunital-Precategory (α : Level → Level) (β : Level → Level → Level) : UUω where

  field
    obj-Large-Nonunital-Precategory :
      (l : Level) → UU (α l)

    hom-set-Large-Nonunital-Precategory :
      {l1 l2 : Level} →
      obj-Large-Nonunital-Precategory l1 →
      obj-Large-Nonunital-Precategory l2 →
      Set (β l1 l2)

  hom-Large-Nonunital-Precategory :
    {l1 l2 : Level} →
    obj-Large-Nonunital-Precategory l1 →
    obj-Large-Nonunital-Precategory l2 →
    UU (β l1 l2)
  hom-Large-Nonunital-Precategory X Y =
    type-Set (hom-set-Large-Nonunital-Precategory X Y)

  is-set-hom-Large-Nonunital-Precategory :
    {l1 l2 : Level}
    (X : obj-Large-Nonunital-Precategory l1)
    (Y : obj-Large-Nonunital-Precategory l2) →
    is-set (hom-Large-Nonunital-Precategory X Y)
  is-set-hom-Large-Nonunital-Precategory X Y =
    is-set-type-Set (hom-set-Large-Nonunital-Precategory X Y)

  field
    comp-hom-Large-Nonunital-Precategory :
      {l1 l2 l3 : Level}
      {X : obj-Large-Nonunital-Precategory l1}
      {Y : obj-Large-Nonunital-Precategory l2}
      {Z : obj-Large-Nonunital-Precategory l3} →
      hom-Large-Nonunital-Precategory Y Z →
      hom-Large-Nonunital-Precategory X Y →
      hom-Large-Nonunital-Precategory X Z

    involutive-eq-associative-comp-hom-Large-Nonunital-Precategory :
      {l1 l2 l3 l4 : Level}
      {X : obj-Large-Nonunital-Precategory l1}
      {Y : obj-Large-Nonunital-Precategory l2}
      {Z : obj-Large-Nonunital-Precategory l3}
      {W : obj-Large-Nonunital-Precategory l4} →
      (h : hom-Large-Nonunital-Precategory Z W)
      (g : hom-Large-Nonunital-Precategory Y Z)
      (f : hom-Large-Nonunital-Precategory X Y) →
      ( comp-hom-Large-Nonunital-Precategory (comp-hom-Large-Nonunital-Precategory h g) f) ＝ⁱ
      ( comp-hom-Large-Nonunital-Precategory h (comp-hom-Large-Nonunital-Precategory g f))

  associative-comp-hom-Large-Nonunital-Precategory :
      {l1 l2 l3 l4 : Level}
      {X : obj-Large-Nonunital-Precategory l1}
      {Y : obj-Large-Nonunital-Precategory l2}
      {Z : obj-Large-Nonunital-Precategory l3}
      {W : obj-Large-Nonunital-Precategory l4} →
      (h : hom-Large-Nonunital-Precategory Z W)
      (g : hom-Large-Nonunital-Precategory Y Z)
      (f : hom-Large-Nonunital-Precategory X Y) →
      ( comp-hom-Large-Nonunital-Precategory (comp-hom-Large-Nonunital-Precategory h g) f) ＝
      ( comp-hom-Large-Nonunital-Precategory h (comp-hom-Large-Nonunital-Precategory g f))
  associative-comp-hom-Large-Nonunital-Precategory h g f =
    eq-involutive-eq
      ( involutive-eq-associative-comp-hom-Large-Nonunital-Precategory h g f)

open Large-Nonunital-Precategory public

make-Large-Nonunital-Precategory :
  {α : Level → Level} {β : Level → Level → Level}
  ( obj : (l : Level) → UU (α l))
  ( hom-set : {l1 l2 : Level} → obj l1 → obj l2 → Set (β l1 l2))
  ( _∘_ :
    {l1 l2 l3 : Level}
    {X : obj l1} {Y : obj l2} {Z : obj l3} →
    type-Set (hom-set Y Z) → type-Set (hom-set X Y) → type-Set (hom-set X Z))
  ( assoc-comp-hom :
    {l1 l2 l3 l4 : Level}
    {X : obj l1} {Y : obj l2} {Z : obj l3} {W : obj l4}
    (h : type-Set (hom-set Z W))
    (g : type-Set (hom-set Y Z))
    (f : type-Set (hom-set X Y)) →
    ( (h ∘ g) ∘ f) ＝ ( h ∘ (g ∘ f))) →
  Large-Nonunital-Precategory α β
make-Large-Nonunital-Precategory
  obj hom-set _∘_ assoc-comp-hom =
  λ where
    .obj-Large-Nonunital-Precategory → obj
    .hom-set-Large-Nonunital-Precategory → hom-set
    .comp-hom-Large-Nonunital-Precategory → _∘_
    .involutive-eq-associative-comp-hom-Large-Nonunital-Precategory h g f →
      involutive-eq-eq (assoc-comp-hom h g f)

{-# INLINE make-Large-Nonunital-Precategory #-}
```

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (C : Large-Nonunital-Precategory α β)
  where

  ap-comp-hom-Large-Nonunital-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-Large-Nonunital-Precategory C l1}
    {Y : obj-Large-Nonunital-Precategory C l2}
    {Z : obj-Large-Nonunital-Precategory C l3}
    {g g' : hom-Large-Nonunital-Precategory C Y Z} (p : g ＝ g')
    {f f' : hom-Large-Nonunital-Precategory C X Y} (q : f ＝ f') →
    comp-hom-Large-Nonunital-Precategory C g f ＝
    comp-hom-Large-Nonunital-Precategory C g' f'
  ap-comp-hom-Large-Nonunital-Precategory =
    ap-binary (comp-hom-Large-Nonunital-Precategory C)

  comp-hom-Large-Nonunital-Precategory' :
    {l1 l2 l3 : Level}
    {X : obj-Large-Nonunital-Precategory C l1}
    {Y : obj-Large-Nonunital-Precategory C l2}
    {Z : obj-Large-Nonunital-Precategory C l3} →
    hom-Large-Nonunital-Precategory C X Y →
    hom-Large-Nonunital-Precategory C Y Z →
    hom-Large-Nonunital-Precategory C X Z
  comp-hom-Large-Nonunital-Precategory' f g =
    comp-hom-Large-Nonunital-Precategory C g f
```

### Nonunital precategories obtained from large nonunital precategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Nonunital-Precategory α β)
  where

  nonunital-precategory-Large-Nonunital-Precategory :
    (l : Level) → Nonunital-Precategory (α l) (β l l)
  pr1 (nonunital-precategory-Large-Nonunital-Precategory l) =
    obj-Large-Nonunital-Precategory C l
  pr1 (pr2 (nonunital-precategory-Large-Nonunital-Precategory l)) =
    hom-set-Large-Nonunital-Precategory C
  pr1 (pr2 (pr2 (nonunital-precategory-Large-Nonunital-Precategory l))) =
    comp-hom-Large-Nonunital-Precategory C
  pr2 (pr2 (pr2 (nonunital-precategory-Large-Nonunital-Precategory l))) =
    involutive-eq-associative-comp-hom-Large-Nonunital-Precategory C
```

### Pre- and postcomposition by a morphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Nonunital-Precategory α β)
  where

  precomp-hom-Large-Nonunital-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-Large-Nonunital-Precategory C l1}
    {Y : obj-Large-Nonunital-Precategory C l2}
    (f : hom-Large-Nonunital-Precategory C X Y) →
    (Z : obj-Large-Nonunital-Precategory C l3) →
    hom-Large-Nonunital-Precategory C Y Z → hom-Large-Nonunital-Precategory C X Z
  precomp-hom-Large-Nonunital-Precategory f Z g =
    comp-hom-Large-Nonunital-Precategory C g f

  postcomp-hom-Large-Nonunital-Precategory :
    {l1 l2 l3 : Level}
    (X : obj-Large-Nonunital-Precategory C l1)
    {Y : obj-Large-Nonunital-Precategory C l2}
    {Z : obj-Large-Nonunital-Precategory C l3}
    (f : hom-Large-Nonunital-Precategory C Y Z) →
    hom-Large-Nonunital-Precategory C X Y → hom-Large-Nonunital-Precategory C X Z
  postcomp-hom-Large-Nonunital-Precategory X f g =
    comp-hom-Large-Nonunital-Precategory C f g
```
