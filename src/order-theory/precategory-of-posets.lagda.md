# The precategory of posets

```agda
module order-theory.precategory-of-posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

The **(large) precategory of posets** consists of
[posets](order-theory.posets.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md).

## Definitions

### The large precategory of posets

```agda
parametric-Poset-Large-Precategory :
  (α β : Level → Level) →
  Large-Precategory
    ( λ l → lsuc (α l) ⊔ lsuc (β l))
    ( λ l1 l2 → α l1 ⊔ β l1 ⊔ α l2 ⊔ β l2)
parametric-Poset-Large-Precategory α β =
  λ where
    .obj-Large-Precategory l → Poset (α l) (β l)
    .hom-set-Large-Precategory → hom-set-Poset
    .comp-hom-Large-Precategory {X = X} {Y} {Z} → comp-hom-Poset X Y Z
    .id-hom-Large-Precategory {X = X} → id-hom-Poset X
    .associative-comp-hom-Large-Precategory {X = X} {Y} {Z} {W} →
      associative-comp-hom-Poset X Y Z W
    .inv-associative-comp-hom-Large-Precategory {X = X} {Y} {Z} {W} →
      inv-associative-comp-hom-Poset X Y Z W
    .left-unit-law-comp-hom-Large-Precategory {X = X} {Y} →
      left-unit-law-comp-hom-Poset X Y
    .right-unit-law-comp-hom-Large-Precategory {X = X} {Y} →
      right-unit-law-comp-hom-Poset X Y

Poset-Large-Precategory : Large-Precategory lsuc (_⊔_)
Poset-Large-Precategory = parametric-Poset-Large-Precategory (λ l → l) (λ l → l)
```

### The precategory or posets of universe level `l`

```agda
Poset-Precategory : (l : Level) → Precategory (lsuc l) l
Poset-Precategory = precategory-Large-Precategory Poset-Large-Precategory
```
