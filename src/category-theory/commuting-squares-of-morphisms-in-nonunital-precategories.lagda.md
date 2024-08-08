# Commuting squares of morphisms in nonunital precategories

```agda
module category-theory.commuting-squares-of-morphisms-in-nonunital-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-set-magmoids
open import category-theory.nonunital-precategories

open import foundation.universe-levels
```

</details>

## Idea

A square of morphisms

```text
  x ------> y
  |         |
  |         |
  ∨         ∨
  z ------> w
```

in a [nonunital precategory](category-theory.nonunital-precategories.md) `C` is
said to **commute** if there is an
[identification](foundation-core.identity-types.md) between both composites:

```text
  bottom ∘ left ＝ right ∘ top.
```

## Definitions

```agda
coherence-square-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  {x y z w : obj-Nonunital-Precategory C}
  (top : hom-Nonunital-Precategory C x y)
  (left : hom-Nonunital-Precategory C x z)
  (right : hom-Nonunital-Precategory C y w)
  (bottom : hom-Nonunital-Precategory C z w) →
  UU l2
coherence-square-hom-Nonunital-Precategory C =
  coherence-square-hom-Set-Magmoid (set-magmoid-Nonunital-Precategory C)
```
