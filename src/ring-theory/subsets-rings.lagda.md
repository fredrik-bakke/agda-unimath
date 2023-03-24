# Subsets of rings

```agda
module ring-theory.subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.subgroups-abelian-groups

open import ring-theory.rings
```

</details>

## Idea

A subset of a ring is a subtype of the underlying type of a ring

## Definition

### Subsets of rings

```agda
subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
subset-Ring l R = subtype l (type-Ring R)

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-in-subset-Ring : type-Ring R → UU l2
  is-in-subset-Ring = is-in-subtype S

  is-prop-is-in-subset-Ring : (x : type-Ring R) → is-prop (is-in-subset-Ring x)
  is-prop-is-in-subset-Ring = is-prop-is-in-subtype S

  type-subset-Ring : UU (l1 ⊔ l2)
  type-subset-Ring = type-subtype S

  inclusion-subset-Ring : type-subset-Ring → type-Ring R
  inclusion-subset-Ring = inclusion-subtype S

  ap-inclusion-subset-Ring :
    (x y : type-subset-Ring) →
    x ＝ y → (inclusion-subset-Ring x ＝ inclusion-subset-Ring y)
  ap-inclusion-subset-Ring = ap-inclusion-subtype S

  is-in-subset-inclusion-subset-Ring :
    (x : type-subset-Ring) → is-in-subset-Ring (inclusion-subset-Ring x)
  is-in-subset-inclusion-subset-Ring =
    is-in-subtype-inclusion-subtype S

  is-closed-under-eq-subset-Ring :
    {x y : type-Ring R} → is-in-subset-Ring x → (x ＝ y) → is-in-subset-Ring y
  is-closed-under-eq-subset-Ring =
    is-closed-under-eq-subtype S

  is-closed-under-eq-subset-Ring' :
    {x y : type-Ring R} → is-in-subset-Ring y → (x ＝ y) → is-in-subset-Ring x
  is-closed-under-eq-subset-Ring' =
    is-closed-under-eq-subtype' S
```

## Conditions on subsets of rings

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  contains-zero-subset-Ring : UU l2
  contains-zero-subset-Ring = is-in-subset-Ring R S (zero-Ring R)

  is-prop-contains-zero-subset-Ring : is-prop contains-zero-subset-Ring
  is-prop-contains-zero-subset-Ring =
    is-prop-is-in-subset-Ring R S (zero-Ring R)
```

### The condition that a subset contains another subset

```agda
  contains-one-subset-Ring : UU l2
  contains-one-subset-Ring = is-in-subset-Ring R S (one-Ring R)

  is-prop-contains-one-subset-Ring : is-prop contains-one-subset-Ring
  is-prop-contains-one-subset-Ring =
    is-prop-is-in-subset-Ring R S (one-Ring R)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Ring =
    (x y : type-Ring R) →
    is-in-subset-Ring R S x →
    is-in-subset-Ring R S y →
    is-in-subset-Ring R S (add-Ring R x y)

  is-prop-is-closed-under-addition-subset-Ring :
    is-prop is-closed-under-addition-subset-Ring
  is-prop-is-closed-under-addition-subset-Ring =
    is-prop-Π
      λ x → is-prop-Π
        λ y → is-prop-Π
          λ _ → is-prop-Π
            λ _ → is-prop-is-in-subset-Ring R S (add-Ring R x y)
```

### The condition that a subset is closed under negatives

```agda
  is-closed-under-negatives-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Ring =
    (x : type-Ring R) →
    is-in-subset-Ring R S x → is-in-subset-Ring R S (neg-Ring R x)

  is-prop-is-closed-under-negatives-subset-Ring :
    is-prop is-closed-under-negatives-subset-Ring
  is-prop-is-closed-under-negatives-subset-Ring =
    is-prop-Π
      λ x → is-prop-Π
        λ _ → is-prop-is-in-subset-Ring R S (neg-Ring R x)
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Ring =
    (x y : type-Ring R) →
    is-in-subset-Ring R S x →
    is-in-subset-Ring R S y →
    is-in-subset-Ring R S (mul-Ring R x y)

  is-prop-is-closed-under-multiplication-subset-Ring :
    is-prop is-closed-under-multiplication-subset-Ring
  is-prop-is-closed-under-multiplication-subset-Ring =
    is-prop-Π
      λ x → is-prop-Π
        λ y → is-prop-Π
          λ _ → is-prop-Π
            λ _ → is-prop-is-in-subset-Ring R S (mul-Ring R x y)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Ring =
    (x y : type-Ring R) →
    is-in-subset-Ring R S y →
    is-in-subset-Ring R S (mul-Ring R x y)

  is-prop-is-closed-under-left-multiplication-subset-Ring :
    is-prop is-closed-under-left-multiplication-subset-Ring
  is-prop-is-closed-under-left-multiplication-subset-Ring =
    is-prop-Π
      λ x → is-prop-Π
        λ y → is-prop-Π
            λ _ → is-prop-is-in-subset-Ring R S (mul-Ring R x y)
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Ring =
    (x y : type-Ring R) →
    is-in-subset-Ring R S x →
    is-in-subset-Ring R S (mul-Ring R x y)

  is-prop-is-closed-under-right-multiplication-subset-Ring :
    is-prop is-closed-under-right-multiplication-subset-Ring
  is-prop-is-closed-under-right-multiplication-subset-Ring =
    is-prop-Π
      λ x → is-prop-Π
        λ y → is-prop-Π
            λ _ → is-prop-is-in-subset-Ring R S (mul-Ring R x y)
```

### The condition that a subset is an additive subgroup

```agda
module _
  {l1 : Level} (R : Ring l1) {l2 : Level} (S : subset-Ring l2 R)
  where

  is-additive-subgroup-subset-Ring : UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Ring = is-subgroup-Ab (ab-Ring R) S

  is-prop-is-additive-subgroup-subset-Ring :
    is-prop is-additive-subgroup-subset-Ring
  is-prop-is-additive-subgroup-subset-Ring =
    is-prop-is-subgroup-Ab (ab-Ring R) S
```
