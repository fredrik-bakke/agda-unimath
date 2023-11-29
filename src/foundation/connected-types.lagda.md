# Connected types

```agda
module foundation.connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be **`k`-connected** if its `k`-truncation is contractible.

## Definition

```agda
is-connected-Prop : {l : Level} (k : 𝕋) → UU l → Prop l
is-connected-Prop k A = is-contr-Prop (type-trunc k A)

is-connected : {l : Level} (k : 𝕋) → UU l → UU l
is-connected k A = type-Prop (is-connected-Prop k A)

is-prop-is-connected :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-connected k A)
is-prop-is-connected k A = is-prop-type-Prop (is-connected-Prop k A)
```

## Properties

### All types are `(-2)`-connected

```agda
is-neg-two-connected : {l : Level} (A : UU l) → is-connected neg-two-𝕋 A
is-neg-two-connected A = is-trunc-type-trunc
```

### A type `A` is `k`-connected if and only if the map `B → (A → B)` is an equivalence for every `k`-truncated type `B`

```agda
is-equiv-diagonal-is-connected :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k) →
  is-connected k A →
  is-equiv (λ (b : type-Truncated-Type B) → const A (type-Truncated-Type B) b)
is-equiv-diagonal-is-connected B H =
  is-equiv-comp
    ( precomp unit-trunc (type-Truncated-Type B))
    ( λ b → const _ _ b)
    ( is-equiv-diagonal-is-contr H (type-Truncated-Type B))
    ( is-truncation-trunc B)
```

### An inhabited type `A` is `k + 1`-connected if and only if its identity types are `k`-connected

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  abstract
    is-inhabited-is-connected :
      is-connected (succ-𝕋 k) A → is-inhabited A
    is-inhabited-is-connected H =
      map-universal-property-trunc
        ( truncated-type-Prop k (is-inhabited-Prop A))
        ( unit-trunc-Prop)
        ( center H)

  abstract
    is-connected-eq-is-connected :
      is-connected (succ-𝕋 k) A → {x y : A} → is-connected k (x ＝ y)
    is-connected-eq-is-connected H {x} {y} =
      is-contr-equiv
        ( unit-trunc x ＝ unit-trunc y)
        ( effectiveness-trunc k x y)
        ( is-prop-is-contr H (unit-trunc x) (unit-trunc y))

  abstract
    is-connected-succ-is-connected-eq :
      is-inhabited A → ((x y : A) → is-connected k (x ＝ y)) →
      is-connected (succ-𝕋 k) A
    is-connected-succ-is-connected-eq H K =
      apply-universal-property-trunc-Prop H
        ( is-connected-Prop (succ-𝕋 k) A)
        ( λ a →
          ( unit-trunc a) ,
          ( function-dependent-universal-property-trunc
            ( Id-Truncated-Type
              ( truncated-type-succ-Truncated-Type
                ( succ-𝕋 k)
                ( trunc (succ-𝕋 k) A))
              ( unit-trunc a))
            ( λ x →
              map-universal-property-trunc
                ( Id-Truncated-Type
                  ( trunc (succ-𝕋 k) A)
                  ( unit-trunc a)
                  ( unit-trunc x))
                ( λ where refl → refl)
                ( center (K a x)))))
```

### Contractible types are `k`-connected for any `k`

```agda
module _
  (k : 𝕋) {l : Level} {A : UU l}
  where

  is-connected-is-contr : is-contr A → is-connected k A
  is-connected-is-contr c =
    is-contr-is-equiv' A unit-trunc (is-equiv-unit-trunc-is-contr k A c) c
```

### Being connected is invariant under equivalence

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-is-equiv :
    (f : A → B) → is-equiv f → is-connected k B → is-connected k A
  is-connected-is-equiv f e =
    is-contr-is-equiv
      ( type-trunc k B)
      ( map-trunc k f)
      ( is-equiv-map-equiv-trunc k (f , e))

  is-connected-equiv :
    A ≃ B → is-connected k B → is-connected k A
  is-connected-equiv f =
    is-connected-is-equiv (map-equiv f) (is-equiv-map-equiv f)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-equiv' :
    A ≃ B → is-connected k A → is-connected k B
  is-connected-equiv' f = is-connected-equiv (inv-equiv f)

  is-connected-is-equiv' :
    (f : A → B) → is-equiv f → is-connected k A → is-connected k B
  is-connected-is-equiv' f e = is-connected-equiv' (f , e)
```
