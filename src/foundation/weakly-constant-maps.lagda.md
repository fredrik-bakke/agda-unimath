# Weakly constant maps

```agda
module foundation.weakly-constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.fixed-points-endofunctions
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.iterated-dependent-product-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "weakly constant" Disambiguation="map of types" Agda=is-weakly-constant}}
if any two elements in `A` are mapped to
[identical elements](foundation-core.identity-types.md) in `B`.

## Definitions

### The structure on a map of being weakly constant

```agda
is-weakly-constant :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-weakly-constant {A = A} f = (x y : A) → f x ＝ f y
```

### The type of weakly constant maps

```agda
weakly-constant-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
weakly-constant-map A B = Σ (A → B) (is-weakly-constant)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : weakly-constant-map A B)
  where

  map-weakly-constant-map : A → B
  map-weakly-constant-map = pr1 f

  is-weakly-constant-weakly-constant-map :
    is-weakly-constant map-weakly-constant-map
  is-weakly-constant-weakly-constant-map = pr2 f
```

## Properties

### Being weakly constant is a property if the codomain is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  where

  abstract
    is-prop-is-weakly-constant-Set : is-prop (is-weakly-constant f)
    is-prop-is-weakly-constant-Set =
      is-prop-iterated-Π 2 (λ x y → is-set-type-Set B (f x) (f y))

  is-weakly-constant-prop-Set : Prop (l1 ⊔ l2)
  pr1 is-weakly-constant-prop-Set = is-weakly-constant f
  pr2 is-weakly-constant-prop-Set = is-prop-is-weakly-constant-Set
```

### The action on identifications of a weakly constant map is weakly constant

This is Auxiliary Lemma 4.3 of {{#cite KECA17}}.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  (H : is-weakly-constant f)
  where

  compute-ap-is-weakly-constant :
    {x y : X} (p : x ＝ y) → inv (H x x) ∙ H x y ＝ ap f p
  compute-ap-is-weakly-constant {x} refl = left-inv (H x x)

  is-weakly-constant-ap : {x y : X} → is-weakly-constant (ap f {x} {y})
  is-weakly-constant-ap {x} {y} p q =
    ( inv (compute-ap-is-weakly-constant p)) ∙
    ( compute-ap-is-weakly-constant q)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (f : weakly-constant-map X Y)
  where

  ap-weakly-constant-map :
    {x y : X} →
    weakly-constant-map
      ( x ＝ y)
      ( map-weakly-constant-map f x ＝ map-weakly-constant-map f y)
  ap-weakly-constant-map {x} {y} =
    ( ap (map-weakly-constant-map f) {x} {y} ,
      is-weakly-constant-ap (is-weakly-constant-weakly-constant-map f))
```

### The type of fixed points of a weakly constant endomap is a proposition

This is Lemma 4.1 of {{#cite KECA17}}. We follow the second proof, due to
Christian Sattler.

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : is-weakly-constant f)
  where

  is-proof-irrelevant-fixed-point-is-weakly-constant-endomap :
    is-proof-irrelevant (fixed-point f)
  is-proof-irrelevant-fixed-point-is-weakly-constant-endomap (x , p) =
    is-contr-equiv
      ( Σ A (λ z → f x ＝ z))
      ( equiv-tot (λ z → equiv-concat (H x z) z))
      ( is-torsorial-Id (f x))

  is-prop-fixed-point-is-weakly-constant-endomap : is-prop (fixed-point f)
  is-prop-fixed-point-is-weakly-constant-endomap =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-fixed-point-is-weakly-constant-endomap)

  fixed-point-prop-is-weakly-constant-endomap : Prop l
  fixed-point-prop-is-weakly-constant-endomap =
    ( fixed-point f , is-prop-fixed-point-is-weakly-constant-endomap)
```

### The type of fixed points of a weakly constant endomap is equivalent to the propositional truncation

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : is-weakly-constant f)
  where

  has-fixed-point-has-element-is-weakly-constant-endomap : A → fixed-point f
  has-fixed-point-has-element-is-weakly-constant-endomap x = (f x , H (f x) x)

  has-fixed-point-is-inhabited-type-is-weakly-constant-endomap :
    is-inhabited A → fixed-point f
  has-fixed-point-is-inhabited-type-is-weakly-constant-endomap =
    rec-trunc-Prop
      ( fixed-point-prop-is-weakly-constant-endomap H)
      ( has-fixed-point-has-element-is-weakly-constant-endomap)

  iff-has-fixed-point-is-inhabited-type-is-weakly-constant-endomap :
    is-inhabited A ↔ fixed-point f
  iff-has-fixed-point-is-inhabited-type-is-weakly-constant-endomap =
    ( has-fixed-point-is-inhabited-type-is-weakly-constant-endomap ,
      unit-trunc-Prop ∘ pr1)
```

## References

{{#bibliography}} {{#reference KECA17}}

## External links

- [weakly constant function](https://ncatlab.org/nlab/show/weakly+constant+function)
  at $n$Lab
