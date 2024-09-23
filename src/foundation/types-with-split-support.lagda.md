# Types with split support

```agda
module foundation.types-with-split-support where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.sections
```

</details>

## Idea

A type `A` is said to have
{{#concept "split support" Disambiguation="type" Agda=has-split-support}} if we
can recover an element of `A` from every proof of
[inhabitedness](foundation.inhabited-types.md) of `A`.

A type has split support if any of the following
[logically equivalent](foundation.logical-equivalences.md) conditions hold:

1. There is a map `║A║₋₁ → A`.
2. The unit of the propositional truncation `η : A → ║A║₋₁` has a
   [section](foundation-core.sections.md).
3. There is a [weakly constant endomap](foundation.weakly-constant-maps.md) on
   `A`.

## Definitions

### Split support on a type

```agda
has-split-support : {l : Level} → UU l → UU l
has-split-support A = is-inhabited A → A
```

## Properties

### Split support maps are sections of the unit of the propoisitional truncation

```agda
module _
  {l : Level} {A : UU l} (ε : has-split-support A)
  where

  is-section-has-split-support : is-section unit-trunc-Prop ε
  is-section-has-split-support x =
    all-elements-equal-type-trunc-Prop (unit-trunc-Prop (ε x)) x

  section-unit-trunc-prop-has-split-support : section (unit-trunc-Prop {A = A})
  section-unit-trunc-prop-has-split-support = ε , is-section-has-split-support

module _
  {l : Level} {A : UU l}
  where

  iff-section-unit-trunc-prop-has-split-support :
    has-split-support A ↔ section (unit-trunc-Prop {A = A})
  iff-section-unit-trunc-prop-has-split-support =
    ( section-unit-trunc-prop-has-split-support , map-section unit-trunc-Prop)
```

### A type has split support if and only if it has a weakly constant endofunction

```agda
module _
  {l : Level} {A : UU l} (ε : has-split-support A)
  where

  map-weakly-constant-endomap-has-split-support : A → A
  map-weakly-constant-endomap-has-split-support = ε ∘ unit-trunc-Prop

  is-weakly-constant-map-weakly-constant-endomap-has-split-support :
    is-weakly-constant map-weakly-constant-endomap-has-split-support
  is-weakly-constant-map-weakly-constant-endomap-has-split-support x y =
    ap
      ( ε)
      ( all-elements-equal-type-trunc-Prop
        ( unit-trunc-Prop x)
        ( unit-trunc-Prop y))

  weakly-constant-endomap-has-split-support : weakly-constant-map A A
  weakly-constant-endomap-has-split-support =
    ( map-weakly-constant-endomap-has-split-support ,
      is-weakly-constant-map-weakly-constant-endomap-has-split-support)

module _
  {l : Level} {A : UU l} (f : weakly-constant-map A A)
  where

  has-split-support-weakly-constant-endomap : has-split-support A
  has-split-support-weakly-constant-endomap |a| =
    pr1
      ( has-fixed-point-is-inhabited-type-is-weakly-constant-endomap
        ( is-weakly-constant-weakly-constant-map f)
        ( |a|))

module _
  {l : Level} {A : UU l}
  where

  iff-weakly-constant-endomap-has-split-support :
    has-split-support A ↔ weakly-constant-map A A
  iff-weakly-constant-endomap-has-split-support =
    ( weakly-constant-endomap-has-split-support ,
      has-split-support-weakly-constant-endomap)
```

## External links

- [split support](https://ncatlab.org/nlab/show/split+support) at $n$Lab
