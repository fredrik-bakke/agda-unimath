# Global modal operators

```agda
module orthogonal-factorization-systems.global-modal-operators where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.global-subuniverses
open import foundation.propositions
open import foundation.small-types
open import foundation.subuniverses
open import foundation.universe-levels
```

</details>

## Idea

Underlying every global modality is a
{{#concept "modal operator" Agda=operator-global-modality}}, which is an
operation on types at every universe level that construct new types. For a
_monadic_ modality `○`, there is moreover a
{{#concept "modal unit" Disambiguation="monadic modality" Agda=unit-global-modality}}
which is a family of comparison maps for every type `X` from `X` into its modal
image `○ X`.

## Definitions

### Global modal operators

```agda
operator-global-modality : (α : Level → Level) → UUω
operator-global-modality α = {l : Level} → UU l → UU (α l)
```

### Units of global modal operators

```agda
unit-global-modality :
  {α : Level → Level} → operator-global-modality α → UUω
unit-global-modality {α} ○ = {l : Level} {X : UU l} → X → ○ X
```

### The predicate on types of being modal

Given a global modal operator and a modal unit, we say that a type `X` is
{{#concept "modal" Disambiguation="type" Agda=is-modal}} if the unit is an
equivalence at `X`.

```agda
module _
  {α : Level → Level}
  {○ : operator-global-modality α}
  (unit-○ : unit-global-modality ○)
  where

  is-modal : {l : Level} (X : UU l) → UU (α l ⊔ l)
  is-modal X = is-equiv (unit-○ {X = X})

  is-modal-family :
    {l1 l2 : Level} {X : UU l1} (P : X → UU l2) → UU (α l2 ⊔ l1 ⊔ l2)
  is-modal-family {X = X} P = (x : X) → is-modal (P x)

  modal-type : (l : Level) → UU (α l ⊔ lsuc l)
  modal-type l = Σ (UU l) (is-modal)

  modal-subuniverse : {l : Level} → subuniverse l (α l ⊔ l)
  modal-subuniverse X = is-equiv-Prop (unit-○ {X = X})

  is-property-is-modal : {l : Level} (X : UU l) → is-prop (is-modal X)
  is-property-is-modal X = is-prop-type-Prop (modal-subuniverse X)
```

## Properties

### Modal types form a global subuniverse

<!-- TODO We need functoriality to prove closure under equivs -->

```agda
-- module _
--   {α : Level → Level}
--   {○ : operator-global-modality α}
--   (unit-○ : unit-global-modality ○)
--   where

--   is-closed-under-equiv-modal-global-subuniverse :
--     is-closed-under-equiv-subuniverses
--       ( λ l → α l ⊔ l)
--       ( λ l → modal-subuniverse unit-○)
--   is-closed-under-equiv-modal-global-subuniverse X Y e is-modal-X = {! is-equiv-  !}

--   modal-global-subuniverse : global-subuniverse (λ l → α l ⊔ l)
--   modal-global-subuniverse =
--     λ where
--     .subuniverse-global-subuniverse l → modal-subuniverse unit-○
--     .is-closed-under-equiv-global-subuniverse → {!   !}
```

## References

{{#bibliography}} {{#reference RSS20}}
