# Multivariable families of equivalences

```agda
module foundation.homotopies-iterated-dependent-product-types where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-extensionality
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

Given an
[iterated dependent product](foundation.iterated-dependent-product-types.md) we
can consider [homotopies](foundation-core.homotopies.md) of its elements. By
[function extensionality](foundation.function-extensionality.md), **iterated
homotopies** are [equivalent](foundation-core.equivalences.md) to
[identifications](foundation-core.identity-types.md).

## Definitions

### Homotopies in iterated dependent products of iterated type families

```agda
equiv-iterated-family :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-Π A) → UU l
equiv-iterated-family {{base-telescope A}} f g = f ＝ g
equiv-iterated-family {{cons-telescope A}} f g =
  (x : _) → equiv-iterated-family {{A x}} (f x) (g x)
```

### Iterated function extensionality

```agda
refl-equiv-iterated-family :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f : iterated-Π A} → equiv-iterated-family {{A}} f f
refl-equiv-iterated-family .0 {{base-telescope A}} = refl
refl-equiv-iterated-family ._ {{cons-telescope A}} x = refl-equiv-iterated-family _ {{A x}}

equiv-iterated-family-eq :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → f ＝ g → equiv-iterated-family {{A}} f g
equiv-iterated-family-eq .0 {{base-telescope A}} p = p
equiv-iterated-family-eq ._ {{cons-telescope A}} p x =
  equiv-iterated-family-eq _ {{A x}} (htpy-eq p x)

eq-equiv-iterated-family :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → equiv-iterated-family {{A}} f g → f ＝ g
eq-equiv-iterated-family .0 {{base-telescope A}} H = H
eq-equiv-iterated-family ._ {{cons-telescope A}} H =
  eq-htpy (λ x → eq-equiv-iterated-family _ {{A x}} (H x))

equiv-iterated-funext :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → (f ＝ g) ≃ equiv-iterated-family {{A}} f g
equiv-iterated-funext .0 {{base-telescope A}} = id-equiv
equiv-iterated-funext ._ {{cons-telescope A}} =
  equiv-Π-equiv-family (λ x → equiv-iterated-funext _ {{A x}}) ∘e equiv-funext
```
