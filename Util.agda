module Util where
  open import Level using (_⊔_)
  open import Relation.Nullary
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality

  if? : ∀ {p q} {P : Set p} {Q : Set q} → Dec P → (P → Q) → (¬ P → Q) → Q
  if? (yes p) q₁ q₂ = q₁  p
  if? (no ¬p) q₁ q₂ = q₂ ¬p

  if₂? : ∀ {p q r} {P : Set p} {Q : Set q} {R : Set r}
       → Dec P → Dec Q
       → (  P →   Q → R)
       → (  P → ¬ Q → R)
       → (¬ P →   Q → R)
       → (¬ P → ¬ Q → R)
       → R
  if₂? (yes p) (yes q) pq _   _   _    = pq    p  q
  if₂? (yes p) (no ¬q) _  p¬q _   _    = p¬q   p ¬q
  if₂? (no ¬p) (yes q) _  _   ¬pq _    = ¬pq  ¬p  q
  if₂? (no ¬p) (no ¬q) _  _   _   ¬p¬q = ¬p¬q ¬p ¬q

  -- cong-rel : ∀ {c ℓ} {X : Set c}
  --          → (_~_ : Rel X ℓ)
  --          → ∀ {a b} → a ≡ b → a ~ b
  -- cong-rel _~_ refl = {!!}
