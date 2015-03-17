module Util where
  open import Level using (_⊔_)
  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Function
  open import Data.Vec


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

  if : ∀ {p q} {P : Set p} {Q : Set q} → Dec P → Q → Q → Q
  if p q₁ q₂ = if? p (const q₁) (const q₂)

  if₂ : ∀ {p q r} {P : Set p} {Q : Set q} {R : Set r}
      → Dec P → Dec Q
      → R → R → R → R
      → R
  if₂ p q r₁ r₂ r₃ r₄ = if₂? p q
                          (const (const r₁))
                          (const (const r₂))
                          (const (const r₃))
                          (const (const r₄))


  data all {a p} {A : Set a} (P : Pred A p) : ∀ {n} → Vec A n → Set (a ⊔ p) where
    nil  :                                             all P []
    cons : ∀ {a₀ n} {aₛ : Vec A n} → P a₀ → all P aₛ → all P (a₀ ∷ aₛ)
