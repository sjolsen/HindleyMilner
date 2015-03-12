open import Relation.Binary using (DecSetoid)
module Free {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
            {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Core primitiveType typeVariable
  open import Type primitiveType typeVariable
  open import Util
  open import Relation.Nullary
  open import Relation.Binary



  data _∈free₀_ (α : TypeVariable) : Type → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    TVar  : (β : TypeVariable) → α ≡ₜᵥ β     → α ∈free₀ TVar β
    Funcₗ : (τ₀ τ₁ : Type)     → α ∈free₀ τ₀ → α ∈free₀ Func τ₀ τ₁
    Funcᵣ : (τ₀ τ₁ : Type)     → α ∈free₀ τ₁ → α ∈free₀ Func τ₀ τ₁

  private
    ∈free₀-elim₀ : ∀ {α β} {p} {P : Set p}
                 → (α ≡ₜᵥ β         → P)
                 → (α ∈free₀ TVar β → P)
    ∈free₀-elim₀ p (TVar _ α≡β) = p α≡β

    ∈free₀-elim₂ : ∀ {α τ₀ τ₁} {p} {P : Set p}
                 → (α ∈free₀ τ₀         → P)
                 → (α ∈free₀ τ₁         → P)
                 → (α ∈free₀ Func τ₀ τ₁ → P)
    ∈free₀-elim₂ p₁ _ (Funcₗ _ _ α∈freeτ₀) = p₁ α∈freeτ₀
    ∈free₀-elim₂ _ p₂ (Funcᵣ _ _ α∈freeτ₁) = p₂ α∈freeτ₁

  _∈free₀?_ : Decidable _∈free₀_
  α ∈free₀? TVar β     = if? (α ≟ₜᵥ β)
                           (λ α≡β → yes (TVar β α≡β))
                           (λ α≢β → no  (∈free₀-elim₀ α≢β))
  α ∈free₀? Prim ι     = no (λ ())
  α ∈free₀? Func τ₀ τ₁ = if₂? (α ∈free₀? τ₀)
                              (α ∈free₀? τ₁)
                           (λ y₀ y₁ → yes (Funcₗ τ₀ τ₁ y₀))
                           (λ y₀ n₁ → yes (Funcₗ τ₀ τ₁ y₀))
                           (λ n₀ y₁ → yes (Funcᵣ τ₀ τ₁ y₁))
                           (λ n₀ n₁ → no  (∈free₀-elim₂ n₀ n₁))
