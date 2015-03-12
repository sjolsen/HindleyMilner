open import Relation.Binary using (DecSetoid)
module Type {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
            {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Core primitiveType typeVariable
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Function
  open import Util



  data Type : Set (c₀ ⊔ c₁) where
    TVar : (α : TypeVariable)  → Type
    Prim : (ι : PrimitiveType) → Type
    Func : (τ₀ τ₁ : Type)      → Type

  data _≡ₜ_ : (τ₀ τ₁ : Type) → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    TVar : (α β : TypeVariable)  → α  ≡ₜᵥ β             → TVar α     ≡ₜ TVar β
    Prim : (ι κ : PrimitiveType) → ι  ≡ᵢ  κ             → Prim ι     ≡ₜ Prim κ
    Func : (τ₀ τ₁ τ₂ τ₃ : Type)  → τ₀ ≡ₜ  τ₂ → τ₁ ≡ₜ τ₃ → Func τ₀ τ₁ ≡ₜ Func τ₂ τ₃

  private
    ≡ₜ-elim₀ : ∀ {α β} → TVar α ≡ₜ TVar β → α ≡ₜᵥ β
    ≡ₜ-elim₀ (TVar _ _ α≡β) = α≡β

    ≡ₜ-elim₁ : ∀ {ι κ} → Prim ι ≡ₜ Prim κ → ι ≡ᵢ κ
    ≡ₜ-elim₁ (Prim _ _ ι≡κ) = ι≡κ

    ≡ₜ-elim₂ₗ : ∀ {τ₀ τ₁ τ₂ τ₃} → Func τ₀ τ₁ ≡ₜ Func τ₂ τ₃ → τ₀ ≡ₜ τ₂
    ≡ₜ-elim₂ₗ (Func _ _ _ _ τ₀≡τ₂ _) = τ₀≡τ₂

    ≡ₜ-elim₂ᵣ : ∀ {τ₀ τ₁ τ₂ τ₃} → Func τ₀ τ₁ ≡ₜ Func τ₂ τ₃ → τ₁ ≡ₜ τ₃
    ≡ₜ-elim₂ᵣ (Func _ _ _ _ _ τ₁≡τ₃) = τ₁≡τ₃

  _≟ₜ_ : Decidable _≡ₜ_
  TVar α     ≟ₜ TVar β     = if? (α ≟ₜᵥ β)
                               (λ α≡β → yes (TVar α β α≡β))
                               (λ α≢β → no  (contraposition ≡ₜ-elim₀ α≢β))
  Prim ι     ≟ₜ Prim κ     = if? (ι ≟ᵢ κ)
                               (λ ι≡κ → yes (Prim ι κ ι≡κ))
                               (λ ι≢κ → no  (contraposition ≡ₜ-elim₁ ι≢κ))
  Func τ₀ τ₁ ≟ₜ Func τ₂ τ₃ = if₂? (τ₀ ≟ₜ τ₂)
                                  (τ₁ ≟ₜ τ₃)
                               (λ τ₀≡τ₂ τ₁≡τ₃ → yes (Func τ₀ τ₁ τ₂ τ₃ τ₀≡τ₂ τ₁≡τ₃))
                               (λ τ₀≡τ₂ τ₁≢τ₃ → no (contraposition ≡ₜ-elim₂ᵣ τ₁≢τ₃))
                               (λ τ₀≢τ₂ τ₁≡τ₃ → no (contraposition ≡ₜ-elim₂ₗ τ₀≢τ₂))
                               (λ τ₀≢τ₂ τ₁≢τ₃ → no (contraposition ≡ₜ-elim₂ₗ τ₀≢τ₂))
  TVar _     ≟ₜ Prim _     = no (λ ())
  TVar _     ≟ₜ Func _  _  = no (λ ())
  Prim _     ≟ₜ TVar _     = no (λ ())
  Prim _     ≟ₜ Func _  _  = no (λ ())
  Func _  _  ≟ₜ TVar _     = no (λ ())
  Func _  _  ≟ₜ Prim _     = no (λ ())
