open import Relation.Binary using (DecSetoid)
module Core {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
            {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Level public using (_⊔_)
  open import Relation.Binary

  open DecSetoid primitiveType public using ()
    renaming (Carrier to PrimitiveType;
              _≈_     to _≡ᵢ_;
              _≟_     to _≟ᵢ_;
              refl    to ≡ᵢ-refl;
              sym     to ≡ᵢ-sym;
              trans   to ≡ᵢ-trans)

  open DecSetoid typeVariable public using ()
    renaming (Carrier to TypeVariable;
              _≈_     to _≡ₜᵥ_;
              _≟_     to _≟ₜᵥ_;
              refl    to ≡ₜᵥ-refl;
              sym     to ≡ₜᵥ-sym;
              trans   to ≡ₜᵥ-trans)
