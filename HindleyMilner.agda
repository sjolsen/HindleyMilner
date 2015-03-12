open import Relation.Binary using (DecSetoid)
module HindleyMilner {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
                     {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Core primitiveType typeVariable
  open import Type primitiveType typeVariable
  open import Free primitiveType typeVariable
