--------------------------------------------------------------------------------
-- Ettore Aldrovandi aldrovandi@math.fsu.edu
-- Keri D'Angelo kd349@cornell.edu

-- Jul 17, 2021
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import SpartanMLTT hiding ( ₀ ; ₁)
open import Groups
open import CrossedModules.CrossedModules

module CrossedModules.CommutativeStructures where

bracket : (G : CrossedModule {𝓤} {𝓥}) → 𝓤 ⊔ 𝓥 ̇
bracket G = ⟨ G ₀ ⟩ → ⟨ G ₀ ⟩ → ⟨ G ₁ ⟩
  where
    open CrossedModule

-- syntax bracket a b = [ a , b ]

record isBraiding {G : CrossedModule {𝓤} {𝓥}} ([_,_] : bracket G) : (𝓤 ⊔ 𝓥) ⁺ ̇ where
  open CrossedModule
  field
    γ : ∀ {x y} → (∂ G ([ x , y ]) ·⟨ G ₀ ⟩ y) ·⟨ G ₀ ⟩ x ≡ x ·⟨ G ₀ ⟩ y

\end{code}

{-
-- Braiding of a CrossedModule

 record IsBraided (X : CrossedModule {𝓤} {𝓥}) (bracketOp : ⟨ CrossedModule.G₀ X ⟩ → ⟨ CrossedModule.G₀ X ⟩ → ⟨ CrossedModule.G₁ X ⟩) : (𝓤 ⊔ 𝓥) ⁺ ̇ where
   open CrossedModule
   field
     T1 : (a b : ⟨ G₀ X ⟩) → (((δ X) (bracketOp a b) ·⟨ G₀ X ⟩ b) ·⟨ G₀ X ⟩ a ≡ a ·⟨ G₀ X ⟩ b)
     T2 : (h : ⟨ G₁ X ⟩) (b : ⟨ G₀ X ⟩) → (bracketOp ((δ X) h) b ≡ h ·⟨ G₁ X ⟩ (pr₁ (ρ X)) b (inv (G₁ X) h))
     T3 : (a : ⟨ G₀ X ⟩) (h : ⟨ G₁ X ⟩) → ((bracketOp a ((δ X) h)) ·⟨ G₁ X ⟩ h ≡ (pr₁ (ρ X)) a h)
     T4 : (a b c : ⟨ G₀ X ⟩) → (bracketOp a (b ·⟨ G₀ X ⟩ c) ≡ (bracketOp a b) ·⟨ G₁ X ⟩ ((pr₁ (ρ X)) b (bracketOp a c)))
     T5 : (a b c : ⟨ G₀ X ⟩) → (bracketOp (a ·⟨ G₀ X ⟩ b) c ≡ ((pr₁ (ρ X)) a (bracketOp b c)) ·⟨ G₁ X ⟩ (bracketOp a c))


 record Braiding : (𝓤 ⊔ 𝓥) ⁺ ̇ where
   open CrossedModule
   field
     X : CrossedModule {𝓤} {𝓥}
     bracketOp : ⟨ G₀ X ⟩ → ⟨ G₀ X ⟩ → ⟨ G₁ X ⟩
     T1 : (a b : ⟨ G₀ X ⟩) → (((δ X) (bracketOp a b) ·⟨ G₀ X ⟩ b) ·⟨ G₀ X ⟩ a ≡ a ·⟨ G₀ X ⟩ b)
     T2 : (h : ⟨ G₁ X ⟩) (b : ⟨ G₀ X ⟩) → (bracketOp ((δ X) h) b ≡ h ·⟨ G₁ X ⟩ (pr₁ (ρ X)) b (inv (G₁ X) h))
     T3 : (a : ⟨ G₀ X ⟩) (h : ⟨ G₁ X ⟩) → ((bracketOp a ((δ X) h)) ·⟨ G₁ X ⟩ h ≡ (pr₁ (ρ X)) a h)
     T4 : (a b c : ⟨ G₀ X ⟩) → (bracketOp a (b ·⟨ G₀ X ⟩ c) ≡ (bracketOp a b) ·⟨ G₁ X ⟩ ((pr₁ (ρ X)) b (bracketOp a c)))
     T5 : (a b c : ⟨ G₀ X ⟩) → (bracketOp (a ·⟨ G₀ X ⟩ b) c ≡ ((pr₁ (ρ X)) a (bracketOp b c)) ·⟨ G₁ X ⟩ (bracketOp a c))

     



-- A Symmetric Braiding



 record SymmetricBraiding (X : CrossedModule {𝓤} {𝓥}) (bracketOp : ⟨ CrossedModule.G₀ X ⟩ → ⟨ CrossedModule.G₀ X ⟩ → ⟨ CrossedModule.G₁ X ⟩) : (𝓤 ⊔ 𝓥) ⁺ ̇ where
   open CrossedModule
   field
     isBraided : IsBraided X bracketOp
     symmetricCondition : (g₁ g₂ : ⟨ G₀ X ⟩) → (((bracketOp g₁ g₂) ·⟨ G₁ X ⟩ (bracketOp g₁ g₂)) ≡ unit (G₁ X)) 




--Morphism Between Two Braided Crossed Modules

 record BraidedMorphism : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇ where
   open CrossedModule
   open CrossedModuleMorphism
   field
     X : CrossedModule {𝓤} {𝓥}
     Y : CrossedModule {𝓦} {𝓣}
     σ×θ : CrossedModuleMorphism X Y
     bracketOp : ⟨ G₀ X ⟩ → ⟨ G₀ X ⟩ → ⟨ G₁ X ⟩
     bracketOp' : ⟨ G₀ Y ⟩ → ⟨ G₀ Y ⟩ → ⟨ G₁ Y ⟩
     XisBraided : IsBraided X bracketOp
     YisBraided : IsBraided Y bracketOp'
     preservesBraiding : (g₁ g₂ : ⟨ G₀ X ⟩) → ((θ σ×θ) (bracketOp g₁ g₂) ≡ bracketOp' ((σ σ×θ) g₁) ((σ σ×θ) g₂))
     
-}
