--------------------------------------------------------------------------------
Ettore Aldrovandi aldrovandi@math.fsu.edu
Keri D'Angelo kd349@cornell.edu

July 1, 2021
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --without-K --safe #-}


open import SpartanMLTT
open import Unit
open import Unit-Properties
open import UF-Subsingletons
open import Id
open import UF-Base
open import UF-Equiv
open import UF-Retracts
--open import Groups renaming (_≅_ to _≣_)
open import UF-SIP
open import UF-SIP-Examples

\end{code}

We define the trivial group (in the universe $𝓤$) giving the trivial
group structure to the one-point type in the universe.

\begin{code}

module Groups.triv {𝓤 : Universe} where

  open sip
  open monoid {𝓤}
  open group {𝓤}

  triv : Group
  triv = 𝟙 , (group-structure-t , group-axiom-t)
    where
      group-structure-t : group-structure  𝟙
      group-structure-t = ((λ x y → ⋆) , unit-t) , is-set-t , left-neutral-t , right-neutral-t , associative-t
        where
          unit-t : 𝟙
          unit-t = ⋆
          is-set-t : is-set 𝟙
          is-set-t = props-are-sets (𝟙-is-prop)
          left-neutral-t : left-neutral unit-t (λ x y → ⋆)
          left-neutral-t = λ { ⋆ → refl}
          right-neutral-t : right-neutral unit-t (λ x y → ⋆)
          right-neutral-t = λ { ⋆ → refl}
          associative-t : associative (λ x y → ⋆)
          associative-t = λ x y z → refl
      group-axiom-t : group-axiom 𝟙 (pr₁ group-structure-t)
      group-axiom-t = λ {x → ⋆ , refl , refl}

\end{code}


  The trivial group is initial and terminal in the obvious sense.

\begin{code}

  -- trivial group is initial

  triv-initial : (G : Group) → ⟨ triv ⟩ → ⟨ G ⟩
  triv-initial G = λ _ → e⟨ G ⟩

  triv-initial-is-hom : (G : Group ) → (is-homomorphism (triv ) G (triv-initial G))
  pr₁ (triv-initial-is-hom G) = {!!}
  pr₂ (triv-initial-is-hom G) = {!!}
  -- e⟨ G ⟩ ≡⟨ (unit-left G e⟨ G ⟩) ⁻¹ ⟩
  --                          e⟨ G ⟩ ·⟨ G ⟩  e⟨ G ⟩ ∎

\end{code}
  -- trivial group is terminal

  triv-terminal : (G : Group 𝓤) → (⟨ G ⟩ → ⟨ triv {𝓥} ⟩)
  triv-terminal G = unique-to-𝟙 

  triv-terminal-is-hom : (G : Group 𝓤) → (is-hom G (triv {𝓥}) (triv-terminal G))
  triv-terminal-is-hom G = refl


  If the underlying type of $G$ is contractible then $G$ is isomorphic
  to the trivial group. Note that it is not necessary to assume the
  center of contraction is the identity.


  group-is-singl-is-triv : (G : Group 𝓤) → is-singleton ⟨ G ⟩ → G ≣ (triv {𝓤})
  pr₁ (group-is-singl-is-triv G is) = triv-terminal G
  pr₁ (pr₁ (pr₂ (group-is-singl-is-triv G is))) = triv-initial G , λ { * → refl}
  pr₂ (pr₁ (pr₂ (group-is-singl-is-triv G is))) = (triv-initial G) , λ x → p ∙ (pr₂ is x)
    where
      c : ⟨ G ⟩
      c = pr₁ is
      p : e⟨ G ⟩ ≡ c
      p = (pr₂ is e⟨ G ⟩) ⁻¹
  pr₂ (pr₂ (group-is-singl-is-triv G is)) {x} {y} = triv-terminal-is-hom G {x} {y}

  group-is-singl-is-triv' : (G : Group 𝓤) → is-singleton ⟨ G ⟩ → (triv {𝓤}) ≣ G
  pr₁ (group-is-singl-is-triv' G is) = triv-initial G
  pr₁ (pr₁ (pr₂ (group-is-singl-is-triv' G is))) = (triv-terminal G) , λ x → p ∙ (pr₂ is x)
    where
      c : ⟨ G ⟩
      c = pr₁ is
      p : e⟨ G ⟩ ≡ c
      p = (pr₂ is e⟨ G ⟩) ⁻¹
  pr₂ (pr₁ (pr₂ (group-is-singl-is-triv' G is))) = (triv-terminal G) , (λ { * → refl})
  pr₂ (pr₂ (group-is-singl-is-triv' G is)) {x} {y} = triv-initial-is-hom G {x} {y}



