module divisible where

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Function
open import Function.Equivalence using (equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary.Definitions hiding (Decidable)
--open import Relation.Binary.Reasoning.StrictPartialOrder
open import Relation.Unary using (Decidable)
import Relation.Nullary.Decidable as Dec

open import divRem


private variable
  d k l m n o p : ℕ

------main definition (multiplicative)

data _∣_ : ℕ → ℕ → Set where

   m∣k*m : ∀ (k : ℕ) →  m ∣ (k * m)


------alternative definition (additive)

data _∣'_ : ℕ → ℕ → Set where

  --o∣'n :  1 ∣' n

  m∣'z   : m ∣' 0

  m∣'m+n :  m ∣' n → m ∣' (m + n)
  

------both definitions are equivalent

∣→∣' : m ∣ n → m ∣' n
∣→∣' (m∣k*m zero) = m∣'z
∣→∣' (m∣k*m (suc k)) = m∣'m+n (∣→∣' (m∣k*m k))

∣'→∣ : (m ∣' n) → (m ∣ n)
∣'→∣ m∣'z = m∣k*m zero
∣'→∣ (m∣'m+n e) with ∣'→∣ e
... | (m∣k*m k) = m∣k*m (suc k)

------some properties

z∤'s : ¬ (zero ∣' suc m)
z∤'s (m∣'m+n x) = z∤'s x

z∤s : ¬ (zero ∣ suc m)
z∤s e = z∤'s (∣→∣' e)

-- o∣'m : 1 ∣' m
-- o∣'m {zero} = m∣'z
-- o∣'m {suc m} = m∣'m+n o∣'m

o∣m : 1 ∣ m
o∣m {m} = subst (1 ∣_) (*-identityʳ m) (m∣k*m m)

-- m∣'m : m ∣' m
-- m∣'m {m} = subst (m ∣'_) (+-identityʳ m) (m∣'m+n {m} {0} m∣'z)

m∣m : m ∣ m
m∣m {m} = subst (m ∣_) (*-identityˡ m) (m∣k*m 1)


m∣'n+m : m ∣' n → m ∣' (n + m)
m∣'n+m {m} {n} m∣'n = subst (m ∣'_) (+-comm m n) (m∣'m+n m∣'n)

m∣m*k : ∀ (k : ℕ) → m ∣ (m * k)
m∣m*k {m} k = subst (m ∣_) (*-comm k m) (m∣k*m k)


-- m≤n→m∣'n∸m : m ∣' n → m ≤ n → m ∣' (n ∸ m)
-- m≤n→m∣'n∸m m∣'z z≤n = m∣'z
-- --m≤n→m∣'n∸m (m∣'m+n {m} {n} m∣'n) _ rewrite m+n∸m≡n m n = m∣'n
-- m≤n→m∣'n∸m (m∣'m+n {m} {n} m∣'n) _ = subst (m ∣'_) (sym (m+n∸m≡n m n)) m∣'n

m∣'n∸m : m ∣' n → m ∣' (n ∸ m)
m∣'n∸m {m = zero} m∣'z = m∣'z
m∣'n∸m {m = suc m} m∣'z = m∣'z
--m∣'n∸m (m∣'m+n {m} {n} m∣'n) rewrite m+n∸m≡n m n = m∣'n
m∣'n∸m (m∣'m+n {m} {n} m∣'n) = subst (m ∣'_) (sym (m+n∸m≡n m n)) m∣'n

-- A⊎B→¬A→B : {A B : Set} → A ⊎ B → ¬ A → B
-- A⊎B→¬A→B (inj₁ a) ¬a = ⊥-elim (¬a a)
-- A⊎B→¬A→B (inj₂ b) _  = b

∣'→≤ : m ∣' n → n ≡ 0 ⊎ m ≤ n
∣'→≤ m∣'z = inj₁ refl
∣'→≤ (m∣'m+n {m} {n} e) = inj₂ (m≤m+n m n)

∣'→≤' : k ≡ suc n → m ∣' k  → m ≤ k
∣'→≤' e (m∣'m+n e') = m≤m+n _ _

∣'→≤'' : m ∣' (suc n) → m ≤ (suc n)
∣'→≤'' e = ∣'→≤' refl e


∣→≤ : m ∣ n → n ≡ 0 ⊎ m ≤ n
∣→≤ (m∣k*m zero) = inj₁ refl
∣→≤ (m∣k*m {m} (suc k)) = inj₂ (m≤m+n m (k * m))

-- ∣→≤' : (n ≡ suc _) → m ∣ n → m ≤ n
-- ∣→≤' {n} {m} e (m∣k*m {m} k) = m≤n*m m {k} {!s≤s!}

-- ∣→≤'' : m ∣ (suc n) → m ≤ (suc n)
-- ∣→≤'' e = ∣→≤' refl e

-- ∣→≤''' : (n ≢ 0) → m ∣ n → m ≤ n
-- ∣→≤'''  n≢0 m∣n = {!!}


∣-trans : m ∣ n → n ∣ o → m ∣ o
∣-trans (m∣k*m {m} k) (m∣k*m l) rewrite sym(*-assoc l k m) = m∣k*m (l * k)

∣'-trans : m ∣' n → n ∣' o → m ∣' o
∣'-trans e e'  = ∣→∣' (∣-trans (∣'→∣ e) (∣'→∣ e'))


------- decidable _∣'_

{-# TERMINATING #-}

_∣'?_ : (m n : ℕ) → Dec (m ∣' n)
m ∣'? zero = yes m∣'z
m ∣'? n@(suc _) = case m ≤? n of λ {
  (no m≰n)  → no λ m∣'n → m≰n (∣'→≤'' m∣'n) ;
  (yes m≤n) → case m ∣'? (n ∸ m) of λ {
                   (no m∤'n∸m)  → no λ m∣'n → m∤'n∸m (m∣'n∸m m∣'n) ;
                   (yes m∣'n∸m) → yes (subst (m ∣'_) (m+[n∸m]≡n {m} {n} m≤n) (m∣'m+n m∣'n∸m))} }



∣→r≡0 : (e : m ≢ 0) → m ∣ n → proj₁ (proj₁ (proj₂ (divRemUnique' m n e))) ≡ 0
∣→r≡0 {m} {n} m≢0 (m∣k*m k) with divRemUnique' m n m≢0
... | q , (r , (r<m , eq) , uniqueR) , uniqueQ = let 0<m = ≤∧≢⇒< z≤n (λ 0≡m → m≢0 (sym 0≡m))
    in uniqueR {0} ( 0<m
  , (cong (_* m) (sym (uniqueQ {k} (0 , ((0<m , refl)
  , (λ {r'} (r'<m , eq') → +-cancelʳ-≡ _ _ eq')))))))

r≡0→∣ : (e : m ≢ 0) → proj₁ (proj₁ (proj₂ (divRemUnique' m n e))) ≡ 0 → m ∣ n
r≡0→∣ {m} {n}  m≢0 r≡0 with (divRemUnique' m n m≢0)
... | q , (r , (r<m , eq) , uniqueR) , uniqueQ = subst (m ∣_) (sym(trans eq (cong (_+ q * m) r≡0))) (m∣k*m q)


_∣?_ : (m n : ℕ) → Dec(m ∣ n)
zero ∣? zero = yes (m∣k*m 0)
zero ∣? suc n = no z∤s
m@(suc _) ∣? n = Dec.map (equivalence (r≡0→∣ 1+n≢0) (∣→r≡0 1+n≢0) ) (_ ≟ _) 
