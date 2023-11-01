module prim where

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
import Data.List.Relation.Unary.AllPairs as AllPairs 
open import Data.List.Relation.Unary.AllPairs.Properties
import Data.List.Relation.Unary.All as All

open import divisible
open import divRem

postulate
  lem : ∀ {A : Set} → A ⊎ ¬ A

variable
  d k l m n o p : ℕ


-----prime numbers

prime_or_one : ℕ → Set
prime_or_one n = ∀ {m : ℕ} → m ∣ n → m ≡ 1 ⊎ m ≡ n

prime : ℕ → Set
prime n = ( n ≢ 1 ) × ( prime_or_one n )

-----idea : list_of_divisors
----- p prime iff lod has 2 elements
----- if d | n, then l(d) subset of l(n)
----- => min l(n)-{1} is prime-divisor of n


------------------

sorted? : List ℕ → Set
sorted? l = AllPairs.AllPairs _<_ l

upTo-sorted : ∀ n → sorted? (upTo n)
upTo-sorted n = applyUpTo⁺₁ id n λ i<j j<n → i<j

record divList (n : ℕ) : Set where
  field list      : List ℕ
        complete₁ : ∀ k → k ∈ list → k ∣ n
        complete₂ : ∀ k → k ∣ n → k ∈ list
        sorted    : sorted? list
open divList

mk-divList : ∀ n → n ≢ 0 → divList n
mk-divList zero n≢0 = ⊥-elim (n≢0 refl)
mk-divList n@(suc _) n≢0 = record { list =  filter (_∣? n) (upTo (suc n))
                              ; complete₁ = λ k k∈list → proj₂ (∈-filter⁻ (_∣? n) {xs = upTo(suc n)} k∈list)
                              ; complete₂ = λ k k∣n → ∈-filter⁺ (_∣? n) {xs = upTo (suc n)} (∈-upTo⁺ (s≤s ((A⊎B→¬A→B (∣→≤ k∣n) 1+n≢0)))) k∣n
                              ; sorted = filter⁺ (_∣? n) (upTo-sorted (suc n))}

x∉[] : {A : Set} → {x : A} → x ∉ []
x∉[] = λ ()

x∉[y] : {x y : ℕ} → x ≢ y → x ∉ y ∷ []
x∉[y] x≢y = λ { (here x≡y) → ⊥-elim (x≢y x≡y)}

x≢y∉[z] : {x y z : ℕ} → (l : List ℕ) → (e : l ≡ z ∷ []) → x ≢ y → ¬ (x ∈ l × y ∈ l)
x≢y∉[z] (z ∷ []) e x≢y = λ { (here x≡z , here y≡z) → x≢y (trans x≡z (sym y≡z))}

at-least-2-divs : ∀ n → (e : n ≢ 0) → n ≢ 1 → (ds : divList n) → length (list ds) ≥ 2
at-least-2-divs n n≢0 n≢1 record { list = [] ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted } = ⊥-elim (x∉[] (complete₂ 1 o∣m))
at-least-2-divs n n≢0 n≢1 record { list = (z ∷ []) ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted } = ⊥-elim (x≢y∉[z] {z = z} (z ∷ []) refl n≢1 ((complete₂ n m∣m) , (complete₂ 1 o∣m)))
at-least-2-divs n n≢0 n≢1 record { list = (x ∷ x₁ ∷ list₁) ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted } = s≤s (s≤s z≤n)


-- prime→2divs : ∀ (p : ℕ) → (p≢0 : p ≢ 0) → prime' p → list(mk-divList p p≢0) ≡ 1 ∷ p ∷ []
-- prime→2divs p p≢0 (p≢1 , primep) = {!!}

lemma : ∀ p → ∀ k → k ∈ 1 ∷ p ∷ [] → k ≡ 1 ⊎ k ≡ p
lemma p k (here k≡1) = inj₁ k≡1
lemma p k (there (here k≡p)) = inj₂ k≡p

2divs→prime : ∀ (p : ℕ) → (p≢0 : p ≢ 0) → list(mk-divList p p≢0) ≡ 1 ∷ p ∷ [] → prime p
2divs→prime zero p≢0 e             = ⊥-elim (p≢0 refl)
2divs→prime 1 p≢0 ()
2divs→prime p@(suc (suc _)) p≢0 e  = let helper = λ k (k∣p : k ∣ p) → subst (k ∈_) e (complete₂(mk-divList p p≢0) k k∣p)
               in ((λ p≡1 → 1+n≢0 (suc-injective p≡1))) , λ {k} k∣p → lemma p k (helper k k∣p)

divisor→sublist : ∀ (n d k : ℕ) → (n≢0 : n ≢ 0) → (d≢0 : d ≢ 0) → d ∣ n → k ∈ list(mk-divList d d≢0) → k ∈ list(mk-divList n n≢0)
divisor→sublist n d k n≢0 d≢0 d∣n k∈ = complete₂(mk-divList n n≢0) k (∣-trans (complete₁(mk-divList d d≢0) k k∈) d∣n)

2-prime : prime 2
2-prime = 2divs→prime 2 (λ ()) refl

myuncons : {A : Set} → (xs : List A) → (xs ≢ []) → (A × List A)
myuncons [] p = ⊥-elim (p refl)
myuncons (x ∷ xs) p = x , xs



∃-prime-divisor : ∀ (n : ℕ) → n ≢ 1 → ∃[ p ] p ∣ n × prime p
∃-prime-divisor zero n≢1 = 2 , ((m∣k*m zero) , 2-prime)
∃-prime-divisor (suc zero) n≢1 = ⊥-elim (n≢1 refl)
∃-prime-divisor n@(suc (suc n₁)) n≢1 with mk-divList n 1+n≢0
... | record { list = [] ; complete₁ = complete₁ ; complete₂ = complete₂ } = ⊥-elim ( x∉[] (complete₂ 1 o∣m))
... | record { list = z ∷ [] ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = _ } = ⊥-elim (x≢y∉[z] {z = z} (z ∷ []) refl n≢1 ((complete₂ n m∣m) , (complete₂ 1 o∣m)))
... | record { list = zero ∷ y ∷ list₁ ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = _ } = ⊥-elim (z∤s (complete₁ 0 (here refl)))
... | record { list = suc zero ∷ y ∷ list₁ ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted }
 = let y∣n = complete₁ y (there (here refl))
       y≢1 = >⇒≢ (All.head (AllPairs.head sorted))
       y<rest = {!λ {z} (z∈rest : z ∈ list₁) → ?!}
       m≤y = λ {m} (m∣y : m ∣ y) → A⊎B→¬A→B (∣→≤ m∣y) λ y≡0 → z∤s (subst (_∣ n) y≡0 y∣n)
   in y , (y∣n , (y≢1
  , λ m∣y → {!!}))
... | record { list = suc (suc x) ∷ y ∷ list₁ ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted } = ⊥-elim {!!}







-- infprim : ∀ (n : ℕ) → ∃[ p ] n ≤ p × prime p
-- infprim n = {!!}
