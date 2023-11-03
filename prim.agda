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

irreducible : ℕ → Set
irreducible n = ∀ {m : ℕ} → m ∣ n → m ≡ 1 ⊎ m ≡ n

prime : ℕ → Set
prime n = (n ≢ 0) × ( n ≢ 1 ) × ( irreducible n )


------list of divisors

p>1 : prime p → p > 1
p>1 {zero}    (p≢0 , p≢1 , irred) = ⊥-elim (p≢0 refl)
p>1 {(suc 0)} (p≢0 , p≢1 , irred) = ⊥-elim (p≢1 refl)
p>1 {p@(suc (suc _))} prime       = s≤s (s≤s z≤n)

sorted? : List ℕ → Set
sorted? l = AllPairs.AllPairs _<_ l

upTo-sorted : ∀ n → sorted? (upTo n)
upTo-sorted n = applyUpTo⁺₁ id n λ i<j j<n → i<j

x∉[] : {A : Set} → {x : A} → x ∉ []
x∉[] = λ ()

x∉[y] : {x y : ℕ} → x ≢ y → x ∉ y ∷ []
x∉[y] x≢y = λ { (here x≡y) → ⊥-elim (x≢y x≡y)}

x≢y∉[z] : {x y z : ℕ} → (l : List ℕ) → (e : l ≡ z ∷ []) → x ≢ y → ¬ (x ∈ l × y ∈ l)
x≢y∉[z] (z ∷ []) e x≢y = λ { (here x≡z , here y≡z) → x≢y (trans x≡z (sym y≡z))}

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
                                  ; complete₂ = λ k k∣n → ∈-filter⁺ (_∣? n) {xs = upTo (suc n)} (∈-upTo⁺ (s≤s (A⊎B⇒¬A⇒B (∣⇒≤ k∣n) 1+n≢0))) k∣n
                                  ; sorted = filter⁺ (_∣? n) (upTo-sorted (suc n))}

-- x<tail→x≡head : (x y : ℕ) → (xs : List ℕ) → sorted? (y ∷ xs) → x ∈ (y ∷ xs) → All.All (x <_) xs → x ≡ y
-- x<tail→x≡head x y xs s (here px) x<tail = px
-- x<tail→x≡head x y xs s (there x∈l) x<tail = {!!}

-- sorted→samelist : ∀ (a b : List ℕ) → All.All (_∈ b) a × All.All (_∈ a) b → (sorted? a × sorted? b) → a ≡ b 
-- sorted→samelist [] [] (a⊂b , b⊂a) (sa , sb) = refl
-- sorted→samelist [] (x ∷ b) (a⊂b , b⊂a) (sa , sb) = ⊥-elim (x∉[] (All.head b⊂a))
-- sorted→samelist (x ∷ a) [] (a⊂b , b⊂a) (sa , sb) = ⊥-elim (x∉[] (All.head a⊂b))
-- sorted→samelist (x ∷ a) (y ∷ b) (a⊂b , b⊂a) (sa , sb) = let x≡y = {!!}
--   in {!!}

-- unique-divList : ∀ n → (a b : divList n) → list a ≡ list b
-- unique-divList n record { list = list-a ; complete₁ = complete₁-a ; complete₂ = complete₂-a ; sorted = sorted-a } record { list = list-b ; complete₁ = complete₁-b ; complete₂ = complete₂-b ; sorted = sorted-b}
--   = sorted→samelist list-a list-b ( All.tabulate (λ {k} k∈l-a → complete₂-b k (complete₁-a k k∈l-a))
--                                   , All.tabulate (λ {k} k∈l-b → complete₂-a k (complete₁-b k k∈l-b))) (sorted-a , sorted-b)


at-least-2-divs : ∀ n → n ≢ 1 → (ds : divList n) → length (list ds) ≥ 2
at-least-2-divs n n≢1 record { list = [] ; complete₂ = complete₂ } = ⊥-elim (x∉[] (complete₂ 1 o∣m))
at-least-2-divs n n≢1 record { list = (z ∷ []) ; complete₂ = complete₂ } = ⊥-elim (x≢y∉[z] {z = z} (z ∷ []) refl n≢1 ((complete₂ n m∣m) , (complete₂ 1 o∣m)))
at-least-2-divs n n≢1 record { list = (x ∷ x₁ ∷ list₁) } = s≤s (s≤s z≤n)


lemma : ∀ p → ∀ k → k ∈ 1 ∷ p ∷ [] → k ≡ 1 ⊎ k ≡ p
lemma p k (here k≡1) = inj₁ k≡1
lemma p k (there (here k≡p)) = inj₂ k≡p

2divs→prime : ∀ (p : ℕ) → (p≢0 : p ≢ 0) → list(mk-divList p p≢0) ≡ 1 ∷ p ∷ [] → prime p
2divs→prime zero p≢0 e             = ⊥-elim (p≢0 refl)
2divs→prime 1 p≢0 ()
2divs→prime p@(suc (suc _)) p≢0 e  = let helper = λ k (k∣p : k ∣ p) → subst (k ∈_) e (complete₂(mk-divList p p≢0) k k∣p)
               in p≢0 , (λ p≡1 → 1+n≢0 (suc-injective p≡1)) , λ {k} k∣p → lemma p k (helper k k∣p)

divisor→sublist : ∀ (n d k : ℕ) → (n≢0 : n ≢ 0) → (d≢0 : d ≢ 0) → d ∣ n → k ∈ list(mk-divList d d≢0) → k ∈ list(mk-divList n n≢0)
divisor→sublist n d k n≢0 d≢0 d∣n k∈ = complete₂(mk-divList n n≢0) k (∣-trans (complete₁(mk-divList d d≢0) k k∈) d∣n)

2-prime : prime 2
2-prime = 2divs→prime 2 (λ ()) refl


∃-prime-divisor : ∀ (n : ℕ) → n ≢ 1 → ∃[ p ] p ∣ n × prime p
∃-prime-divisor zero n≢1 = 2 , ((m∣k*m zero) , 2-prime)
∃-prime-divisor (suc zero) n≢1 = ⊥-elim (n≢1 refl)
∃-prime-divisor n@(suc (suc _)) n≢1 with mk-divList n 1+n≢0
... | record { list = [] ; complete₂ = complete₂ } = ⊥-elim ( x∉[] (complete₂ 1 o∣m))
... | record { list = z ∷ [] ; complete₂ = complete₂ } = ⊥-elim (x≢y∉[z] {z = z} (z ∷ []) refl n≢1 ((complete₂ n m∣m) , (complete₂ 1 o∣m)))
... | record { list = zero ∷ y ∷ list ; complete₁ = complete₁ } = ⊥-elim (z∤s (complete₁ 0 (here refl)))
... | record { list = suc zero ∷ y ∷ list ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted }
 = let y∣n = complete₁ y (there (here refl))
       y>1 = All.head (AllPairs.head sorted)
       y≢0 = >⇒≢ (<-trans (s≤s z≤n) y>1)
       y≢1 = >⇒≢ y>1
       y<rest = AllPairs.head (AllPairs.tail sorted)
       m≤y = λ {m} (m∣y : m ∣ y) → A⊎B⇒¬A⇒B (∣⇒≤ m∣y) y≢0
       m∈list = λ {m} (m∣y : m ∣ y) → complete₂ m (∣-trans m∣y y∣n)
   in y , (y∣n , ( y≢0 , y≢1
  , λ {m} m∣y → case m∈list m∣y of λ { (here m≡1) → inj₁ m≡1 ; (there (here m≡y)) → inj₂ m≡y ; (there (there m∈rest)) → ⊥-elim {!!}}))
... | record { list = suc (suc _) ∷ y ∷ list ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted } = ⊥-elim {!!}


fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = (suc n) * fac n

fac≢0 : ∀ n → fac n ≢ 0
fac≢0 zero = λ ()
fac≢0 (suc n) = {!!}

k∣facn : ∀ k → k ≢ 0 → ∀ n → k ≤ n → k ∣ fac n
k∣facn zero k≢0 n k≤n = ⊥-elim (k≢0 refl)
k∣facn  k@(suc _) k≢0 n k≤n = helper n (≤⇒≤′ k≤n)
  where helper : ∀ n → k ≤′ n → k ∣ fac n
        helper n ≤′-refl = m∣m*k _
        helper n@(suc n₁) (≤′-step e) = ∣-trans (helper n₁ e) (m∣k*m (suc n₁))


infprim : ∀ (n : ℕ) → ∃[ p ] n ≤ p × prime p
infprim n = let N = suc (fac n)
                N≢1 = λ N≡1 → fac≢0 n (suc-injective N≡1)
                p , (p∣N , primep) = ∃-prime-divisor N N≢1
                p≢0 = proj₁ primep
  in case p <? n of λ
  { (no p≮n)  → p , ((≮⇒≥ p≮n) , primep)
  ; (yes p<n) → ⊥-elim (m∣n⇒m∤1+n (p>1 primep) (k∣facn p p≢0 n (<⇒≤ p<n)) p∣N) }
