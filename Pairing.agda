module Pairing where

open import Agda.Primitive

private variable
  a b c : Level
  A B C : Set a

infix  4 _≡_
infixl 8 _+_

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data _×_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _,_ : A → B → A × B

{-# TERMINATING #-}
π' : ℕ → ℕ → ℕ
π' n (s m) = s (π' (s n) m)
π' z     z = z
π' (s n) z = s (π' z n)

π : ℕ × ℕ → ℕ
π (n , m) = π' n m

unπ' : ℕ → ℕ × ℕ → ℕ × ℕ
unπ' z     (n , m)   = n , m
unπ' (s i) (z , n)   = unπ' i (s n , z)
unπ' (s i) (s n , m) = unπ' i (n , s m)

unπ : ℕ → ℕ × ℕ
unπ i = unπ' i (z , z)

data _≡_ {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {x y : A} {z w : B} → (f : A → B → C) → x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

{-# BUILTIN EQUALITY _≡_ #-}

_+_ : ℕ → ℕ → ℕ
z   + m = m
s n + m = s (n + m)

+z : ∀ n → n + z ≡ n
+z z     = refl
+z (s n) rewrite +z n = refl 

+s : ∀ n m → n + s m ≡ s (n + m)
+s z m     = refl
+s (s n) m rewrite +s n m = refl

data ⊥ : Set where

znots : ∀ {n} → z ≡ s n → ⊥
znots ()

⊥-elim : ⊥ → A
⊥-elim ()

ret' : ∀ i n m → π (unπ' i (n , m)) ≡ i + π (n , m)
ret' z     n     m = refl
ret' (s i) z     m rewrite ret' i (s m) z = +s _ _
ret' (s i) (s n) m rewrite ret' i n (s m) = +s _ _

s-inj : ∀ {n m} → s n ≡ s m → n ≡ m
s-inj refl = refl

{-# TERMINATING #-}
inj-l : ∀ n k m l → π' n k ≡ π' m l → n ≡ m
{-# TERMINATING #-}
inj-r : ∀ n k m l → π' n k ≡ π' m l → k ≡ l

inj-l n     (s k) m     (s l) e = s-inj (inj-l _ _ _ _ (s-inj e))
inj-l n     (s k) (s m) z     e = ⊥-elim (znots (sym (inj-l _ _ _ _ (s-inj e))))
inj-l z     z     z     z     e = refl
inj-l (s n) z     m     (s l) e = ⊥-elim (znots (inj-l _ _ _ _ (s-inj e)))
inj-l (s n) z     (s m) z     e = cong s (inj-r _ _ _ _ (s-inj e))

inj-r n     (s k) m     (s l) e = cong s (inj-r _ _ _ _ (s-inj e))
inj-r n     (s k) (s m) z     e = ⊥-elim (znots (sym (inj-l _ _ _ _ (s-inj e))))
inj-r z     z     z     z     e = refl
inj-r (s n) z     m     (s l) e = ⊥-elim (znots (inj-l _ _ _ _ (s-inj e)))
inj-r (s n) z     (s m) z     e = refl

inj : ∀ p q → π p ≡ π q → p ≡ q
inj (_ , _) (_ , _) e = cong₂ _,_ (inj-l _ _ _ _ e) (inj-r _ _ _ _ e)

-- π is a bijection :)
ret : ∀ i → π (unπ i) ≡ i
ret i = trans (ret' i z z) (+z _)

sec : ∀ p → unπ (π p) ≡ p
sec p = inj (unπ (π p)) p (ret (π p))
