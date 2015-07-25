module CoPL.Nat where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

module DerivingSystem-Nat where
  data _plus_is_ : Nat → Nat → Nat → Set where
    P-ZERO : (n : Nat) → 0 plus n is n
    P-SUCC : (n₁ n₂ n₃ : Nat) → n₁ plus n₂ is n₃ → S n₁ plus n₂ is S n₃
  data _times_is_ : Nat → Nat → Nat → Set where
    T-ZERO : (n : Nat) → 0 times n is 0
    T-SUCC : (n₁ n₂ n₃ n₄ : Nat) → n₁ times n₂ is n₃ → n₂ plus n₃ is n₄ → S n₁ times n₂ is n₄

module DerivingSystem-CompareNat1 where
  data _is-less-than_ : Nat → Nat → Set where
    L-SUCC : (n : Nat) → n is-less-than S n
    L-TRANS : (n₁ n₂ n₃ : Nat) → n₁ is-less-than n₂ → n₂ is-less-than n₃ → n₁ is-less-than n₃

module DerivingSystem-CompareNat2 where
  data _is-less-than_ : Nat → Nat → Set where
    L-ZERO : (n : Nat) → Z is-less-than S n
    L-SUCCSUCC : (n₁ n₂ : Nat) → n₁ is-less-than n₂ → S n₁ is-less-than S n₂

module DerivingSystem-CompareNat3 where
  data _is-less-than_ : Nat → Nat → Set where
    L-SUCC : (n : Nat) → n is-less-than S n
    L-SUCCR : (n₁ n₂ : Nat) → n₁ is-less-than n₂ → n₁ is-less-than S n₂

data Exp : Set where
  E : (n : Nat) → Exp
  _+_ : (e₁ e₂ : Exp) → Exp
  _*_ : (e₁ e₂ : Exp) → Exp
infixl 6 _+_
infixl 7 _*_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}
infix 4 _≡_

module DerivingSystem-EvalNatExp where
  open DerivingSystem-Nat
  data _↓_ : Exp → Nat → Set where
    E-CONST : (n : Nat) → E n ↓ n
    E-PLUS : (e₁ e₂ : Exp) → (n₁ n₂ n : Nat) → e₁ ↓ n₁ → e₂ ↓ n₂ → n₁ plus n₂ is n → e₁ + e₂ ↓ n
    E-TIMES : (e₁ e₂ : Exp) → (n₁ n₂ n : Nat) → e₁ ↓ n₁ → e₂ ↓ n₂ → n₁ times n₂ is n → e₁ * e₂ ↓ n
  infix 5 _↓_

module DerivingSystem-ReduceNatExp where
  open DerivingSystem-Nat
  data _⟶_ : Exp → Exp → Set where
    R-PLUS : (n₁ n₂ n₃ : Nat) → n₁ plus n₂ is n₃ → E n₁ + E n₂ ⟶ E n₃
    R-TIMES : (n₁ n₂ n₃ : Nat) → n₁ times n₂ is n₃ → E n₁ * E n₂ ⟶ E n₃
    R-PLUSL : (e₁ e₁' e₂ : Exp) → e₁ ⟶ e₁' → e₁ + e₂ ⟶ e₁' + e₂
    R-PLUSR : (e₁ e₂ e₂' : Exp) → e₂ ⟶ e₂' → e₁ + e₂ ⟶ e₁ + e₂'
    R-TIMESL : (e₁ e₁' e₂ : Exp) → e₁ ⟶ e₁' → e₁ * e₂ ⟶ e₁' * e₂
    R-TIMESR : (e₁ e₂ e₂' : Exp) → e₂ ⟶ e₂' → e₁ * e₂ ⟶ e₁ * e₂'
  infix 5 _⟶_

  data _⟶*_ : Exp → Exp → Set where
    MR-ZERO : (e : Exp) → e ⟶* e
    MR-ONE : (e e' : Exp) → e ⟶* e'
    MR-MULTI : (e e' e'' : Exp) → e ⟶* e' → e' ⟶* e'' → e ⟶* e''
  infix 5 _⟶*_

  data _⟶d_ : Exp → Exp → Set where
    R-PLUS : (n₁ n₂ n₃ : Nat) → n₁ plus n₂ is n₃ → E n₁ + E n₂ ⟶d E n₃
    R-TIMES : (n₁ n₂ n₃ : Nat) → n₁ times n₂ is n₃ → E n₁ * E n₂ ⟶d E n₃
    R-PLUSL : (e₁ e₁' e₂ : Exp) → e₁ ⟶d e₁' → e₁ + e₂ ⟶d e₁' + e₂
    R-PLUSR : (n : Nat) → (e₂ e₂' : Exp) → e₂ ⟶d e₂' → E n + e₂ ⟶d E n + e₂'
    R-TIMESL : (e₁ e₁' e₂ : Exp) → e₁ ⟶d e₁' → e₁ * e₂ ⟶d e₁' * e₂
    R-TIMESR : (n : Nat) → (e₂ e₂' : Exp) → e₂ ⟶d e₂' → E n * e₂ ⟶d E n * e₂'
  infix 5 _⟶d_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public
infixr 4 _,_

Σ-syntax : ∀ (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : {A : Set} → (A → Set) → Set
∃ = Σ _

_×_ : (A : Set) (B : Set) → Set
A × B = Σ[ x ∈ A ] B
infixr 2 _×_

module Properties where
  open DerivingSystem-Nat
  -- 定理 2.1 (1)
  zero-plus : (n : Nat) → Z plus n is n
  zero-plus = P-ZERO
  -- 定理 2.1 (2)
  plus-zero : (n : Nat) → n plus Z is n
  plus-zero Z = P-ZERO Z
  plus-zero (S n) = P-SUCC n Z n (plus-zero n)
  -- 定理 2.2
  plus-uniq : {n₁ n₂ n₃ n₄ : Nat} → n₁ plus n₂ is n₃ → n₁ plus n₂ is n₄ → n₃ ≡ n₄
  plus-uniq (P-ZERO n₂) (P-ZERO .n₂) = refl
  plus-uniq (P-SUCC n₁ n₂ n₃ n₁+n₂=n₃) (P-SUCC .n₁ .n₂ n₄ n₁+n₂=n₄)
    rewrite plus-uniq n₁+n₂=n₃ n₁+n₂=n₄
          = refl
  -- 定理 2.3
  plus-closure : (n₁ n₂ : Nat) → ∃ λ n₃ → n₁ plus n₂ is n₃
  plus-closure Z n₂ = n₂ , P-ZERO n₂
  plus-closure (S n₁) n₂ with plus-closure n₁ n₂
  plus-closure (S n₁) n₂ | proj₁ , proj₂ = S proj₁ , P-SUCC n₁ n₂ proj₁ proj₂
  -- 定理 2.4
  plus-comm : {n₁ n₂ n₃ : Nat} → n₁ plus n₂ is n₃ → n₂ plus n₁ is n₃
  plus-comm (P-ZERO n₂) = plus-zero n₂
  plus-comm (P-SUCC n₁ n₂ n₃ n₁+n₂=n₃) with plus-comm n₁+n₂=n₃
  plus-comm (P-SUCC n₁ .0 .n₁ n₁+n₂=n₃) | P-ZERO .n₁ = P-ZERO (S n₁)
  plus-comm (P-SUCC n₁ .(S n₂) .(S n₃) n₁+n₂=n₃) | P-SUCC n₂ .n₁ n₃ n₂+n₁=n₃ = P-SUCC n₂ (S n₁) (S n₃) (plus-comm (P-SUCC n₁ n₂ n₃ (plus-comm n₂+n₁=n₃)))
  -- 定理 2.5
  plus-assoc : {n₁ n₂ n₃ n₄ n₅ : Nat} → n₁ plus n₂ is n₄ → n₄ plus n₃ is n₅ → ∃ λ n₆ → n₂ plus n₃ is n₆ × n₁ plus n₆ is n₅
  plus-assoc {n₅ = n₅} (P-ZERO n₂) n₄+n₃=n₅ = n₅ , n₄+n₃=n₅ , P-ZERO n₅
  plus-assoc (P-SUCC n₁ n₂ n₄ n₁+n₂=n₄) (P-SUCC .n₄ n₃ n₅ n₄+n₃=n₅) with plus-assoc n₁+n₂=n₄ n₄+n₃=n₅
  plus-assoc (P-SUCC n₁ n₂ n₄ n₁+n₂=n₄) (P-SUCC .n₄ n₃ n₅ n₄+n₃=n₅) | proj₁ , proj₂ , proj₃ = proj₁ , proj₂ , P-SUCC n₁ proj₁ n₅ proj₃
  -- 定理 2.6
  times-uniq : {n₁ n₂ n₃ n₄ : Nat} → n₁ times n₂ is n₃ → n₁ times n₂ is n₄ → n₃ ≡ n₄
  times-uniq (T-ZERO n₂) (T-ZERO .n₂) = refl
  times-uniq (T-SUCC n₁ n₂ n₅ n₃ n₁*n₂=n₃ x) (T-SUCC .n₁ .n₂ n₆ n₄ n₁*n₂=n₄ x₁)
    rewrite times-uniq n₁*n₂=n₃ n₁*n₂=n₄
          | plus-uniq x x₁
          = refl
  -- 定理 2.7
  times-closure : (n₁ n₂ : Nat) → ∃ λ n₃ → n₁ times n₂ is n₃
  times-closure Z n₂ = Z , T-ZERO n₂
  times-closure (S n₁) n₂ with times-closure n₁ n₂
  times-closure (S n₁) n₂ | proj₁ , proj₂ with plus-closure n₂ proj₁
  times-closure (S n₁) n₂ | proj₁ , proj₄ | proj₂ , proj₃ = proj₂ , T-SUCC n₁ n₂ proj₁ proj₂ proj₄ proj₃
  -- 定理 2.8 (1)
  0*n=0 : (n : Nat) → Z times n is Z
  0*n=0 = T-ZERO
  -- 定理 2.8 (2)
  n*0=0 : (n : Nat) → n times Z is Z
  n*0=0 Z = T-ZERO Z
  n*0=0 (S n) = T-SUCC n Z 0 Z (n*0=0 n) (P-ZERO Z)
  -- 定理 2.9
  times-comm : {n₁ n₂ n₃ : Nat} → n₁ times n₂ is n₃ → n₂ times n₁ is n₃
  times-comm (T-ZERO n₂) = n*0=0 n₂
  times-comm (T-SUCC n₁ .0 n₃ .n₃ x (P-ZERO .n₃))
    rewrite times-uniq x (n*0=0 n₁)
          = T-ZERO (S n₁)
  times-comm (T-SUCC n₁ .(S n₂) n₄ .(S n₃) x (P-SUCC n₂ .n₄ n₃ x₁)) with times-comm x
  times-comm (T-SUCC n₁ .(S n₂) n₄ .(S n₅) n₁*Sn₂=n₄ (P-SUCC n₂ .n₄ n₅ n₂+n₄=n₅)) | T-SUCC .n₂ .n₁ n₃ .n₄ n₂*n₁=n₃ n₁+n₃=n₄ = Sn₂+Sn₁=Sn₅ where
    n₁*n₂=n₃ = times-comm n₂*n₁=n₃
    n₄+n₂=n₅ = plus-comm n₂+n₄=n₅
    n₃+n₁=n₄ = plus-comm n₁+n₃=n₄
    n₆×n₁+n₂=n₆×n₃+n₆=n₅ = plus-assoc n₃+n₁=n₄ n₄+n₂=n₅
    n₆ = proj₁ n₆×n₁+n₂=n₆×n₃+n₆=n₅
    n₁+n₂=n₆ = proj₁ (proj₂ n₆×n₁+n₂=n₆×n₃+n₆=n₅)
    n₃+n₆=n₅ = proj₂ (proj₂ n₆×n₁+n₂=n₆×n₃+n₆=n₅)
    n₂+n₁=n₆ = plus-comm n₁+n₂=n₆
    n₆+n₃=n₅ = plus-comm n₃+n₆=n₅
    n₇×n₂+n₃=n₇×n₁+n₇=n₅ = plus-assoc n₁+n₂=n₆ n₆+n₃=n₅
    n₇ = proj₁ n₇×n₂+n₃=n₇×n₁+n₇=n₅
    n₂+n₃=n₇ = proj₁ (proj₂ n₇×n₂+n₃=n₇×n₁+n₇=n₅)
    n₁+n₇=n₅ = proj₂ (proj₂ n₇×n₂+n₃=n₇×n₁+n₇=n₅)
    Sn₁*n₂=n₇ = T-SUCC _ _ _ _ n₁*n₂=n₃ n₂+n₃=n₇
    n₂*Sn₁=n₇ = times-comm Sn₁*n₂=n₇
    Sn₁+n₇=Sn₅ = P-SUCC n₁ n₇ n₅ n₁+n₇=n₅
    Sn₂+Sn₁=Sn₅ = T-SUCC _ _ _ _ n₂*Sn₁=n₇ Sn₁+n₇=Sn₅
