module CoPL.Nat where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

module DerivingSystem-Nat where
  data _plus_is_ : Nat → Nat → Nat → Set where
    P-ZERO : (n : Nat) → Z plus n is n
    P-SUCC : (n₁ n₂ n₃ : Nat) → n₁ plus n₂ is n₃ → S n₁ plus n₂ is S n₃
  data _times_is_ : Nat → Nat → Nat → Set where
    T-ZERO : (n : Nat) → Z times n is Z
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

-- 定義 1.5
data Exp : Set where
  E : (n : Nat) → Exp
  _+_ : (e₁ e₂ : Exp) → Exp
  _*_ : (e₁ e₂ : Exp) → Exp
infixl 6 _+_
infixl 7 _*_

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
