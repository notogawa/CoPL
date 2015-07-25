module CoPL.Chapter1 where

open import CoPL.Nat

module Practice-1-1 where

module Practice-1-2 where
  open DerivingSystem-Nat
  practice-1-2-1 : 3 plus 1 is 4
  practice-1-2-1 = P-SUCC 2 1 3 (P-SUCC 1 1 2 (P-SUCC 0 1 1 (P-ZERO 1)))
  practice-1-2-2 : 1 plus 3 is 4
  practice-1-2-2 = P-SUCC 0 3 3 (P-ZERO 3)
  practice-1-2-3 : 3 times 0 is 0
  practice-1-2-3 = T-SUCC 2 0 0 0 (T-SUCC 1 0 0 0 (T-SUCC 0 0 0 0 (T-ZERO 0) (P-ZERO 0)) (P-ZERO 0)) (P-ZERO 0)

module Practice-1-3 where

module Practice-1-4 where

module Practice-1-5 where
  module Case1 where
    open DerivingSystem-CompareNat1
    practice-1-5-1 : 0 is-less-than 2
    practice-1-5-1 = L-TRANS 0 1 2 (L-SUCC 0) (L-SUCC 1)
    practice-1-5-2 : 2 is-less-than 4
    practice-1-5-2 = L-TRANS 2 3 4 (L-SUCC 2) (L-SUCC 3)
  module Case2 where
    open DerivingSystem-CompareNat2
    practice-1-5-1 : 0 is-less-than 2
    practice-1-5-1 = L-ZERO 1
    practice-1-5-2 : 2 is-less-than 4
    practice-1-5-2 = L-SUCCSUCC 1 3 (L-SUCCSUCC 0 2 (L-ZERO 1))
  module Case3 where
    open DerivingSystem-CompareNat3
    practice-1-5-1 : 0 is-less-than 2
    practice-1-5-1 = L-SUCCR 0 1 (L-SUCC 0)
    practice-1-5-2 : 2 is-less-than 4
    practice-1-5-2 = L-SUCCR 2 3 (L-SUCC 2)

module Practice-1-6 where

module Practice-1-7 where

module Practice-1-8 where
  open DerivingSystem-Nat
  open DerivingSystem-EvalNatExp
  practice-1-8-1 : E 0 + E 2 ↓ 2
  practice-1-8-1 = E-PLUS (E 0) (E 2) Z 2 2 (E-CONST 0)
                     (E-CONST 2) (P-ZERO 2)
  practice-1-8-2 : E 2 + E 0 ↓ S 1
  practice-1-8-2 = E-PLUS (E 2) (E 0) 2 0 2
                     (E-CONST 2) (E-CONST 0)
                     (P-SUCC 1 0 1 (P-SUCC 0 0 0 (P-ZERO 0)))
  practice-1-8-3 : E 1 + E 1 + E 1 ↓ S 2
  practice-1-8-3 = E-PLUS (E 1 + E 1) (E 1) 2 1 (S 2)
                     (E-PLUS (E 1) (E 1) 1 1 2 (E-CONST 1)
                      (E-CONST 1) (P-SUCC Z 1 1 (P-ZERO 1)))
                     (E-CONST 1)
                     (P-SUCC 1 1 2
                      (P-SUCC Z 1 1 (P-ZERO 1)))
  practice-1-8-4 : E (S 2) + E 2 * E 1 ↓ 5
  practice-1-8-4 = E-PLUS (E 3) (E 2 * E 1) 3
                     2 5 (E-CONST (S 2))
                     (E-TIMES (E 2) (E 1) 2 1 2
                      (E-CONST 2) (E-CONST 1)
                      (T-SUCC 1 1 1 2
                       (T-SUCC 0 1 0 1 (T-ZERO 1) (P-SUCC 0 0 0 (P-ZERO 0)))
                       (P-SUCC 0 1 1 (P-ZERO 1))))
                     (P-SUCC 2 2 4
                      (P-SUCC 1 2 3
                       (P-SUCC 0 2 2 (P-ZERO 2))))
  practice-1-8-5 : (E 2 + E 2) * E 0 ↓ 0
  practice-1-8-5 = E-TIMES (E 2 + E 2) (E 0) (4) 0 0
                     (E-PLUS (E 2) (E 2) 2 2
                      4 (E-CONST 2) (E-CONST 2)
                      (P-SUCC 1 2 3
                       (P-SUCC 0 2 2 (P-ZERO 2))))
                     (E-CONST 0)
                     (T-SUCC 3 0 0 0
                      (T-SUCC 2 0 0 0
                       (T-SUCC 1 0 0 0 (T-SUCC 0 0 0 0 (T-ZERO 0) (P-ZERO 0))
                        (P-ZERO 0))
                       (P-ZERO 0))
                      (P-ZERO 0))
  practice-1-8-6 : E 0 * (E 2 + E 2) ↓ 0
  practice-1-8-6 = E-TIMES (E 0) (E 2 + E 2) 0 4 0
                     (E-CONST 0)
                     (E-PLUS (E 2) (E 2) 2 2
                      (4) (E-CONST 2) (E-CONST 2)
                      (P-SUCC 1 2 3
                       (P-SUCC 0 2 2 (P-ZERO 2))))
                     (T-ZERO 4)

module Practice-1-9 where
  open DerivingSystem-Nat
  open DerivingSystem-ReduceNatExp
  practice-1-9-1 : E 0 + E 2 ⟶* E 2
  practice-1-9-1 = MR-ONE (E 0 + E 2) (E 2)
  practice-1-9-2 : E 1 * E 1 + E 1 * E 1  ⟶d E 1 + E 1 * E 1
  practice-1-9-2 = R-PLUSL (E 1 * E 1) (E 1) (E 1 * E 1)
                     (R-TIMES 1 1 1
                      (T-SUCC 0 1 0 1 (T-ZERO 1) (P-SUCC 0 0 0 (P-ZERO 0))))
  practice-1-9-3 : E 1 * E 1 + E 1 * E 1  ⟶  E 1 * E 1 + E 1
  practice-1-9-3 = R-PLUSR (E 1 * E 1) (E 1 * E 1) (E 1)
                     (R-TIMES 1 1 1
                      (T-SUCC 0 1 0 1 (T-ZERO 1) (P-SUCC 0 0 0 (P-ZERO 0))))
  practice-1-9-4 : E 1 * E 1 + E 1 * E 1  ⟶* E 2
  practice-1-9-4 = MR-ONE (E 1 * E 1 + E 1 * E 1) (E 2)

module Practice-1-10 where
  open DerivingSystem-Nat
  data _⟶d_ : Exp → Exp → Set where
    R-PLUS : (n₁ n₂ n₃ : Nat) → n₁ plus n₂ is n₃ → E n₁ + E n₂ ⟶d E n₃
    R-TIMES : (n₁ n₂ n₃ : Nat) → n₁ times n₂ is n₃ → E n₁ * E n₂ ⟶d E n₃
    R-PLUSL : (e₁ e₁' : Exp) → (n : Nat) → e₁ ⟶d e₁' → e₁ + E n ⟶d e₁' + E n
    R-PLUSR : (e₁ e₂ e₂' : Exp) → e₂ ⟶d e₂' → e₁ + e₂ ⟶d e₁ + e₂'
    R-TIMESL : (e₁ e₁' : Exp) → (n : Nat) → e₁ ⟶d e₁' → e₁ * E n ⟶d e₁' * E n
    R-TIMESR : (e₁ e₂ e₂' : Exp) → e₂ ⟶d e₂' → e₁ * e₂ ⟶d e₁ * e₂'
  infix 5 _⟶d_
  practice-1-10-1 : E 1 * E 1 + E 1 * E 1  ⟶d E 1 * E 1 + E 1
  practice-1-10-1 = R-PLUSR (E 1 * E 1) (E 1 * E 1) (E 1)
                      (R-TIMES 1 1 1
                       (T-SUCC 0 1 0 1 (T-ZERO 1) (P-SUCC 0 0 0 (P-ZERO 0))))
  practice-1-10-2 : E 1 * E 1 + E 1 ⟶d E 1 + E 1
  practice-1-10-2 = R-PLUSL (E 1 * E 1) (E 1) 1
                      (R-TIMES 1 1 1
                       (T-SUCC 0 1 0 1 (T-ZERO 1) (P-SUCC 0 0 0 (P-ZERO 0))))
