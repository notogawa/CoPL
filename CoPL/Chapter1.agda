module CoPL.Chapter1 where

open import CoPL.Nat

module Practice-1-1 where

module Practice-1-2 where
  open DerivingSystem-Nat
  practice-1-2-1 : S (S (S Z)) plus S Z is S (S (S (S Z)))
  practice-1-2-1 = P-SUCC (S (S Z)) (S Z) (S (S (S Z)))
                     (P-SUCC (S Z) (S Z) (S (S Z))
                      (P-SUCC Z (S Z) (S Z) (P-ZERO (S Z))))
  practice-1-2-2 : S Z plus S (S (S Z)) is S (S (S (S Z)))
  practice-1-2-2 = P-SUCC Z (S (S (S Z))) (S (S (S Z))) (P-ZERO (S (S (S Z))))
  practice-1-2-3 : S (S (S Z)) times Z is Z
  practice-1-2-3 = T-SUCC (S (S Z)) Z Z Z
                     (T-SUCC (S Z) Z Z Z (T-SUCC Z Z Z Z (T-ZERO Z) (P-ZERO Z))
                      (P-ZERO Z))
                     (P-ZERO Z)

module Practice-1-3 where

module Practice-1-4 where

module Practice-1-5 where
  module Case1 where
    open DerivingSystem-CompareNat1
    practice-1-5-1 : Z is-less-than S (S Z)
    practice-1-5-1 = L-TRANS Z (S Z) (S (S Z)) (L-SUCC Z) (L-SUCC (S Z))
    practice-1-5-2 : S (S Z) is-less-than S (S (S (S Z)))
    practice-1-5-2 = L-TRANS (S (S Z)) (S (S (S Z))) (S (S (S (S Z))))
                       (L-SUCC (S (S Z))) (L-SUCC (S (S (S Z))))
  module Case2 where
    open DerivingSystem-CompareNat2
    practice-1-5-1 : Z is-less-than S (S Z)
    practice-1-5-1 = L-ZERO (S Z)
    practice-1-5-2 : S (S Z) is-less-than S (S (S (S Z)))
    practice-1-5-2 = L-SUCCSUCC (S Z) (S (S (S Z)))
                       (L-SUCCSUCC Z (S (S Z)) (L-ZERO (S Z)))
  module Case3 where
    open DerivingSystem-CompareNat3
    practice-1-5-1 : Z is-less-than S (S Z)
    practice-1-5-1 = L-SUCCR Z (S Z) (L-SUCC Z)
    practice-1-5-2 : S (S Z) is-less-than S (S (S (S Z)))
    practice-1-5-2 = L-SUCCR (S (S Z)) (S (S (S Z))) (L-SUCC (S (S Z)))

module Practice-1-6 where

module Practice-1-7 where

module Practice-1-8 where
  open DerivingSystem-Nat
  open DerivingSystem-EvalNatExp
  practice-1-8-1 : E Z + E (S (S Z)) ↓ S (S Z)
  practice-1-8-1 = E-PLUS (E Z) (E (S (S Z))) Z (S (S Z)) (S (S Z)) (E-CONST Z)
                     (E-CONST (S (S Z))) (P-ZERO (S (S Z)))
  practice-1-8-2 : E (S (S Z)) + E Z ↓ S (S Z)
  practice-1-8-2 = E-PLUS (E (S (S Z))) (E Z) (S (S Z)) Z (S (S Z))
                     (E-CONST (S (S Z))) (E-CONST Z)
                     (P-SUCC (S Z) Z (S Z) (P-SUCC Z Z Z (P-ZERO Z)))
  practice-1-8-3 : E (S Z) + E (S Z) + E (S Z) ↓ S (S (S Z))
  practice-1-8-3 = E-PLUS (E (S Z) + E (S Z)) (E (S Z)) (S (S Z)) (S Z) (S (S (S Z)))
                     (E-PLUS (E (S Z)) (E (S Z)) (S Z) (S Z) (S (S Z)) (E-CONST (S Z))
                      (E-CONST (S Z)) (P-SUCC Z (S Z) (S Z) (P-ZERO (S Z))))
                     (E-CONST (S Z))
                     (P-SUCC (S Z) (S Z) (S (S Z))
                      (P-SUCC Z (S Z) (S Z) (P-ZERO (S Z))))
  practice-1-8-4 : E (S (S (S Z))) + E (S (S Z)) * E (S Z) ↓ S (S (S (S (S Z))))
  practice-1-8-4 = E-PLUS (E (S (S (S Z)))) (E (S (S Z)) * E (S Z)) (S (S (S Z)))
                     (S (S Z)) (S (S (S (S (S Z))))) (E-CONST (S (S (S Z))))
                     (E-TIMES (E (S (S Z))) (E (S Z)) (S (S Z)) (S Z) (S (S Z))
                      (E-CONST (S (S Z))) (E-CONST (S Z))
                      (T-SUCC (S Z) (S Z) (S Z) (S (S Z))
                       (T-SUCC Z (S Z) Z (S Z) (T-ZERO (S Z)) (P-SUCC Z Z Z (P-ZERO Z)))
                       (P-SUCC Z (S Z) (S Z) (P-ZERO (S Z)))))
                     (P-SUCC (S (S Z)) (S (S Z)) (S (S (S (S Z))))
                      (P-SUCC (S Z) (S (S Z)) (S (S (S Z)))
                       (P-SUCC Z (S (S Z)) (S (S Z)) (P-ZERO (S (S Z))))))
  practice-1-8-5 : (E (S (S Z)) + E (S (S Z))) * E Z ↓ Z
  practice-1-8-5 = E-TIMES (E (S (S Z)) + E (S (S Z))) (E Z) (S (S (S (S Z)))) Z Z
                     (E-PLUS (E (S (S Z))) (E (S (S Z))) (S (S Z)) (S (S Z))
                      (S (S (S (S Z)))) (E-CONST (S (S Z))) (E-CONST (S (S Z)))
                      (P-SUCC (S Z) (S (S Z)) (S (S (S Z)))
                       (P-SUCC Z (S (S Z)) (S (S Z)) (P-ZERO (S (S Z))))))
                     (E-CONST Z)
                     (T-SUCC (S (S (S Z))) Z Z Z
                      (T-SUCC (S (S Z)) Z Z Z
                       (T-SUCC (S Z) Z Z Z (T-SUCC Z Z Z Z (T-ZERO Z) (P-ZERO Z))
                        (P-ZERO Z))
                       (P-ZERO Z))
                      (P-ZERO Z))
  practice-1-8-6 : E Z * (E (S (S Z)) + E (S (S Z))) ↓ Z
  practice-1-8-6 = E-TIMES (E Z) (E (S (S Z)) + E (S (S Z))) Z (S (S (S (S Z)))) Z
                     (E-CONST Z)
                     (E-PLUS (E (S (S Z))) (E (S (S Z))) (S (S Z)) (S (S Z))
                      (S (S (S (S Z)))) (E-CONST (S (S Z))) (E-CONST (S (S Z)))
                      (P-SUCC (S Z) (S (S Z)) (S (S (S Z)))
                       (P-SUCC Z (S (S Z)) (S (S Z)) (P-ZERO (S (S Z))))))
                     (T-ZERO (S (S (S (S Z)))))

module Practice-1-9 where
  open DerivingSystem-Nat
  open DerivingSystem-ReduceNatExp
  practice-1-9-1 : E Z + E (S (S Z)) ⟶* E (S (S Z))
  practice-1-9-1 = MR-ONE (E Z + E (S (S Z))) (E (S (S Z)))
  practice-1-9-2 : E (S Z) * E (S Z) + E (S Z) * E (S Z)  ⟶d E (S Z) + E (S Z) * E (S Z)
  practice-1-9-2 = R-PLUSL (E (S Z) * E (S Z)) (E (S Z)) (E (S Z) * E (S Z))
                     (R-TIMES (S Z) (S Z) (S Z)
                      (T-SUCC Z (S Z) Z (S Z) (T-ZERO (S Z)) (P-SUCC Z Z Z (P-ZERO Z))))
  practice-1-9-3 : E (S Z) * E (S Z) + E (S Z) * E (S Z)  ⟶  E (S Z) * E (S Z) + E (S Z)
  practice-1-9-3 = R-PLUSR (E (S Z) * E (S Z)) (E (S Z) * E (S Z)) (E (S Z))
                     (R-TIMES (S Z) (S Z) (S Z)
                      (T-SUCC Z (S Z) Z (S Z) (T-ZERO (S Z)) (P-SUCC Z Z Z (P-ZERO Z))))
  practice-1-9-4 : E (S Z) * E (S Z) + E (S Z) * E (S Z)  ⟶* E (S (S Z))
  practice-1-9-4 = MR-ONE (E (S Z) * E (S Z) + E (S Z) * E (S Z)) (E (S (S Z)))

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
  practice-1-10-1 : E (S Z) * E (S Z) + E (S Z) * E (S Z)  ⟶d E (S Z) * E (S Z) + E (S Z)
  practice-1-10-1 = R-PLUSR (E (S Z) * E (S Z)) (E (S Z) * E (S Z)) (E (S Z))
                      (R-TIMES (S Z) (S Z) (S Z)
                       (T-SUCC Z (S Z) Z (S Z) (T-ZERO (S Z)) (P-SUCC Z Z Z (P-ZERO Z))))
  practice-1-10-2 : E (S Z) * E (S Z) + E (S Z) ⟶d E (S Z) + E (S Z)
  practice-1-10-2 = R-PLUSL (E (S Z) * E (S Z)) (E (S Z)) (S Z)
                      (R-TIMES (S Z) (S Z) (S Z)
                       (T-SUCC Z (S Z) Z (S Z) (T-ZERO (S Z)) (P-SUCC Z Z Z (P-ZERO Z))))
