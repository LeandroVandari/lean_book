def even (n : Nat) : Prop :=
  ∃k, k*2 = n

def prime (n : Nat) : Prop :=
  n > 1 ∧ ∀a, (∃p, n = a*p) → a = 1 ∨ a = n

def infinitely_many_primes : Prop :=
  ∀n, (∃p, prime p ∧ p > n)

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃k, (k > 0) ∧ (2^k + 1 = n)

def infinitely_many_Fermat_primes : Prop :=
  ∀n, (∃p, Fermat_prime p ∧ p > n)

def goldbach_conjecture : Prop :=
  ∀n, (n > 2 ∧ even n) → ∃p₁ p₂, (prime p₁ ∧ prime p₂ ∧ p₁ + p₂ = n)

def Goldbach's_weak_conjecture : Prop :=
  ∀n, (n > 5 ∧ ¬(even n)) → ∃p₁ p₂ p₃, (prime p₁ ∧ prime p₂ ∧ prime p₃ ∧ p₁ + p₂ + p₃ = n)

def Fermat's_last_theorem : Prop :=
  ∀n: Nat, (n > 2) → ¬(∃a b c : Nat, (a^n + b^n = c^n))
