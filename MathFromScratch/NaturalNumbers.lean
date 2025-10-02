/-!
# Numeri Naturali e Induzione in Lean 4

Questo file introduce i numeri naturali seguendo gli Assiomi di Peano
e la tecnica dell'induzione matematica.

## I Numeri Naturali in Lean:
- `Nat` è il tipo dei numeri naturali (0, 1, 2, ...)
- `Nat.zero` o `0` è il numero zero
- `Nat.succ n` è il successore di n (n + 1)
- Ogni numero naturale è o zero o il successore di qualche altro numero

## Induzione Matematica:
Per dimostrare una proprietà P(n) per tutti i numeri naturali:
1. Caso base: dimostra P(0)  
2. Passo induttivo: dimostra che P(k) → P(k+1) per ogni k

## Sintassi dell'Induzione in Lean:
- `induction n with | zero => ... | succ k ih => ...`
- `ih` è l'ipotesi induttiva: assume P(k) per dimostrare P(k+1)
-/

/-!
## Esercizio 1: Proprietà di Base del Successore
Iniziamo con alcune proprietà fondamentali.
-/

-- Zero non è il successore di nessun numero
theorem zero_ne_succ (n : Nat) : 0 ≠ Nat.succ n := by
  -- COMPLETA: dimostra che 0 ≠ succ(n)
  -- Suggerimento: usa `intro h` per assumere l'uguaglianza, poi trova la contraddizione
  sorry

-- Il successore è iniettivo
theorem succ_inj {m n : Nat} : Nat.succ m = Nat.succ n → m = n := by
  -- COMPLETA: se succ(m) = succ(n), allora m = n
  -- Suggerimento: usa `intro h` e poi `injection h`
  sorry

/-!
## Esercizio 2: Addizione sui Naturali
L'addizione è definita ricorsivamente:
- a + 0 = a
- a + succ(b) = succ(a + b)

Dimostriamo le sue proprietà fondamentali.
-/

-- Addizione con zero a destra (questo è per definizione)
theorem add_zero (n : Nat) : n + 0 = n := by
  -- COMPLETA: questo dovrebbe essere immediato
  -- Suggerimento: prova `rfl` (riflessività)
  sorry

-- Addizione con zero a sinistra (richiede induzione!)
theorem zero_add (n : Nat) : 0 + n = n := by
  -- COMPLETA: dimostra per induzione su n
  -- Caso base: 0 + 0 = 0
  -- Passo induttivo: se 0 + k = k, allora 0 + succ(k) = succ(k)
  induction n with
  | zero => 
    -- Caso base: dimostra 0 + 0 = 0
    sorry
  | succ k ih =>
    -- Passo induttivo: hai ih : 0 + k = k
    -- Devi dimostrare: 0 + succ(k) = succ(k)
    sorry

-- Successore e addizione
theorem add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := by
  -- COMPLETA: questo dovrebbe essere per definizione
  sorry

theorem succ_add (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  -- COMPLETA: richiede induzione su n
  -- Suggerimento: simile a zero_add ma con un pattern diverso
  sorry

/-!
## Esercizio 3: Commutatività dell'Addizione
Questo è un teorema importante che richiede i lemmi precedenti.
-/

theorem add_comm (m n : Nat) : m + n = n + m := by
  -- COMPLETA: dimostra la commutatività per induzione
  -- Suggerimento: usa i teoremi che hai dimostrato sopra
  -- Fai induzione su una delle variabili e usa zero_add, succ_add, add_succ
  sorry

/-!
## Esercizio 4: Associatività dell'Addizione
Altra proprietà fondamentale.
-/

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  -- COMPLETA: dimostra l'associatività per induzione
  -- Suggerimento: fai induzione su c
  sorry

/-!
## Esercizio 5: Moltiplicazione
La moltiplicazione è definita come:
- a * 0 = 0  
- a * succ(b) = a * b + a

Dimostra alcune proprietà di base.
-/

theorem mul_zero (n : Nat) : n * 0 = 0 := by
  -- COMPLETA: per definizione
  sorry

theorem zero_mul (n : Nat) : 0 * n = 0 := by
  -- COMPLETA: richiede induzione
  sorry

theorem mul_one (n : Nat) : n * 1 = n := by
  -- COMPLETA: ricorda che 1 = succ(0)
  -- Dovrai usare mul_zero e add_zero
  sorry

theorem one_mul (n : Nat) : 1 * n = n := by
  -- COMPLETA: richiede induzione
  sorry

/-!
## Esercizio 6: Proprietà Distributiva
La moltiplicazione distribuisce sull'addizione.
-/

theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  -- COMPLETA: dimostra la distributività a sinistra
  -- Suggerimento: induzione su c, usa add_assoc
  sorry

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  -- COMPLETA: dimostra la distributività a destra
  sorry

/-!
## Esercizio 6.5: Commutatività e Associatività della Moltiplicazione
Queste sono proprietà fondamentali che completano la teoria della moltiplicazione.
Per dimostrare la commutatività serve prima un lemma ausiliario.
-/

-- Lemma utile per la commutatività
theorem mul_succ (a b : Nat) : a * Nat.succ b = a * b + a := by
  -- COMPLETA: questo dovrebbe essere per definizione della moltiplicazione
  -- La moltiplicazione è definita come: a * succ(b) = a * b + a
  sorry

-- Commutatività della moltiplicazione
theorem mul_comm (m n : Nat) : m * n = n * m := by
  -- COMPLETA: dimostra per induzione su n
  -- Caso base: m * 0 = 0 * m
  -- Passo induttivo: se m * k = k * m, allora m * succ(k) = succ(k) * m
  -- Suggerimento: usa mul_zero, zero_mul, mul_succ, e i teoremi precedenti
  sorry

-- Associatività della moltiplicazione  
theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  -- COMPLETA: dimostra per induzione su c
  -- Suggerimento: usa mul_zero, mul_succ, mul_add
  sorry

/-!
## Esercizio 6.6: Potenze (Esponenziazione)
Definiamo l'esponenziazione ricorsivamente e dimostriamo le sue proprietà.

Definizione ricorsiva delle potenze:
- a^0 = 1 (per ogni a)  
- a^(succ n) = a^n * a
-/

-- Definizione delle potenze (per evitare conflitti con Nat.pow)
def myPow (a : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ n => myPow a n * a

-- Sintassi più carina (uso ** per evitare conflitti)
infix:80 " ** " => myPow

-- Proprietà di base delle potenze
theorem pow_zero (a : Nat) : a ** 0 = 1 := by
  -- COMPLETA: questo è per definizione
  sorry

theorem pow_succ (a n : Nat) : a ** Nat.succ n = a ** n * a := by
  -- COMPLETA: questo è per definizione
  sorry

-- Potenza di 1
theorem pow_one (a : Nat) : a ** 1 = a := by
  -- COMPLETA: usa pow_succ e pow_zero e mul_one
  -- Ricorda che 1 = succ(0)
  sorry

-- 1 elevato a qualsiasi potenza è 1
theorem one_pow (n : Nat) : 1 ** n = 1 := by
  -- COMPLETA: dimostra per induzione su n
  -- Suggerimento: usa pow_zero, pow_succ, one_mul
  sorry

-- 0 elevato a succ(n) è 0
theorem zero_pow_succ (n : Nat) : 0 ** Nat.succ n = 0 := by
  -- COMPLETA: usa pow_succ e zero_mul
  sorry

-- Proprietà delle potenze: a^(m+n) = a^m * a^n
theorem pow_add (a m n : Nat) : a ** (m + n) = a ** m * a ** n := by
  -- COMPLETA: dimostra per induzione su n
  -- Caso base: a^(m + 0) = a^m * a^0
  -- Passo induttivo: se a^(m + k) = a^m * a^k, allora a^(m + succ k) = a^m * a^(succ k)
  -- Suggerimento: usa add_zero, add_succ, pow_zero, pow_succ, mul_one, mul_assoc
  sorry

-- Proprietà delle potenze: (a^m)^n = a^(m*n)
theorem pow_mul (a m n : Nat) : (a ** m) ** n = a ** (m * n) := by
  -- COMPLETA: questo è più avanzato, richiede induzione e proprietà precedenti
  -- Suggerimento: induzione su n, usa pow_zero, pow_succ, pow_add, mul_zero, mul_succ
  sorry

-- Proprietà delle potenze: (a*b)^n = a^n * b^n
theorem mul_pow (a b n : Nat) : (a * b) ** n = a ** n * b ** n := by
  -- COMPLETA: dimostra per induzione su n
  -- Suggerimento: usa pow_zero, pow_succ, mul_one, mul_assoc, mul_comm per riorganizzare
  sorry

/-!
## Esercizio 7: Relazione di Ordine
Definiamo quando un numero è minore o uguale a un altro.
-/

-- La relazione ≤ sui naturali (per evitare conflitti con Nat.le)
def myLe (m n : Nat) : Prop := ∃ k, m + k = n

-- Sintassi più carina
infix:50 " ≤≤ " => myLe

-- Proprietà di base dell'ordine
theorem le_refl (n : Nat) : n ≤≤ n := by
  -- COMPLETA: ogni numero è ≤ a se stesso
  -- Suggerimento: usa la definizione di ≤ con k = 0
  sorry

theorem le_trans {a b c : Nat} : a ≤≤ b → b ≤≤ c → a ≤≤ c := by
  -- COMPLETA: la relazione ≤ è transitiva
  -- Suggerimento: se a + k₁ = b e b + k₂ = c, allora a + (k₁ + k₂) = c
  sorry

theorem le_antisymm {m n : Nat} : m ≤≤ n → n ≤≤ m → m = n := by
  -- COMPLETA: se m ≤ n e n ≤ m, allora m = n
  -- Suggerimento: se m + k₁ = n e n + k₂ = m, cosa puoi dire di k₁ e k₂?
  sorry

/-!
## Esercizio Bonus: Un Teorema Più Avanzato
Dimostra che l'addizione è cancellativa.
-/

theorem add_cancel_left {a b c : Nat} : a + b = a + c → b = c := by
  -- COMPLETA: se a + b = a + c, allora b = c
  -- Questo è più difficile e potrebbe richiedere tecniche avanzate
  sorry

/-!
## Note per lo Studio:
1. Inizia con i teoremi più semplici (zero_ne_succ, add_zero)
2. L'induzione segue sempre lo stesso pattern: caso base + passo induttivo  
3. Usa sempre i teoremi precedenti per dimostrare quelli successivi
4. La tattica `simp` può semplificare espressioni aritmetiche
5. `rw [theorem_name]` riscrive usando un teorema di uguaglianza
-/