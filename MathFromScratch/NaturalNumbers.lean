/-!
# Numeri Naturali e Induzione Matematica

La costruzione rigorosa dei numeri naturali seguendo gli Assiomi di Peano e l'introduzione 
del principio di induzione matematica - uno strumento fondamentale per la dimostrazione.

**Sviluppo Storico:**
- **Euclide (circa 300 a.C.)**: Prime proprietà aritmetiche negli "Elementi"
- **Pierre de Fermat (1601-1665)**: Primo uso dell'induzione matematica
- **Blaise Pascal (1623-1662)**: Formalizzazione del principio di induzione
- **Giuseppe Peano (1858-1932)**: Assiomatizzazione rigorosa dei naturali (1889)

**I Numeri Naturali:**
Ogni numero naturale è o zero o il successore di qualche altro numero naturale.
Questa definizione ricorsiva cattura l'essenza dell'infinito numerabile.
-/

/-!
## Assiomi di Peano: Proprietà del Successore

**Giuseppe Peano (1858-1932)** rivoluzionò l'aritmetica con la sua assiomatizzazione. 
Professore all'Università di Torino, Peano era ossessionato dalla precisione matematica
e creò persino una lingua artificiale (Latino sine flexione) per la comunicazione scientifica.

**Significato:** Questi assiomi garantiscono che ogni numero naturale sia unico e 
che la successione 0, 1, 2, 3, ... sia ben definita senza ambiguità.
-/

theorem zero_ne_succ (n : Nat) : 0 ≠ Nat.succ n := sorry

theorem succ_inj {m n : Nat} : Nat.succ m = Nat.succ n → m = n := sorry

/-!
## Addizione: La Prima Operazione

**Definizione Ricorsiva:**
- a + 0 = a (elemento neutro)
- a + succ(b) = succ(a + b) (costruzione iterativa)

**Scoperta Storica:** Anche se l'addizione sembra naturale, la sua definizione rigorosa 
richiese millenni. I Babilonesi (2000 a.C.) sapevano calcolare, ma non avevano 
una teoria formale delle operazioni.
-/

theorem add_zero (n : Nat) : n + 0 = n := sorry

/-!
## Zero come Elemento Neutro a Sinistra

**Sfida Storica:** Dimostrare che 0 + n = n richiede induzione! Questo sorprese i 
matematici del XIX secolo: proprietà "ovvie" necessitavano dimostrazioni non banali.

**L'Induzione Matematica:** Principio scoperto da Fermat nel XVII secolo durante 
i suoi studi sui numeri figurati. Pascal lo rese famoso, ma la prima dimostrazione 
rigorosa appartiene a Peano.
-/

theorem zero_add (n : Nat) : 0 + n = n := sorry

theorem add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := sorry

theorem succ_add (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := sorry

/-!
## Commutatività dell'Addizione

**Carl Friedrich Gauss (1777-1855)** raccontava di aver scoperto questa proprietà
da bambino quando, punito dal maestro a calcolare 1+2+...+100, trovò immediatamente
la risposta usando 50×101. Aveva intuito che l'ordine non conta.

**Significato Profondo:** La commutatività collega l'aritmetica alla geometria:
contare oggetti in righe o colonne dà lo stesso risultato.
-/

theorem add_comm (m n : Nat) : m + n = n + m := sorry

/-!
## Associatività: Raggruppare le Operazioni

**Arthur Cayley (1821-1895)** fu il primo a studiare sistematicamente questa proprietà
nell'algebra astratta. Avvocato per metà carriera, poi matematico puro, dimostrò che
molte strutture condividono le stesse proprietà operazionali.
-/

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := sorry

/-!
## Moltiplicazione: Addizione Ripetuta

**Definizione Ricorsiva:**
- a × 0 = 0 (non ci sono copie di a)
- a × succ(b) = a × b + a (una copia in più di a)

**Evoluzione Storica:** Gli Egizi (1650 a.C.) moltiplicavano solo per raddoppiamento.
I Greci introdussero la moltiplicazione generale, ma la vedevano geometricamente 
come area di rettangoli.
-/

theorem mul_zero (n : Nat) : n * 0 = 0 := sorry

theorem zero_mul (n : Nat) : 0 * n = 0 := sorry

theorem mul_one (n : Nat) : n * 1 = n := sorry

theorem one_mul (n : Nat) : 1 * n = n := sorry

/-!
## Proprietà Distributiva

**Scoperta da:** Euclide negli "Elementi" (circa 300 a.C.)
**Proposizione:** La moltiplicazione distribuisce sull'addizione

**Significato Geometrico:** Se hai un rettangolo di dimensioni a×(b+c), puoi spezzarlo
in due rettangoli a×b e a×c. Euclide lo vedeva come proprietà delle aree, non dei numeri!

**Impatto Moderno:** Questa proprietà è alla base dell'algebra: permette di "aprire le parentesi"
in espressioni come a(b+c) = ab + ac.
-/

theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := sorry

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := sorry

/-!
## Commutatività e Associatività della Moltiplicazione

**Brahmagupta (628 d.C.)** fu il primo matematico a trattare sistematicamente queste proprietà
nei suoi testi indiani. Lavorando con numeri negativi (sconosciuti ai Greci), scoprì
che le regole dell'aritmetica hanno validità universale.
-/

theorem mul_succ (a b : Nat) : a * Nat.succ b = a * b + a := sorry

theorem mul_comm (m n : Nat) : m * n = n * m := sorry

theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := sorry

/-!
## Esponenziazione: Moltiplicazione Ripetuta

**Definizione Ricorsiva:**
- a^0 = 1 (per convenzione universale)
- a^(succ n) = a^n × a (una moltiplicazione in più)

**Michael Stifel (1487-1567)** introdusse la notazione moderna per gli esponenti.
Monaco agostiniano poi convertito al protestantesimo, fu perseguitato per le sue idee
religiose ma rivoluzionò la notazione algebrica.

**Controversia dello Zero:** Perché a^0 = 1? Questa convenzione fu dibattuta per secoli.
La risposta viene dalle proprietà: a^(m+n) = a^m × a^n richiede che a^0 = 1.
-/

def myPow (a : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ n => myPow a n * a

infix:80 " ** " => myPow

theorem pow_zero (a : Nat) : a ** 0 = 1 := sorry

theorem pow_succ (a n : Nat) : a ** Nat.succ n = a ** n * a := sorry

theorem pow_one (a : Nat) : a ** 1 = a := sorry

theorem one_pow (n : Nat) : 1 ** n = 1 := sorry

theorem zero_pow_succ (n : Nat) : 0 ** Nat.succ n = 0 := sorry

/-!
## Leggi degli Esponenti

**John Wallis (1616-1703)** fu il primo a studiare sistematicamente le proprietà degli esponenti.
Matematico inglese e decrittografo per Oliver Cromwell, introdusse il simbolo ∞ per l'infinito
e anticipò il calcolo integrale.

**Legge Fondamentale:** a^(m+n) = a^m × a^n
Questa proprietà trasforma l'addizione degli esponenti in moltiplicazione delle potenze,
collegando le tre operazioni aritmetiche in una gerarchia elegante.
-/

theorem pow_add (a m n : Nat) : a ** (m + n) = a ** m * a ** n := sorry

theorem pow_mul (a m n : Nat) : (a ** m) ** n = a ** (m * n) := sorry

theorem mul_pow (a b n : Nat) : (a * b) ** n = a ** n * b ** n := sorry

/-!
## Relazione d'Ordine

**Definizione:** m ≤ n se esiste k tale che m + k = n
**Significato:** Cattura l'intuizione che "minore o uguale" significa "si può raggiungere aggiungendo qualcosa"

**Origini:** Il concetto di ordine è antico quanto il contare, ma la sua formalizzazione 
matematica risale a **Richard Dedekind (1831-1916)**, che studiò i "tagli" per costruire i reali.
-/

def myLe (m n : Nat) : Prop := ∃ k, m + k = n

infix:50 " ≤≤ " => myLe

theorem le_refl (n : Nat) : n ≤≤ n := sorry

theorem le_trans {a b c : Nat} : a ≤≤ b → b ≤≤ c → a ≤≤ c := sorry

/-!
## Antisimmetria dell'Ordine

**Teorema Fondamentale:** Se m ≤ n e n ≤ m, allora m = n

**Importanza:** Questo principio distingue l'ordine totale (sui naturali) da ordini più generali.
È alla base del principio di buon ordinamento che caratterizza i numeri naturali.
-/

theorem le_antisymm {m n : Nat} : m ≤≤ n → n ≤≤ m → m = n := sorry

/-!
## Cancellazione nell'Addizione

**Teorema:** Se a + b = a + c, allora b = c

**Giuseppe Peano** considerava questo teorema così fondamentale da includerlo 
tra i suoi assiomi originali. Dimostra che l'addizione è "fedele": numeri diversi 
producono sempre somme diverse quando aggiunti allo stesso numero.

**Conseguenza:** Questo principio è essenziale per "risolvere equazioni" - 
il fondamento dell'algebra elementare.
-/

theorem add_cancel_left {a b c : Nat} : a + b = a + c → b = c := sorry