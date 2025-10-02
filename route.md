# Percorso di Formalizzazione in Lean 4: Dalle Basi alla Logica

Questo percorso è strutturato per seguire l'ordine di dipendenza logica e riflette l'evoluzione storica della matematica, ideale per studiare la **teoria e la logica formale**.

## 1. Fondamenti Logici e Aritmetica (Livello Base 🎓)

Questa fase costruisce il linguaggio e le strutture numeriche discrete.

### A. Immersione in Lean
* **Obiettivo:** Acquisire familiarità con l'ambiente e la sintassi.
* **Concetti:** Interazione `by`, tattiche base (`rfl`, `exact`), l'uso dell'InfoView (Stato della Dimostrazione).
* **Riferimenti:** **Natural Number Game**, prime sezioni di **Theorem Proving in Lean**.

### B. Logica Proposizionale
* **Obiettivo:** Comprendere le regole di inferenza formale.
* **Concetti:** Implicazione ($\to$), Congiunzione ($\wedge$), Disgiunzione ($\vee$), Negazione ($\neg$).

### C. Numeri Naturali ($\mathbb{N}$)
* **Obiettivo:** Formalizzare gli **Assiomi di Peano** e stabilire l'**Induzione Matematica**.
* **Concetti:** Definizione ricorsiva di `add` e `mul`, dimostrazione delle proprietà base (es. commutatività).

### D. Numeri Interi ($\mathbb{Z}$) e Razionali ($\mathbb{Q}$)
* **Obiettivo:** Costruire le prime strutture con operazioni invertibili (debito e divisione).
* **Concetti:** Costruzione come coppie o tramite relazione di equivalenza, dimostrazione che $\mathbb{Q}$ è un campo.

---

## 2. L'Algebra e la Misura del Continuo (Livello Intermedio 📚)

Si formalizzano le strutture astratte e si definisce il continuo matematico.

### E. Algebra Astratta
* **Obiettivo:** Generalizzare le proprietà delle operazioni.
* **Strutture:** Definizione e studio di **Gruppi** (struttura base), **Anelli** (due operazioni) e **Campi** (tutte le operazioni invertibili).

### F. Numeri Reali ($\mathbb{R}$)
* **Obiettivo:** Formalizzare la proprietà di **Completezza**, essenziale per l'analisi.
* **Concetti:** Costruzione (es. Sezioni di Dedekind o successioni di Cauchy), dimostrazione dell'esistenza di $\sup$ e $\inf$.

### G. Numeri Complessi ($\mathbb{C}$)
* **Obiettivo:** Estendere i reali per l'Algebra (Teorema Fondamentale dell'Algebra).
* **Concetti:** $\mathbb{C}$ come $\mathbb{R} \times \mathbb{R}$, definizione di $i$ e dimostrazione che $i^2 = -1$.

### H. Spazi Vettoriali e Algebra Lineare
* **Obiettivo:** Fornire la base per l'Algebra Lineare.
* **Concetti:** Formalizzazione dei **Moduli** e degli **Spazi Vettoriali** su un campo.

---

## 3. L'Analisi e la Topologia (Livello Avanzato 🔬)

Il rigoroso studio dei limiti e delle funzioni nel continuo.

### I. Topologia Generale
* **Obiettivo:** Definire astrattamente il concetto di "vicinanza" e "apertura".
* **Concetti:** Formalizzazione di **Spazi Metrici** e **Spazi Topologici**, definizione di **Intorno** (`nhds`).

### L. Limiti e Continuità
* **Obiettivo:** Rigorizzare il concetto di limite.
* **Concetti:** Definizione $\epsilon$-$\delta$ (o tramite filtri), funzioni **Continue** (in $\mathbb{R}$ e in spazi topologici generali).

### M. Derivate e Integrali
* **Obiettivo:** Formalizzazione del Calcolo Differenziale e Integrale.
* **Concetti:** Definizione della **Derivata** come limite, **Integrale di Riemann/Lebesgue**, dimostrazione del **Teorema Fondamentale del Calcolo**.

---

## 4. Metamatematica e Logica Fondazionale (Livello Esperto 💡)

La fase in cui la matematica analizza sé stessa.

### N. Teoria degli Insiemi in Lean
* **Obiettivo:** Capire le collezioni di oggetti e la loro dimensione.
* **Concetti:** Definizione formale di `Set` (Insiemi), **Cardinalità** (es. il Teorema di Cantor), e l'impatto dell'**Assioma della Scelta**.

### O. Logica del Primo Ordine (FOL)
* **Obiettivo:** Formalizzare un sistema logico *esterno* a quello di Lean per studiarne le proprietà.
* **Concetti:** Sintassi delle formule, regole di inferenza, dimostrazione di **Correttezza** e **Completezza** della FOL.

### P. Teorema di Incompletezza di Gödel
* **Obiettivo:** La sfida ultima: formalizzare l'auto-referenza logica.
* **Concetti:** Formalizzazione dell'**Aritmetica di Peano (PA)**, processo di **Gödellizzazione** (codifica di formule e dimostrazioni in numeri), e dimostrazione del **Primo Teorema di Incompletezza**.
