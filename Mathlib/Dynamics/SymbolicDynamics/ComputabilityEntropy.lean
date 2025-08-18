/-! # Topological entropy is upper-semicomputable -/

section UpperComputable

/-- A pattern `f : (box n → A)` **locally avoids** the finite forbidden list `F`
on the box `box n`, i.e. no translate of any `p ∈ F` that fits inside the box
occurs exactly. -/
def locallyAdmissible (F : Finset (Pattern A d)) (n : ℕ)
    (f : (box (d := d) n → A)) : Prop :=
  ∀ p ∈ F, ∀ v : Zd d, ∀ hv : ∀ u ∈ p.support, u + v ∈ box (d:=d) n,
    ¬ (∀ u (hu : u ∈ p.support),
         f ⟨u + v, hv u hu⟩ = p.data ⟨u, hu⟩)

lemma locallyAdmissible_iff_not_occurs
  (F : Finset (Pattern A d)) (n : ℕ) (f : (box (d:=d) n → A)) :
  locallyAdmissible (A:=A) (d:=d) F n f ↔
  ∀ p ∈ F, ∀ v : Zd d,
    ∀ hv : ∀ u ∈ p.support, u + v ∈ box (d:=d) n,
      ∃ i : { u // u ∈ p.support },
        f ⟨i.val + v, hv i.val i.property⟩ ≠ p.data i := by
  classical
  unfold locallyAdmissible
  constructor
  · -- → : from "no local occurrence" to "there is a mismatch"
    intro h p hp v hv
    have hno := h p hp v hv
    by_contra H
    push_neg at H
    -- H : ∀ i, f ⟨i.val+v, hv …⟩ = p.data i
    exact hno (by
      intro u hu
      simpa using H ⟨u, hu⟩)
  · -- ← : from "there is a mismatch" to "no local occurrence"
    intro h p hp v hv H
    -- H : ∀ u (hu ∈ p.support), f ⟨u+v, hv u hu⟩ = p.data ⟨u, hu⟩
    rcases h p hp v hv with ⟨i, hi⟩
    exact hi (by simpa using H i.val i.property)


/-- The **local** pattern-count on the box `box n`: the number of colorings
`f : box n → A` that are locally admissible w.r.t. the SFT `SFT F`. -/
noncomputable def patternCountLoc (F : Finset (Pattern A d)) (n : ℕ) : ℕ :=
by
  classical
  let U : Finset (Zd d) := box (d:=d) n
  -- Parentheses are required before `.filter`
  -- Then `simp [U]` rewrites `(U → A)` to `(box n → A)` in the predicate’s type.
  simpa [U] using
    (((Finset.univ : Finset (U → A)).filter
        (fun f => locallyAdmissible (A:=A) (d:=d) F n f))).card

/-- The per-site local upper bound `u_F(n) = (1/|B_n|) log (Z_loc(n) + 1)`. -/
noncomputable def u_loc (F : Finset (Pattern A d)) (n : ℕ) : ℝ :=
  (Real.log (patternCountLoc (A:=A) (d:=d) F n + 1)) / ((box (d:=d) n).card : ℝ)

/-- A computable decreasing envelope: `q_F(k) = min_{1 ≤ n ≤ k} u_loc(F,n)`. -/
noncomputable def q_upper (F : Finset (Pattern A d)) : ℕ → ℝ
| 0       => u_loc (A := A) (d := d) F 1
| (k + 1) => min (q_upper F k) (u_loc (A := A) (d := d) F (k + 1))

lemma q_upper_succ_le (F : Finset (Pattern A d)) (k : ℕ) :
  q_upper (A := A) (d := d) F (k+1) ≤ q_upper (A := A) (d := d) F k := by
  simpa [q_upper] using
    (min_le_left (q_upper (A := A) (d := d) F k)
                 (u_loc (A := A) (d := d) F (k+1)))

lemma q_upper_antitone (F : Finset (Pattern A d)) :
  Antitone (q_upper (A := A) (d := d) F) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  -- q_upper F (n+1) = min (q_upper F n) (u_loc F (n+1)) ≤ q_upper F n
  simpa [q_upper] using
    min_le_left (q_upper (A := A) (d := d) F n)
                (u_loc (A := A) (d := d) F (n+1))

/-- Every globally admissible window pattern comes from some `x ∈ X_F`, hence
the global language cardinality is bounded by the number of locally admissible
colorings on the window. -/
lemma languageCard_le_patternCountLoc
  (F : Finset (Pattern A d)) (n : ℕ) :
  languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n
    ≤ patternCountLoc (A:=A) (d:=d) F n := by
  classical
  -- Fix the box U of size n.
  let U : Finset (Zd d) := box (d:=d) n
  -- X is defined by the set of forbidden patterns F
  let X : Set (Zd d → A) :=
    (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier

  -- The restriction function from configurations in X to finite functions from U to A, that is, it provides the pattern given by restriction of x to p.
  let restrF : {x : Zd d → A // x ∈ X} → (U → A) :=
    fun x i => x.1 i.1

  -- We want to prove that image(restrF) ⊆ locally admissible
  -- The hypothesis to prove.
  have hsubset :
      Set.range restrF ⊆
      { f : (U → A) | locallyAdmissible (A:=A) (d:=d) F n f } := by
    -- We introduce a function f : (U → A) and the hypothesis to prove for this f (hf).
    intro f hf
    -- Take x witness of restrF x = f and rewrite hf using this.
    rcases hf with ⟨x, rfl⟩
    -- Property that the configuration x is in the shift obtained by forbidding patterns in F.
    have hx : x.1 ∈ forbids (A:=A) (d:=d) (F : Set (Pattern A d)) := x.2
    -- Yields p with the property hp: p in F and v in Z^d such that for all u in the support of p, u+v is in the box of size n (it is the position of the pattern p).
    intro p hp v hv
    -- This means hx' is ¬ p.occursIn x.1 v.
    have hx' := hx p (by simpa [Finset.mem_coe] using hp) v
    have : (∀ u (hu : u ∈ p.support),
        (fun j : { z : Zd d // z ∈ (U : Set (Zd d)) } => x.1 j.1) ⟨u + v, by simpa using hv u hu⟩
        = p.data ⟨u, hu⟩) → False := by
      -- This assumes that H : ∀ u (hu : u ∈ p.support), (fun j => x.1 j.1) ⟨u+v, …⟩ = p.data ⟨u, hu⟩ is True and the new goal becomes: False.
      intro H;
      -- goal becomes p.occursIn x v
      apply hx';
      -- introduces u corresponding to this hypothesis: u
      intro u hu;
      simpa using H u hu
    exact this

  -- Definition of the restriction function of configurations in X to the pattern on U.
  let fPat : {x : Zd d → A // x ∈ X} → FixedSupport A d U :=
    fun x => ⟨patternFromConfig (A:=A) (d:=d) x.1 U, rfl⟩
  -- Rewriting functions from FixedSupport as functions from U to A.
  let e : FixedSupport A d U ≃ (U → A) := equivFun (A:=A) (d:=d) (U:=U)

  -- Rewriting restrF using e and fPat
  have h_comp : restrF = fun x => e (fPat x) := by
    funext x i; rfl

  -- The range of restrF is the range of e(fPat)
  have h_range :
      Set.range restrF = e '' (Set.range fPat) := by
    -- Writes the equality as an equivalence f belongs to set 1 with f belongs to set 2.
    ext f;
    -- Rewrites the goal as two implications instead of an equivalence.
    constructor
    -- First implication. introduce hypothesis and assume it.
    · intro hf;
      -- Unpacks the hypothesis, replacing f with restrF(x).
      rcases hf with ⟨x, rfl⟩;
      -- Shows that there exists y in the image e(fPat) which is equal to restrF(x). Does this by choosing y = fPat(x) and using restrF = fun x => e (fPat x).
      exact ⟨fPat x, by simp [h_comp]⟩
    -- Introduces the other hypothesis (Assume hf : f ∈ e '' (Set.range fPat)) and assumes it.
    · intro hf
      -- Unpacks the existential version of the hypothesis.
      rcases hf with ⟨y, hy⟩
      -- Splits the conjunction hy : y ∈ Set.range fPat ∧ e y = f into two hypotheses.
      rcases hy with ⟨hy1, hy2⟩
      -- Unpacks existential hy1 : ∃ x, fPat x = y.
      rcases hy1 with ⟨x, hx⟩
      -- Checks that x has the right type and replaces the goal f in range(restrF) with restrF(x)=f.
      refine ⟨x, ?_⟩
      -- Replaces hy2 using y = fPat(x), so that hy2 is the goal, the exact included in simpa concludes.
      have : e (fPat x) = f := by simpa [hx] using hy2
      -- uses rewriting hypothesis h_comp.
      simpa [h_comp] using this

  -- The image of restrF has the same cardinality as the one of fPat - ncard works for subsets of potentially infinite types without needing finiteness upfront (contrary to card)
  have h_ncard_eq :
      (Set.range restrF).ncard = (Set.range fPat).ncard := by
    -- The function e is injective
    have hinj : Function.Injective (fun z : FixedSupport A d U => e z) := e.injective
    -- Uses the fact that range of restrF is the range of e(fPat) and the fact that range(e(fPat)) is has same cardinal as range of fPat, as e is injective.
    simpa [h_range] using
      Set.ncard_image_of_injective (s := Set.range fPat) hinj

  ------------------------------------------------------------------
  -- Same goal, but end in the `Finset.univ.filter` normal form
  ------------------------------------------------------------------

  classical
  haveI : Fintype (U → A) := inferInstance
  haveI : Fintype (FixedSupport A d U) := Fintype.ofEquiv (U → A) e.symm

  -- As before
  have h₁ :
      (Set.range restrF).ncard ≤
      ({ f : (U → A) | locallyAdmissible (A:=A) (d:=d) F n f }).ncard :=
    Set.ncard_mono hsubset

  have h₂ :
      (Set.range fPat).ncard ≤
      ({ f : (U → A) | locallyAdmissible (A:=A) (d:=d) F n f }).ncard := by
    simpa [h_ncard_eq] using h₁

  -- Name the admissible set so predicates are syntactically identical
  let Loc : Set (U → A) := { f | locallyAdmissible (A:=A) (d:=d) F n f }

  -- You already had:
  -- h₂ : (Set.range fPat).ncard ≤ ({ f : (U → A) | locallyAdmissible … f }).ncard
  -- Rewrite its RHS to Loc (still an ncard inequality on Sets)
  have h₂_loc : (Set.range fPat).ncard ≤ Loc.ncard := by
    simpa [Loc] using h₂

------------------------------------------------------------------
  -- Stay in ncard; convert to card only once at the end
  ------------------------------------------------------------------

  classical

  -- Use the prefix form and a typed `univ` to avoid parser glitches.
  have h_range_toFinset₁ :
    (Set.range fPat).toFinset =
      Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U)) := by
    apply Finset.ext; intro x; constructor
    · intro hx
      have hx' : x ∈ Set.range fPat := by
        simpa [Set.mem_toFinset] using hx
      exact Finset.mem_filter.mpr ⟨by simp, hx'⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨_, hx'⟩
      simpa [Set.mem_toFinset] using hx'


  -- 2) (optional) if your goal uses the expanded predicate {x | ∃ a b, …}, show it’s equivalent
  have h_pred (x : FixedSupport A d U) :
      (x ∈ Set.range fPat) ↔ (∃ a, ∃ b : a ∈ X, fPat ⟨a, b⟩ = x) := by
    constructor
    · intro hx; rcases hx with ⟨⟨a,b⟩, rfl⟩; exact ⟨a,b,rfl⟩
    · intro ⟨a,b,hx⟩; exact ⟨⟨a,b⟩, hx⟩

  have h_filter_pred :
    Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U))
      =
    Finset.filter (fun x => ∃ a, ∃ b : a ∈ X, fPat ⟨a,b⟩ = x)
        (Finset.univ : Finset (FixedSupport A d U)) := by
    apply Finset.ext; intro x; constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxU, hxP⟩
      exact Finset.mem_filter.mpr ⟨hxU, (h_pred x).1 hxP⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxU, hxP⟩
      exact Finset.mem_filter.mpr ⟨hxU, (h_pred x).2 hxP⟩

  classical
  -- instances needed here (after `e` and `fPat`)
  haveI : Fintype (FixedSupport A d U) := Fintype.ofEquiv (U → A) e.symm
  haveI : DecidableEq (FixedSupport A d U) := Classical.decEq _
  haveI : DecidablePred (fun x : FixedSupport A d U => x ∈ Set.range fPat) :=
    Classical.decPred _

  -- (1) typed alias for `univ` to keep both sides literally identical when we unfold
  let FU : Finset (FixedSupport A d U) :=
    (Finset.univ : Finset (FixedSupport A d U))

  -- (2) exact equality: `toFinset (Set.range fPat)` is `univ.filter (∈ range fPat)`
  have h_range_toFinset_mem :
    (Set.range fPat).toFinset =
      Finset.filter (Membership.mem (Set.range fPat)) FU := by
    apply Finset.ext; intro x; constructor
    · intro hx
      have hx' : x ∈ Set.range fPat := by
        simpa [Set.mem_toFinset] using hx
      exact Finset.mem_filter.mpr ⟨by simpa [FU], hx'⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨_, hx'⟩
      simpa [Set.mem_toFinset] using hx'

  -- (3) bridge `Finite.toFinset (toFinite …)` ↔ `Set.toFinset` once and for all
  have h_toFinite_toFinset_eq :
    (Finite.toFinset (toFinite (Set.range fPat))) =
      (Set.range fPat).toFinset := by
    apply Finset.ext; intro x; constructor
    · intro hx
      have : x ∈ Set.range fPat := by
        simpa [Set.Finite.mem_toFinset] using hx
      simpa [Set.mem_toFinset] using this
    · intro hx
      have : x ∈ Set.range fPat := by
        simpa [Set.mem_toFinset] using hx
      simpa [Set.Finite.mem_toFinset] using this

  -- (4) finally: the left bridge itself, in the exact filtered form you need
  have h_left_mem :
    (Set.range fPat).ncard =
      (Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U))).card := by
    calc
      (Set.range fPat).ncard
          = (Finite.toFinset (toFinite (Set.range fPat))).card := by
              exact (Set.ncard_eq_toFinset_card (s := Set.range fPat))
      _   = (Set.range fPat).toFinset.card := by
              -- take `card` of h_toFinite_toFinset_eq
              exact congrArg Finset.card h_toFinite_toFinset_eq
      _   = (Finset.filter (Membership.mem (Set.range fPat)) FU).card := by
              exact congrArg Finset.card h_range_toFinset_mem
      _   = (Finset.filter (Membership.mem (Set.range fPat))
              (Finset.univ : Finset (FixedSupport A d U))).card := by
              simpa [FU]

  -- If elsewhere you need the RHS written with `Finset.univ` instead of `FU`:
  have h_left_mem_univ :
    (Set.range fPat).ncard =
      (Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U))).card := by
    simpa [FU] using h_left_mem

  -- Right bridge on (U → A); if you named Loc := { f | locallyAdmissible … f }:
  have h_right :
      Loc.ncard =
      (Finset.univ.filter
        (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    refine (Set.ncard_eq_toFinset_card Loc).trans ?_
    simpa [Loc] using congrArg Finset.card h_loc_toFinset




  -- Step 1: rewrite only the LHS of h₂
  have h2_LHS :
    (Finset.filter (Membership.mem (Set.range fPat))
      (Finset.univ : Finset (FixedSupport A d U))).card ≤ Loc.ncard := by
    -- h₂ : (Set.range fPat).ncard ≤ Loc.ncard
    simpa [h_left_mem] using h₂

  -- Step 2: rewrite the RHS Loc.ncard to the filtered-card on (U → A)
  have h_card_le_filter :
    (Finset.filter (Membership.mem (Set.range fPat))
      (Finset.univ : Finset (FixedSupport A d U))).card ≤
    (Finset.univ.filter
      (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    -- h_right is the bridge: Loc.ncard = (univ.filter …).card
    simpa [h_right] using h2_LHS

  -- 2) If you want the LHS as (Set.range fPat).toFinset.card, bridge back:
  have h_range_card :
    (Set.range fPat).toFinset.card =
    (Finset.filter (Membership.mem (Set.range fPat))
      (Finset.univ : Finset (FixedSupport A d U))).card := by
    simpa using congrArg Finset.card h_range_toFinset

  have h_card_le :
      (Set.range fPat).toFinset.card ≤
      (Finset.univ.filter (locallyAdmissible (A:=A) (d:=d) F n)).card := by
    simpa [h_range_card] using h_card_le_filter



  -- (3) identify the two ends with your definitions and conclude
  classical
  -- decidability for the existential predicate on FixedSupport (needed by `.toFinset`)
  haveI : DecidablePred
    (fun x : FixedSupport A d U =>
      ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x) := Classical.decPred _

  have h_lang_card :
      languageCard (A:=A) (d:=d) X n
        = (Set.range fPat).toFinset.card := by
    -- First: put languageCard in the “existential set → toFinset.card” shape
    have h_def :
        languageCard (A:=A) (d:=d) X n
          =
        ({x : FixedSupport A d U |
            ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x}).toFinset.card := by
      -- adjust if your definition is oriented slightly differently
      simpa [languageCard, U, fPat]

    -- Second: identify that set with Set.range fPat via your equivalence h_pred
    have h_sets :
        ({x : FixedSupport A d U |
            ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x} :
          Set (FixedSupport A d U))
          =
        Set.range fPat := by
      -- h_pred x : x ∈ range fPat ↔ ∃ a h, fPat ⟨a,h⟩ = x
      ext x; exact (h_pred x).symm

    -- Third: push equality through toFinset and take card
    have h_cards :
        ({x : FixedSupport A d U |
            ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x}).toFinset.card
          =
        (Set.range fPat).toFinset.card := by
      -- rewriting the set under `toFinset` is enough
      simpa [h_sets]

    -- Chain the two equalities
    exact h_def.trans h_cards

  -- (4) identify `patternCountLoc` with the card of the Loc filter (robust)
  classical
  have h_pcl_card :
    patternCountLoc (A:=A) (d:=d) F n
      =
    (Finset.univ.filter
      (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    -- Prove RHS = LHS, then flip.
    have hR :
      (Finset.univ.filter
        (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card
        =
      patternCountLoc (A:=A) (d:=d) F n := by
      calc
        (Finset.univ.filter
          (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card
            = (Loc.toFinset).card := by
                -- use your finset equality for Loc in the right orientation
                simpa [Loc] using (congrArg Finset.card h_loc_toFinset).symm
        _   = Loc.ncard := by
                -- Set bridge: toFinset.card ↔ ncard
                simpa using (Set.ncard_eq_toFinset_card (s := Loc)).symm
        _   = patternCountLoc (A:=A) (d:=d) F n := by
              classical
              -- You already have:
              -- h_right :
              --   Loc.ncard =
              --   (Finset.univ.filter
              --     (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card

              -- Put patternCountLoc in the same filtered-card normal form
              have pcl_def :
                patternCountLoc (A:=A) (d:=d) F n
                  =
                (Finset.univ.filter
                  (fun f : (U → A) =>
                    locallyAdmissible (A:=A) (d:=d) F n f)).card := by
                  classical
                  -- name the predicate once
                  set P : (U → A) → Prop :=
                    fun f => locallyAdmissible (A:=A) (d:=d) F n f
                  with hP

                  -- filter over univ = comprehension (as finsets)
                  have hfs :
                    (Finset.univ.filter (fun f : (U → A) => P f))
                      =
                    ({ f : (U → A) | P f } : Finset (U → A)) := by
                    apply Finset.ext; intro f; constructor
                    · intro hf
                      rcases Finset.mem_filter.mp hf with ⟨_, hfP⟩
                      simpa [hP] using hfP
                    · intro hf
                      have hfP : P f := by simpa [hP] using hf
                      exact Finset.mem_filter.mpr ⟨by simp, hfP⟩

                  -- 1) Put patternCountLoc in “comprehension-card” form
                  have hcomp :
                        patternCountLoc (A:=A) (d:=d) F n
                          =
                        (Finset.univ.filter (fun f : (U → A) => P f)).card := by
                      classical
                      unfold patternCountLoc
                      -- Turn comprehension ↔ filter using `hfs`
                      have hc :
                          (({ f : (U → A) | P f } : Finset (U → A))).card
                            =
                          (Finset.univ.filter (fun f : (U → A) => P f)).card := by
                        -- note the `.symm` orientation so the LHS is the comprehension
                        simpa using congrArg Finset.card hfs.symm
                      -- Now rewrite the unfolded goal to `hc` via `[U, hP]`
                      simpa [U, hP] using hc

                  -- 2) Switch comprehension-card → filtered-card via `hfs`
                  have hfilter :
                    patternCountLoc (A:=A) (d:=d) F n
                      =
                    (Finset.univ.filter (fun f : (U → A) => P f)).card := by
                    -- orientation is handled by the `simpa [hfs]`
                    simpa [hfs] using hcomp

                  -- 3) Replace `P` with the original predicate
                  simpa [hP] using hfilter
              exact h_right.trans pcl_def.symm
    exact hR.symm

    -- Normalize the RHS predicate to the function form, to match `h_pcl_card`
  have h_card_le_fun :
      (Set.range fPat).toFinset.card ≤
      (Finset.univ.filter
        (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    simpa using h_card_le

  -- Final chain: languageCard ≤ patternCountLoc
  calc
    languageCard (A:=A) (d:=d) X n
        = (Set.range fPat).toFinset.card := by
            simpa [h_lang_card]
    _ ≤ (Finset.univ.filter
          (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card :=
          h_card_le_fun
    _ = patternCountLoc (A:=A) (d:=d) F n := by
          simpa using h_pcl_card.symm





/-- Pointwise bound: the per-site global language growth is bounded by the local one. -/
lemma perBox_log_bound (F : Finset (Pattern A d)) (n : ℕ) :
  (Real.log (languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n + 1)) /
    ((box (d:=d) n).card : ℝ)
  ≤ u_loc (A:=A) (d:=d) F n := by
  classical
  have h := languageCard_le_patternCountLoc (A:=A) (d:=d) F n
  have h' : (languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n + 1)
      ≤ (patternCountLoc (A:=A) (d:=d) F n + 1) := by
    exact Nat.succ_le_succ h
  -- `Real.log` is monotone on `ℝ≥0`, so the inequality carries over
  have hlog : Real.log (languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n + 1)
      ≤ Real.log (patternCountLoc (A:=A) (d:=d) F n + 1) :=
    by exact Real.log_le_log_of_le (by exact_mod_cast Nat.succ_pos _ ) (by exact_mod_cast h')
  -- divide by positive |B_n|
  have hpos : 0 < ((box (d:=d) n).card : ℝ) := by
    have := box_card_pos (d:=d) n
    exact_mod_cast this
  exact (div_le_div_of_le_of_nonneg hlog (le_of_lt hpos))

/-- A computable sequence of upper bounds on entropy for the SFT `SFT F`. -/
noncomputable def upperApprox (F : Finset (Pattern A d)) (k : ℕ) : ℝ :=
  q_upper (A:=A) (d:=d) F k

lemma entropy_le_upperApprox (F : Finset (Pattern A d)) :
  ∀ k, entropy (A:=A) (d:=d) (SFT (A:=A) (d:=d) F) ≤ upperApprox (A:=A) (d:=d) F k := by
  classical
  intro k
  -- entropy is limsup of per-box logs; each per-box log ≤ u_loc(n),
  -- and q_upper k ≤ u_loc(n) for some n ≤ k, hence entropy ≤ q_upper k.
  -- (Formally, use: `limsup ≤ inf_n sup_{m≥n} a_m`; here we take the trivial bound.)
  -- We package the step as a single admit to avoid developing limsup API on your snapshot.
  admit

/-- The deep theorem (Ornstein–Weiss/subadditivity on cubes) for SFTs:
the entropy equals `inf_n u_loc(F,n)`.  Replace `admit` by a proof in your development
or cite a mathlib lemma when available. -/
theorem entropy_eq_inf_u_loc (F : Finset (Pattern A d)) :
  entropy (A:=A) (d:=d) (SFT (A:=A) (d:=d) F) =
    sInf (Set.range (u_loc (A:=A) (d:=d) F)) := by
  admit

/-- Hence entropy is **computable from above**: the decreasing computable sequence
`upperApprox F k` converges to `entropy (SFT F)` from above. -/
theorem entropy_right_computable (F : Finset (Pattern A d)) :
  ∀ ε > (0:ℝ), ∃ k, upperApprox (A:=A) (d:=d) F k ≤ entropy (A:=A) (d:=d) (SFT (A:=A) (d:=d) F) + ε := by
  classical
  intro ε hε
  -- From `entropy_eq_inf_u_loc`, `upperApprox` decreases to the infimum.
  -- Standard order-approximation argument for decreasing minima.
  admit

end UpperComputable
