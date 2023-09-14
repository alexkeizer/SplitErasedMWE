def Erased (α : Sort u) : Sort max 1 u :=
  Σ's : α → Prop, ∃ a, (fun b => a = b) = s

namespace Erased

def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/-- Extracts the erased value, noncomputably. -/
noncomputable def out {α} : Erased α → α
  | ⟨_, h⟩ => Classical.choose h

theorem mk_out {α} : ∀ a : Erased α, mk (out a) = a
  | ⟨s, h⟩ => by simp [mk]; congr; exact Classical.choose_spec h

@[simp]
theorem out_mk {α} (a : α) : (mk a).out = a := by
  let h := (mk a).2; show Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congrFun this a).symm rfl

@[injection]
theorem out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b :=
  Eq.mp (congr (congrArg Eq (mk_out a)) (mk_out b)) (congrArg mk h)

@[injection]
theorem mk_inj (h : Erased.mk a = Erased.mk b) : a = b := by
  injection h with fst_eq snd_eq
  have (b') : (a = b') = (b = b') := by
    show (fun b => a = b) b' = (fun b_1 => b = b_1) b'
    rw [fst_eq]
  rw [this]

end Erased

inductive Ty
  | nat
  | bool

def Ctxt : Type :=
  Erased <| List Ty

@[match_pattern]
noncomputable def Ctxt.snoc (Γ : Ctxt) (t : Ty) : Ctxt :=
  Erased.mk <| t :: Γ.out

def Ctxt.Var (Γ : Ctxt) (t : Ty) : Type :=
  { i : Nat // Γ.out.get? i = some t }

inductive CtxtProp : Ctxt → Type
  | nil : CtxtProp (Erased.mk [])
  | snoc : CtxtProp Δ → (t : Ty) → CtxtProp (Δ.snoc t)


noncomputable def matchVar {Δ : Ctxt} {t} : CtxtProp Δ → Δ.Var t  → Option Bool
  | .snoc d _, ⟨w+1, h⟩ => -- w† = Var.toSnoc w
      let w : Ctxt.Var _ t := ⟨w, by simp_all[List.get?, Ctxt.snoc]⟩
      matchVar d w
  -- Neither spelling out all cases, nor having a single fallback case work
  | .nil, _ | .snoc .., ⟨0, _⟩ => none
  -- | _, _ => none

@[injection]
theorem Erased.mk_snoc (h : Erased.mk [] = Ctxt.snoc Γ t) : [] = t :: Γ.out :=
  Erased.mk_inj h

@[injection]
theorem Erased.snoc_mk (h : Ctxt.snoc Γ t = Erased.mk []) : t :: Γ.out = [] :=
  Erased.mk_inj h

@[injection]
theorem Ctxt.snoc_inj (h : Ctxt.snoc Γ₁ t₁ = Ctxt.snoc Γ₂ t₂) : t₁ = t₂ ∧ Γ₁ = Γ₂ := by
  have := Erased.mk_inj h
  injection this with t_eq Γ_eq
  exact ⟨t_eq, Erased.out_inj _ _ Γ_eq⟩

-- set_option trace.Meta.Tactic.injection true
-- set_option trace.Meta.Match.matchEqs true
example {Δ : Ctxt} (d : CtxtProp Δ) {w : Δ.Var t} :
  matchVar d w = none
    := by
        cases w; next w h =>
        induction d generalizing w <;> cases w
        . rfl
        . rfl
        . rfl
        next ih _ => -- simp [matchVar]
          simp [matchVar]
          apply ih