  --------------------------- HOMSL(ω) ----------------------------------
  structure Symbols where
    FunSyms : Type
    PredSyms : Type
  deriving Repr

  variable (Syms : Symbols)

  structure Variable where
    name : String
  deriving Repr, BEq

  inductive Term where
    | var (x : Variable)
    | tree (symbol : Syms.FunSyms)
    | pred (symbol : Syms.PredSyms)
    | app (a b : Term)
    | id

  @[simp]
  axiom left_id_does_nothing : ∀ t : Term Syms, (Term.id).app t = t

  inductive GoalFormula where
    | atomic (A : Term Syms)
    | and (G H : GoalFormula)
    | existential (x : Variable) (G : GoalFormula)
    | true

  inductive HOMSLHead : List Variable → Type where
    | pred (P : Syms.PredSyms) (ys : List Variable) : HOMSLHead ys
    | predC (P : Syms.PredSyms) (c : Syms.FunSyms) (ys : List Variable) : HOMSLHead ys

  @[simp]
  def HOMSLhead2goal (A : HOMSLHead Syms ys) : GoalFormula Syms :=
    match A with
      | HOMSLHead.pred P ys => GoalFormula.atomic (List.foldl (λ term y => Term.app term (Term.var y)) (Term.pred P) ys)  -- (...(((P y₁) y₂) y₃) ...) y_n
      | HOMSLHead.predC P c ys => GoalFormula.atomic (Term.app (Term.pred P) (List.foldl (λ term y => Term.app term (Term.var y)) (Term.tree c) ys))  -- P ((...(((c y₁) y₂) y₃) ...) y_n)

  inductive HOMSLDefiniteClause where
    | forAll (ys : List Variable) (G : GoalFormula Syms) (A : HOMSLHead Syms ys)
    | true

  abbrev HOMSLDefFm := List (HOMSLDefiniteClause Syms)

  def Substitution := List (Variable × Term Syms)

  def get_substitution (x : Variable) (s : Substitution Syms) : Option (Term Syms) :=
    (s.find? (λ (y, _) => x == y)).map Prod.snd

  def substitute_term (T : Term Syms) (s : Substitution Syms) : Term Syms :=
    match T with
      | Term.var x =>
        match get_substitution Syms x s with
          | some t => t
          | none => Term.var x
      | Term.app p q => Term.app (substitute_term p s) (substitute_term q s)
      | _ => T

  def substitute_goal (G : GoalFormula Syms) (s : Substitution Syms) : GoalFormula Syms :=
    match G with
      | GoalFormula.atomic t => GoalFormula.atomic (substitute_term Syms t s)
      | GoalFormula.and G H => GoalFormula.and (substitute_goal G s) (substitute_goal H s)
      | GoalFormula.true => GoalFormula.true
      | GoalFormula.existential x G =>
          let s' := s.filter (λ (y, _) => y != x)
          GoalFormula.existential x (substitute_goal G s')

  @[simp]
  def combine_substs (σ₁ σ₂ : Substitution Syms) : Substitution Syms :=
    List.map (λ p => (p.fst, substitute_term Syms p.snd σ₂)) σ₁


  theorem true_subs_intro (σ : Substitution Syms) : GoalFormula.true = substitute_goal Syms GoalFormula.true σ :=
    by
      unfold substitute_goal
      rfl

  inductive HOMSLProof : HOMSLDefFm Syms → GoalFormula Syms → Type 2 where
  | True : (D : HOMSLDefFm Syms) → HOMSLProof D GoalFormula.true
  | And : HOMSLProof D G → HOMSLProof D H → HOMSLProof D (G.and H)
  | Ex : HOMSLProof D (substitute_goal Syms G [(x, t)]) → HOMSLProof D (G.existential x)
  | Res : HOMSLProof D (substitute_goal Syms G s) → (HOMSLDefiniteClause.forAll ys G A) ∈ D
      → HOMSLProof D (substitute_goal Syms (HOMSLhead2goal Syms A) s)


  def HOMSLProvable (D : HOMSLDefFm Syms) (G : GoalFormula Syms) : Prop :=
    ∃ (_ : HOMSLProof Syms D G), True


  --------------------------- MSL(ω) ----------------------------------
  inductive FunSymsHash where
    | original : Syms.FunSyms → FunSymsHash
    | hash : Syms.PredSyms → FunSymsHash


  inductive PredSymsHash where
    | original : Syms.PredSyms → PredSymsHash
    | T

  def Hash : Symbols :=
    {FunSyms := FunSymsHash Syms, PredSyms := PredSymsHash Syms}


  inductive MSLHead : List Variable → Type where
    | T (P : Syms.PredSyms) (ys : List Variable) : MSLHead ys
    | og (P : Syms.PredSyms) (c : Syms.FunSyms) (ys : List Variable) : MSLHead ys
    | refl (P : Syms.PredSyms) (c : Syms.FunSyms) (ys : List Variable) : MSLHead [{name := "z"}]

  axiom refl_is_T_form (P : Syms.PredSyms) (c : Syms.FunSyms) (ys : List Variable) : MSLHead.refl P c ys = MSLHead.T P [{name := "z"}]

  @[simp]
  def update_subst (σ : Substitution (Hash Syms)) (A : MSLHead Syms ys) : Substitution (Hash Syms) :=
    match A with
      | MSLHead.refl _ c ys => combine_substs (Hash Syms) [({name := "z"}, (List.foldl (λ term y => Term.app term (Term.var y)) (Term.tree (FunSymsHash.original c)) ys))] σ
      | _ => σ

  def transform_term (t : Term Syms) : Term (Hash Syms) :=
    match t with
      | Term.var x => Term.var x
      | Term.tree c => Term.tree (FunSymsHash.original c)
      | Term.pred P => Term.tree (FunSymsHash.hash P)
      | Term.app a b => Term.app (transform_term a) (transform_term b)
      | Term.id => Term.id

  def transform_head (A : HOMSLHead Syms ys) : MSLHead Syms ys :=
    match A with
      | HOMSLHead.pred P ys => MSLHead.T P ys
      | HOMSLHead.predC P c ys => MSLHead.og P c ys


  def transform_goal (G : GoalFormula Syms) : GoalFormula (Hash Syms) :=
    match G with
      | GoalFormula.true => GoalFormula.true
      | GoalFormula.atomic A => GoalFormula.atomic ((Term.pred PredSymsHash.T).app (transform_term Syms A))
      | GoalFormula.and H I => GoalFormula.and (transform_goal H) (transform_goal I)
      | GoalFormula.existential x H => GoalFormula.existential x (transform_goal H)

  inductive MSLDefiniteClause : Type where
    | forAll (ys : List Variable) (G : GoalFormula (Hash Syms)) (A : MSLHead Syms ys)
    | true

  def transform_definite_clause (C : HOMSLDefiniteClause Syms) : List (MSLDefiniteClause Syms) :=
    match C with
      | HOMSLDefiniteClause.forAll ys G A =>
          match A with
            | HOMSLHead.pred P ys => [MSLDefiniteClause.forAll ys (transform_goal Syms G) (MSLHead.T P ys)]
            | HOMSLHead.predC P c ys => [MSLDefiniteClause.forAll ys (transform_goal Syms G) (MSLHead.og P c ys),
                                        MSLDefiniteClause.forAll [{name := "z"}] (GoalFormula.atomic (Term.app (Term.pred (PredSymsHash.original P)) (Term.var {name := "z"}))) (MSLHead.refl P c ys)]
      | HOMSLDefiniteClause.true => [MSLDefiniteClause.true]


  abbrev MSLDefFm := List (MSLDefiniteClause Syms)


  def transform_definite_formula (D : HOMSLDefFm Syms) : MSLDefFm Syms :=
    (D.map (transform_definite_clause Syms)).flatten

  def transform_subst (s : Substitution Syms) : Substitution (Hash Syms) :=
    s.map (Prod.map id (transform_term Syms))

  @[simp]
  def MSLhead2goal (A : MSLHead Syms ys) : GoalFormula (Hash Syms) :=
    match A with
      | MSLHead.T P ys => GoalFormula.atomic (Term.app (Term.pred (PredSymsHash.T)) (List.foldl (λ term y => Term.app term (Term.var y)) (Term.tree (FunSymsHash.hash P)) ys))
      | MSLHead.og P c ys => GoalFormula.atomic (Term.app (Term.pred (PredSymsHash.original P)) (List.foldl (λ term y => Term.app term (Term.var y)) (Term.tree (FunSymsHash.original c)) ys))
      | MSLHead.refl P _ ys => GoalFormula.atomic (Term.app (Term.pred (PredSymsHash.T)) (Term.app (Term.tree (FunSymsHash.hash P)) (Term.var {name := "z"})))


  def MSLget_head (C : MSLDefiniteClause Syms) : GoalFormula (Hash Syms) :=
    match C with
      | MSLDefiniteClause.forAll _ _ A => MSLhead2goal Syms A
      | MSLDefiniteClause.true => GoalFormula.true

  inductive MSLProof : MSLDefFm Syms → GoalFormula (Hash Syms) → Type 2 where
    | True : (D : MSLDefFm Syms) → MSLProof D GoalFormula.true
    | And : MSLProof D G → MSLProof D H → MSLProof D (G.and H)
    | Ex : MSLProof D (substitute_goal (Hash Syms) G [(x, t)]) → MSLProof D (G.existential x)
    | Res : MSLProof D (substitute_goal (Hash Syms) G s) → (MSLDefiniteClause.forAll ys G A) ∈ D
        → MSLProof D (substitute_goal (Hash Syms) (MSLhead2goal Syms A) s)

  def MSLProvable (D : MSLDefFm Syms) (G : GoalFormula (Hash Syms)) : Prop :=
    ∃ (_ : MSLProof Syms D G), True


  ----------------  D ⊢ G → |D| ⊢ |G| -----------------------------
  @[simp]
  axiom subs_transform_comm (G : GoalFormula Syms) (s : Substitution Syms) : transform_goal Syms (substitute_goal Syms G s) = substitute_goal (Hash Syms) (transform_goal Syms G) (transform_subst Syms s)

  @[simp]
  axiom term_subs_transform_comm (t : Term Syms) (s : Substitution Syms) : transform_term Syms (substitute_term Syms t s) = substitute_term (Hash Syms) (transform_term Syms t) (transform_subst Syms s)

  @[simp]
  theorem transform_fold : transform_term Syms (List.foldl (fun term y => term.app (Term.var y)) t ys) = List.foldl (fun term y => term.app (Term.var y)) (transform_term Syms t) ys :=
    by
      induction ys generalizing t
      case nil => simp
      case cons y ys ih =>
        simp [transform_term]
        rw [ih]
        rfl


  theorem df_mem_means_tdf_mem : (HOMSLDefiniteClause.forAll ys G A) ∈ D →
    MSLDefiniteClause.forAll ys (transform_goal Syms G)
        (transform_head Syms A) ∈ transform_definite_formula Syms D :=
        by
          intro h
          unfold transform_definite_formula
          rw [List.mem_flatten]
          exists transform_definite_clause Syms (HOMSLDefiniteClause.forAll ys G A)
          apply And.intro
          case left =>
            apply List.mem_map_of_mem
            exact h
          case right =>
            unfold transform_definite_clause
            cases A
            case pred P =>
              simp [h]
              rfl
            case predC P c =>
              simp
              unfold transform_head
              simp


  theorem dc_mem_means_tdc_subset : C ∈ D →
    transform_definite_clause Syms C ⊆ transform_definite_formula Syms D :=
        by
          intro memC x x_in
          unfold transform_definite_formula
          rw [List.mem_flatten]
          exists transform_definite_clause Syms C
          apply And.intro
          apply List.mem_map_of_mem
          exact memC
          exact x_in




  theorem intro_z (ys : List Variable) :
      (substitute_goal Syms
        (GoalFormula.atomic (Term.app (Term.pred P) c_ys_term))
          s)
    =
      (substitute_goal Syms
        (GoalFormula.atomic (Term.app (Term.pred P) (Term.var {name := "z"})))
          (combine_substs Syms [({name := "z"}, c_ys_term)] s)) := -- assume ys in correct order

      by
        simp only [substitute_goal]
        apply congrArg GoalFormula.atomic
        simp

        induction ys
        case nil =>
          simp [substitute_term]
          rw [get_substitution]
          simp
          have : (Variable.mk "z" == Variable.mk "z") = true := by decide
          rw [this]
          simp

        case cons y ys ih =>
          simp [substitute_term]
          rw [get_substitution]
          simp
          have : (Variable.mk "z" == Variable.mk "z") = true := by decide
          rw [this]
          simp


  theorem b1 : HOMSLProvable Syms D G → MSLProvable Syms (transform_definite_formula Syms D) (transform_goal Syms G) :=
    by
      intro h
      obtain ⟨HOMSLpf⟩ := h
      induction HOMSLpf with
        | True =>
            unfold transform_goal
            exists MSLProof.True (transform_definite_formula Syms D)
        | And pfG pfH ihG ihH =>
            obtain ⟨pfG'⟩ := ihG
            obtain ⟨pfH'⟩ := ihH
            exists MSLProof.And pfG' pfH'
        | Ex pf ih =>
            obtain ⟨pf'⟩ := ih
            rw [subs_transform_comm] at pf'
            exists MSLProof.Ex pf'
        | @Res G σ ys A pf side ih =>
            obtain ⟨ih_pf⟩ := ih
            rw [subs_transform_comm] at ih_pf

            cases A with
              | predC P c ys =>
                  have memTr : transform_definite_clause Syms (HOMSLDefiniteClause.forAll ys G (HOMSLHead.predC P c ys)) ⊆ transform_definite_formula Syms D := dc_mem_means_tdc_subset Syms side
                  simp [transform_definite_clause] at memTr
                  cases memTr with
                  | intro og refl =>
                      have pf1 : MSLProof Syms (transform_definite_formula Syms D)
                        (substitute_goal (Hash Syms)
                          (GoalFormula.atomic (Term.app (Term.pred (PredSymsHash.original P)) (List.foldl (λ term y => Term.app term (Term.var y)) (Term.tree (FunSymsHash.original c)) ys)))
                            (transform_subst Syms σ)) :=
                        MSLProof.Res ih_pf og

                      rw [intro_z (Hash Syms)] at pf1
                      simp at pf1

                      rw [refl_is_T_form] at refl

                      have pf2 : MSLProof Syms (transform_definite_formula Syms D) (substitute_goal (Hash Syms) (MSLhead2goal Syms (MSLHead.T P [{ name := "z" }])) [({name := "z"}, substitute_term (Hash Syms)
                        (List.foldl (fun term y => term.app (Term.var y)) (Term.tree (FunSymsHash.original c)) ys)
                        (transform_subst Syms σ))]) := MSLProof.Res pf1 refl

                      simp [substitute_goal, MSLhead2goal] at pf2

                      unfold substitute_goal
                      simp [transform_goal, transform_term]
                      simp [substitute_goal, substitute_term]

                      simp [substitute_term, get_substitution] at pf2
                      have : (Variable.mk "z" == Variable.mk "z") = true := by decide
                      rw [this] at pf2
                      simp at pf2
                      exists pf2
                      exact ys



              | pred P ys =>
                  have memTr : MSLDefiniteClause.forAll ys (transform_goal Syms G) (MSLHead.T P ys) ∈ transform_definite_formula Syms D := df_mem_means_tdf_mem Syms side
                  rw [subs_transform_comm]
                  let x := MSLProof.Res ih_pf memTr
                  simp at x
                  simp [transform_goal]
                  exists x




---------------------------- |D| ⊢ G → D ⊢ |G|⁻¹ --------------------------------
  @[simp]
  def inverse_term_transform (T' : Term (Hash Syms)) : Term Syms :=
    match T' with
      | Term.var x => Term.var x
      | Term.tree (FunSymsHash.hash P) => Term.pred P
      | Term.tree (FunSymsHash.original c) => Term.tree c
      | Term.app S Q => Term.app (inverse_term_transform S) (inverse_term_transform Q)
      | Term.pred (PredSymsHash.original P) => Term.pred P
      | Term.pred (PredSymsHash.T) => Term.id
      | Term.id => Term.id

  @[simp]
  def inverse_goal_transform (G' : GoalFormula (Hash Syms)) : GoalFormula Syms :=
    match G' with
      | GoalFormula.true => GoalFormula.true
      | GoalFormula.atomic A => GoalFormula.atomic (inverse_term_transform Syms A)
      | GoalFormula.and H' I' => GoalFormula.and (inverse_goal_transform H') (inverse_goal_transform I')
      | GoalFormula.existential x G => GoalFormula.existential x (inverse_goal_transform G)  -- the type is always γ so no need to transform

  @[simp]
  def get_provenance (C' : MSLDefiniteClause Syms) : HOMSLDefiniteClause Syms :=
    match C' with
      | MSLDefiniteClause.true => HOMSLDefiniteClause.true
      | MSLDefiniteClause.forAll ys G A =>
          match A with
            | MSLHead.og P c ys => HOMSLDefiniteClause.forAll ys (inverse_goal_transform Syms G) (HOMSLHead.predC P c ys)
            | MSLHead.T P ys => HOMSLDefiniteClause.forAll ys (inverse_goal_transform Syms G) (HOMSLHead.pred P ys)
            | MSLHead.refl P c ys => HOMSLDefiniteClause.forAll ys (inverse_goal_transform Syms G) (HOMSLHead.predC P c ys)

  @[simp]
  def inverse_subst_transform (σ : Substitution (Hash Syms)) : Substitution Syms :=
    σ.map (Prod.map id (inverse_term_transform Syms))

  @[simp]
  axiom subst_inverse_goal_comm (G : GoalFormula (Hash Syms)) (s : Substitution (Hash Syms)) : inverse_goal_transform Syms (substitute_goal (Hash Syms) G s) = substitute_goal Syms (inverse_goal_transform Syms G) (inverse_subst_transform Syms s)

  @[simp]
  theorem inverse_transform_fold : inverse_term_transform Syms (List.foldl (fun term y => term.app (Term.var y)) t ys) = List.foldl (fun term y => term.app (Term.var y)) (inverse_term_transform Syms t) ys :=
    by
      induction ys generalizing t
      case nil => simp
      case cons y ys ih =>
        simp [inverse_term_transform]
        rw [ih]
        rfl


  theorem term_tfm_inv_eq_id : (inverse_term_transform Syms (transform_term Syms T)) = T :=
    by
      unfold transform_term
      cases T
      case var x => simp
      case tree c => simp
      case pred c => simp
      case app P Q =>
        simp
        apply And.intro
        case left => apply term_tfm_inv_eq_id
        case right => apply term_tfm_inv_eq_id
      case id => simp


  theorem tfm_inv_eq_id : (inverse_goal_transform Syms (transform_goal Syms G)) = G :=
    by
      unfold transform_goal
      cases G
      case atomic A =>
        simp
        apply term_tfm_inv_eq_id
      case and G H =>
        simp
        apply And.intro
        case left => apply tfm_inv_eq_id
        case right => apply tfm_inv_eq_id
      case existential x G =>
        simp
        apply tfm_inv_eq_id
      case true => simp



  axiom c_inv (C : MSLDefiniteClause Syms) (C' : HOMSLDefiniteClause Syms) : C ∈ (transform_definite_clause Syms C') → (get_provenance Syms C) = C'


  @[simp]
  theorem tdf_mem_means_df_mem2 : C ∈ (transform_definite_formula Syms D) → (get_provenance Syms C) ∈ D :=
      by
        intro h

        unfold transform_definite_formula at h
        rw [List.mem_flatten] at h
        obtain ⟨tC, ⟨tC_in, C_in⟩⟩ := h
        rcases List.mem_map.mp tC_in with ⟨C', C'_in_D, rfl⟩

        have : (get_provenance Syms C) = C' := c_inv Syms C C' C_in
        rw [this]
        exact C'_in_D


  axiom hyp_goal_from_side (G : GoalFormula (Hash Syms)) (P : Syms.PredSyms) (c : Syms.FunSyms) (ys : List Variable) (D : MSLDefFm Syms): MSLDefiniteClause.forAll [{name := "z"}] G (MSLHead.refl P c ys) ∈ D → G = GoalFormula.atomic (Term.app (Term.pred (PredSymsHash.original P)) (Term.var {name := "z"}))


  theorem b2 : MSLProvable Syms (transform_definite_formula Syms D) G → HOMSLProvable Syms D (inverse_goal_transform Syms G) :=
    by
      intros h
      obtain ⟨pf, _⟩ := h
      induction pf with
        | True => exists HOMSLProof.True D
        | And pfG pfH ihG ihH =>
            obtain ⟨MSLG⟩ := ihG
            obtain ⟨MSLH⟩ := ihH
            exists HOMSLProof.And MSLG MSLH
        | Ex pf ih =>
            obtain ⟨x⟩ := ih
            simp at x
            exists HOMSLProof.Ex x
        | @Res G σ ys A pf side ih =>
            obtain ⟨pf'⟩ := ih
            simp at pf'
            cases A with
              | og P c ys =>
                  have og_side := tdf_mem_means_df_mem2 Syms side
                  simp [get_provenance] at og_side
                  simp [MSLhead2goal]
                  exists HOMSLProof.Res pf' og_side

              | T P ys =>
                  have og_side := tdf_mem_means_df_mem2 Syms side
                  simp
                  exists HOMSLProof.Res pf' og_side

              | refl P c ys =>
                  have og_side := tdf_mem_means_df_mem2 Syms side
                  simp at og_side
                  simp
                  have : G = GoalFormula.atomic (Term.app (Term.pred (PredSymsHash.original P)) (Term.var {name := "z"})) := hyp_goal_from_side Syms G P c ys (transform_definite_formula Syms D) side
                  rw [this] at pf'
                  exists pf'




  ------------------------ D ⊢ G ↔ |D| ⊢ |G| -----------------------------------
  theorem thm3_1 : HOMSLProvable Syms D G ↔ MSLProvable Syms (transform_definite_formula Syms D) (transform_goal Syms G) :=
    by
      constructor
      intro h
      apply b1
      exact h

      intro h

      have pf : HOMSLProvable Syms D (inverse_goal_transform Syms (transform_goal Syms G)) :=
        by
          apply b2
          exact h

      rw [tfm_inv_eq_id] at pf
      exact pf
end formalisation



-- EXAMPLES
section examples
  inductive MyFunSyms where
    | a

  inductive MyPredSyms where
    | P
    | Q
    | R
    | S

  abbrev MySyms : Symbols := {FunSyms := MyFunSyms, PredSyms := MyPredSyms}

  def x := Variable.mk "x"
  def y := Variable.mk "y"
  def xT : Term MySyms := Term.var x
  def yT : Term MySyms := Term.var y
  def a := MyFunSyms.a
  def P := (MyPredSyms.P)
  def Q := (MyPredSyms.Q)
  def R := (MyPredSyms.R)
  def S := (MyPredSyms.S)
  def PT : Term MySyms := Term.pred P
  def QT : Term MySyms := Term.pred Q
  def RT : Term MySyms := Term.pred R
  def St : Term MySyms := Term.pred S

  def myD : HOMSLDefFm MySyms := [HOMSLDefiniteClause.forAll [x] (GoalFormula.atomic (Term.app (Term.app PT QT) xT)) (HOMSLHead.pred S [x]),
                                  HOMSLDefiniteClause.forAll [x, y] (GoalFormula.and (GoalFormula.atomic (Term.app RT yT)) (GoalFormula.atomic (Term.app xT yT))) (HOMSLHead.pred P [x, y]),
                                  HOMSLDefiniteClause.forAll [x] (GoalFormula.atomic (Term.app RT xT)) (HOMSLHead.predC Q a [x]),
                                  HOMSLDefiniteClause.forAll [x] (GoalFormula.true) (HOMSLHead.predC R a [x])]
  def tfmdD := transform_definite_formula MySyms myD
  #reduce tfmdD

  def a' : Term (Hash MySyms) := Term.tree (FunSymsHash.original a)
  def s : Term (Hash MySyms) := Term.tree (FunSymsHash.hash S)
  def r : Term (Hash MySyms) := Term.tree (FunSymsHash.hash R)
  def R' : Term (Hash MySyms) := Term.pred (PredSymsHash.original R)
  def T : Term (Hash MySyms) := Term.pred (PredSymsHash.T)
  def c : Term (Hash MySyms) := Term.var {name := "c"}
  def xT' : Term (Hash MySyms) := Term.var x
  def z := Variable.mk "z"

  theorem exProof : MSLProvable MySyms tfmdD (GoalFormula.atomic (T.app (r.app (a'.app (a'.app c))))) := by
    have pf1 : MSLProof MySyms tfmdD GoalFormula.true := MSLProof.True tfmdD
    rw [true_subs_intro (Hash MySyms) [(x, a'.app c)]] at pf1

    have side1 : MSLDefiniteClause.forAll [x] GoalFormula.true (MSLHead.og MyPredSyms.R MyFunSyms.a [x]) ∈ tfmdD :=
      by
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.head

    have pf2 : MSLProof MySyms tfmdD (substitute_goal (Hash MySyms) (GoalFormula.atomic ((Term.pred (PredSymsHash.original R)).app (a'.app xT'))) [(x, a'.app c)]) := MSLProof.Res pf1 side1

    rw [intro_z (Hash MySyms)] at pf2
    simp at pf2

    have side2 : MSLDefiniteClause.forAll [z] (GoalFormula.atomic ((Term.pred (PredSymsHash.original MyPredSyms.R)).app (Term.var { name := "z" }))) (MSLHead.refl MyPredSyms.R MyFunSyms.a [x]) ∈ tfmdD :=
      by
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.tail
        apply List.Mem.head

    simp at side2

    have pf3 : MSLProof MySyms tfmdD (substitute_goal (Hash MySyms) (GoalFormula.atomic (Term.app (Term.pred PredSymsHash.T) (r.app (Term.var z)))) [(z, a'.app (a'.app c))]) := MSLProof.Res pf2 side2

    exists pf3
    exact []


end examples
