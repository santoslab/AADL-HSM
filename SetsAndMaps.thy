theory SetsAndMaps
  imports Main
begin

section "States as Partial Functions"

(* Gerwin suggested that using "the" directly below would help with proof automation *)
definition opt_get :: "'a option \<Rightarrow> 'a" 
  where [simp add]: "opt_get optval \<equiv> the optval"

(* Gerwin suggested that using "the" directly below would help with proof automation *)
definition map_get :: "('a, 'b) map \<Rightarrow> 'a \<Rightarrow> 'b"  (infixl "$" 73)
  where [simp add]: "map_get m k = the (m k)"

lemma map_some_val: 
  assumes "x \<in> dom f"
  shows "(f x = Some y) = (f $ x = y)"
proof
  show "f x = Some y \<Longrightarrow> f $ x = y"
    by simp
next
  show "f $ x = y \<Longrightarrow> f x = Some y"
    using assms by force
qed

lemma map_some_val_given:
  assumes "f x = Some y"
  shows "f $ x = y"
  by (simp add: assms)

lemma singleton_unfold: "[a \<mapsto> b] = (\<lambda>x. if x = a then Some b else None)"
  by fastforce

lemma singleton_map_upd: "m(a\<mapsto>b) = m ++ [a \<mapsto> b]"
  unfolding map_add_def singleton_unfold
  by fastforce

section "Sets of States and State Updates"

definition map_Add (infixl "**" 100) where "map_Add X Y = {x ++ y | x y. x \<in> X \<and> y \<in> Y }"

lemma map_Add_assoc: "X ** (Y ** Z) = (X ** Y) ** Z"
proof
  show "X ** Y ** Z \<subseteq> X ** (Y ** Z)" 
  proof
    fix x
    assume "x \<in> X ** Y ** Z"
    then show "x \<in> X ** (Y ** Z)" unfolding map_Add_def apply simp
      by (metis map_add_assoc)
    qed
next
  show "X ** (Y ** Z) \<subseteq> X ** Y ** Z" unfolding map_Add_def apply simp by force
qed

lemma map_Add_unit_right[simp]: "X ** {Map.empty} = X" unfolding map_Add_def by force
lemma map_Add_unit_left[simp]: "{Map.empty} ** X = X" unfolding map_Add_def by force
lemma map_Add_empty_right[simp]: "X ** {} = {}" unfolding map_Add_def by simp
lemma map_Add_empty_left[simp]: "{} ** X = {}" unfolding map_Add_def by simp

lemma map_Add_extract: "{s ++ m | s m. s \<in> S \<and> p m } = S ** { m | m. p m }"
proof
  show "{s ++ m |s m. s \<in> S \<and> p m} \<subseteq> S ** {m |m. p m}" using map_Add_def by fastforce
next
  show "S ** {m |m. p m} \<subseteq> {s ++ m |s m. s \<in> S \<and> p m}" by (simp add: map_Add_def)
qed

lemma map_Add_over:
  assumes x: "x \<in> S ** T" 
      and d: "\<forall>y \<in> T. dom x \<subseteq> dom y"
    shows "x \<in> T"
proof -
  obtain p q where x1: "p \<in> S" and x2: "q \<in> T" and x3: "x = p ++ q" using x
    by (smt (verit) CollectD map_Add_def)
  then have h1: "dom x \<subseteq> dom q" using d by simp
  then show ?thesis
    by (metis Un_iff dom_map_add map_add_subsumed1 map_add_subsumed2 map_le_def map_le_map_add 
        subsetI subset_antisym x2 x3)
qed

lemma map_Add_extend:
  assumes x: "x \<in> S ** T"
      and d: "\<forall>a \<in> S.\<forall>b \<in> T. dom a \<subseteq> dom b"
    shows "x \<in> T"
  using x d
  by (smt (verit) CollectD Un_absorb2 dom_map_add map_Add_def map_le_antisym map_le_def map_le_map_add)

section "Merging States"

definition merge :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixl "\<uplus>\<^sub>m" 55) where
  "m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<equiv> \<lambda>a. if \<exists>y. {Some y} = {m\<^sub>1 a, m\<^sub>2 a} - {None} then (THE b. b \<in> {m\<^sub>1 a, m\<^sub>2 a} - {None}) else None"

lemma merge_unit[simp]: "m \<uplus>\<^sub>m Map.empty = m"
proof
  fix x
  show "(m \<uplus>\<^sub>m Map.empty) x = m x"
    proof (cases "m x = None")
      case True
      then show ?thesis 
        by (simp add: merge_def)
    next
      case False
      then show ?thesis
        apply (simp add: merge_def)
        by auto
    qed
qed

lemma merge_comm: "m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 = m\<^sub>2 \<uplus>\<^sub>m m\<^sub>1"
proof
  fix x
  show "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) x = (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>1) x"
  proof (cases "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) x = None")
    case True
    then show ?thesis 
      by (smt (verit) insertI1 insert_commute merge_def singletonD the_equality)
  next
    case False
    then show ?thesis
      by (simp add: insert_commute merge_def)
  qed
qed

lemma map_merge_left_sub: "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {} \<Longrightarrow> m\<^sub>1 \<subseteq>\<^sub>m (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2)"
proof (simp only: map_le_def; standard)
  fix a
  assume a1: "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
     and a2: "a \<in> dom m\<^sub>1"
  have x1: "m\<^sub>2 a = None"
    using a1 a2 by blast
  from a2 obtain y where y1: "m\<^sub>1 a = Some y" by blast
  show "m\<^sub>1 a = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a" using a1 unfolding merge_def dom_def apply (simp add: x1 y1)
    by (smt (verit, best) Diff_insert_absorb emptyE insertE insert_commute option.distinct(1) the_equality)
qed

lemma map_merge_right_sub: "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {} \<Longrightarrow> m\<^sub>2 \<subseteq>\<^sub>m (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2)"
  by (metis inf_commute map_merge_left_sub merge_comm)

(*  Syntax error related to subscripts in the text below.
text \<open> Associativity "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3 = m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)" does not hold in general because None models top and bottom \<close>
*)

lemma assoc_disjoint:
  assumes d1: "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
      and d2: "dom m\<^sub>1 \<inter> dom m\<^sub>3 = {}"
      and d3: "dom m\<^sub>2 \<inter> dom m\<^sub>3 = {}"
    shows "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3 = m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)"
proof -
  have h1: "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3 \<subseteq>\<^sub>m m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)"
  proof (simp only: map_le_def; standard)
    fix a
    assume "a \<in> dom (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)"
    then obtain y where y1: "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a = Some y" by blast
    hence h4: "Some y = (m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      have u1: "m\<^sub>1 a = Some y"
        using y1 True d1 apply (simp add: merge_def)
        by (smt (z3) Diff_iff d2 domIff insert_absorb insert_disjoint(2) insert_iff option.distinct(1) the1_equality)
      then show ?thesis 
        using True d1 d2 apply (simp add: merge_def)
        by (smt (verit) Diff_insert_absorb domIff insertE insert_absorb insert_absorb2 insert_commute insert_disjoint(2) insert_not_empty option.distinct(1) the_equality)
    next
      case False
      have u2: "m\<^sub>1 a = None" using False by blast
      then show ?thesis
      proof (cases "a \<in> dom m\<^sub>2")
        case True
        have u1: "m\<^sub>2 a = Some y"
          using y1 True d2 apply (simp add: merge_def)
          by (smt (z3) Diff_iff d3 domIff insert_absorb insert_disjoint(1) insert_iff option.distinct(1) the1_equality)
        have u3: "m\<^sub>3 a = None" using True d3 by blast
      then show ?thesis
        using True u1 u2 u3 apply (simp add: merge_def)
        by (smt (verit, best) Diff_cancel empty_Diff insert_Diff_if member_remove not_None_eq remove_def the_equality)
      next
        case False
        have u3: "m\<^sub>2 a = None" using False by blast
        have u1: "m\<^sub>3 a = Some y"
          using y1 u2 u3 apply (simp add: merge_def)
          by (smt (z3) Diff_cancel Diff_insert_absorb insert_absorb2 insert_not_empty option.simps(3) singletonD theI_unique)
        then show ?thesis using False u1 u2 u3 by (simp add: merge_def)
      qed
    qed
    show "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a = (m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a" by (simp add: h4 y1)
  qed
  have h2: "m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) \<subseteq>\<^sub>m (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3" 
  proof (simp only: map_le_def; standard)
    fix a
    assume a1: "a \<in> dom (m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3))"
    then obtain y where y1: "(m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a = Some y" by blast
    hence h5: " Some y = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      have u1: "m\<^sub>1 a = Some y"
        using y1 True apply (simp add: merge_def)
        by (smt (z3) Diff_iff a1 domIff insertCI insertE the_equality y1)
      have u2: "m\<^sub>2 a = None" using True d1 by blast
      have u3: "m\<^sub>3 a = None" using True d2 by blast
      then show ?thesis
        using True u1 u2 u3 y1 apply (simp add: merge_def)
        by (smt (verit) option.distinct(1) the_equality)
    next
      case False
      have u2: "m\<^sub>1 a = None" using False by blast
      then show ?thesis
      proof (cases "a \<in> dom m\<^sub>2")
        case True
        have u1: "m\<^sub>2 a = Some y"
          using y1 u2 True d2 apply (simp add: merge_def)
          by (smt (z3) Diff_iff domIff insert_iff option.simps(3) theI)
        have u3: "m\<^sub>3 a = None" using True d3 by blast
        then show ?thesis
          using u1 u2 u3 apply (simp add: merge_def)
          by (smt (verit, best) Diff_insert_absorb emptyE insertE insert_commute option.distinct(1) the_equality)
      next
        case False
        have u1: "m\<^sub>2 a = None" using False by blast
        have u3: "m\<^sub>3 a = Some y"
          using y1 u2 u1 apply (simp add: merge_def)
          by (smt (z3) Diff_iff insert_Diff1 option.distinct(1) singletonD singletonI theI)
        then show ?thesis using False u1 u2 u3 by (simp add: merge_def)
      qed
    qed
    show "(m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a" by (simp add: h5 y1)
  qed
  show ?thesis using h1 h2 map_le_antisym by blast
qed

definition Merge :: "('a \<rightharpoonup> 'b) set \<Rightarrow> ('a \<rightharpoonup> 'b)"  ("\<Uplus>\<^sub>m _" [900] 900) where
  "(\<Uplus>\<^sub>m M) \<equiv> \<lambda>a. if (\<exists>y. {Some y} = { b | b m. m \<in> M \<and> m a = b  \<and> b \<noteq> None }) 
    then (THE b. \<exists> m. m \<in> M \<and> m a = b \<and> b \<noteq> None) 
    else None"

lemma Merge_empty[simp]: "(\<Uplus>\<^sub>m {}) = Map.empty"
  unfolding Merge_def by simp

lemma map_Merge_not_none: "(\<Uplus>\<^sub>m M) a \<noteq> None \<Longrightarrow> \<exists>y. \<forall>m \<in> M. m a \<noteq> None \<longrightarrow> m a = Some y"
proof -
  assume a1: "(\<Uplus>\<^sub>m M) a \<noteq> None"
  then obtain y where y1: "(\<Uplus>\<^sub>m M) a = Some y" by blast
  hence h1: "Some y = (THE b. \<exists> m. m \<in> M \<and> m a = b \<and> b \<noteq> None)"
    by (metis (mono_tags, lifting) Merge_def option.distinct(1))
  have "\<forall>m \<in> M. m a \<noteq> None \<longrightarrow> m a = Some y"
  proof
    fix m
    assume m1: "m \<in> M"
    show "m a \<noteq> None \<longrightarrow> m a = Some y"
    proof
      assume m2: "m a \<noteq> None"
      show "m a = Some y" using a1 m1 m2 apply(simp add: h1 Merge_def)
        by (smt (verit, del_insts) mem_Collect_eq option.distinct(1) singleton_iff theI_unique)
    qed
  qed
  thus ?thesis by blast
qed

lemma map_Merge_le: "\<lbrakk>m \<in> M; \<forall>m' \<in> M. dom m \<inter> dom m' = {}\<rbrakk> \<Longrightarrow> (\<Uplus>\<^sub>m M) |` dom m \<subseteq>\<^sub>m m"
  by fastforce

lemma map_Merge_dom_sub: "dom (\<Uplus>\<^sub>m M) \<subseteq> (\<Union>m \<in> M. dom m)"
proof
  fix x
  assume a1: "x \<in> dom (\<Uplus>\<^sub>m M)"
  then show "x \<in> (\<Union>m \<in> M. dom m)"
    unfolding dom_def apply(simp add: Merge_def)
    by (smt (verit, best) insertI1 mem_Collect_eq option.distinct(1))
qed

lemma map_Merge_dom: 
  assumes "\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
  shows "dom (\<Uplus>\<^sub>m M) = (\<Union>m \<in> M. dom m)"
proof
  show "dom (\<Uplus>\<^sub>m M) \<subseteq> (\<Union>m \<in> M. dom m)"
  proof
    fix x
    assume "x \<in> dom (\<Uplus>\<^sub>m M)"
    then show "x \<in> (\<Union>m \<in> M. dom m)"
      unfolding dom_def apply(simp add: Merge_def)
      by (smt (verit) insertI1 mem_Collect_eq option.distinct(1))
  qed
next
  show "(\<Union>m \<in> M. dom m) \<subseteq> dom (\<Uplus>\<^sub>m M)"
  proof
    fix x
    assume "x \<in> (\<Union>m \<in> M. dom m)"
    then show "x \<in> dom (\<Uplus>\<^sub>m M)"
      unfolding dom_def apply(simp add: Merge_def)
      using assms by fastforce
  qed
qed

lemma not_dom_Merge: 
  assumes a: "a \<notin> M"
      and d: "\<forall>m \<in> M. dom a \<inter> dom m = {}"
    shows "dom a \<inter> dom (\<Uplus>\<^sub>m M) = {}"
proof
  have "\<And>x. x \<in> dom a \<Longrightarrow> x \<notin> dom (\<Uplus>\<^sub>m M)"
    using a d unfolding Merge_def apply (simp add: dom_def; clarify)
    by (smt (verit) domI empty_Collect_eq insert_disjoint(2) insert_dom insert_not_empty)
  thus "dom a \<inter> dom (\<Uplus>\<^sub>m M) \<subseteq> {}" by blast
next
  show "{} \<subseteq> dom a \<inter> dom (\<Uplus>\<^sub>m M)" by blast
qed

lemma empty_Merge: 
  assumes a: "a = Map.empty"
    shows "dom a \<inter> dom (\<Uplus>\<^sub>m M) = {}"
  by (simp add: assms)

lemma merge_Merge_union: 
  assumes d: "\<forall>m' \<in> M. dom m \<inter> dom m' = {}"
  shows "\<Uplus>\<^sub>m (M\<union>{m}) = \<Uplus>\<^sub>m M \<uplus>\<^sub>m m"
proof (rule map_le_antisym)
  show h1: "(\<Uplus>\<^sub>m (M \<union> {m})) \<subseteq>\<^sub>m (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m)"
  proof (simp only: map_le_def; standard)
    fix a
    assume a1: "a \<in> dom (\<Uplus>\<^sub>m (M \<union> {m}))"
    then obtain y where a2: "Some y = (\<Uplus>\<^sub>m (M \<union> {m})) a" by force
    have "Some y = (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a"
    proof (cases "a \<in> dom m")
      case True
      then have t1: "a \<in> dom m" by blast
      then have a3: "Some y = m a" using a2 unfolding Merge_def
        by (metis (mono_tags, lifting) UnI2 domIff mem_Collect_eq option.simps(3) 
            singletonD singletonI the_equality)
      show ?thesis
      proof (cases "a \<in> dom (\<Uplus>\<^sub>m M)")
        case True
        have "(\<Uplus>\<^sub>m M) a = Some y"
          using t1 True d unfolding Merge_def apply (simp only: a2 a3)
          by (smt (verit) domIff empty_Collect_eq insert_absorb insert_disjoint(2) insert_not_empty)
        then show ?thesis using t1 d a3 unfolding Merge_def
          by (smt (verit, best) domIff insert_disjoint(1) insert_dom mem_Collect_eq singletonI)
      next
        case False
        then have t2: "(\<Uplus>\<^sub>m M) a = None" by (simp add: domIff)
        show ?thesis using False t1 d a3 unfolding merge_def apply (simp add: t2)
          by (smt (verit, ccfv_threshold) Diff_empty Diff_insert0 emptyE insertE the_equality)
      qed
    next
      case False
      hence t4: "m a = None" by blast
      hence t5: "\<forall>m' \<in> M. m' a = Some y \<or> m' a = None" 
        using a2 t4 unfolding Merge_def
        by (metis (mono_tags, lifting) Un_iff mem_Collect_eq option.simps(3) singleton_iff the_equality)
      then obtain m' where t6: "m' \<in> M" and t7: "m' a = Some y"
        using a1 unfolding Merge_def
        by (smt (verit, ccfv_threshold) False Un_iff domIff empty_Collect_eq insert_not_empty singletonD)
      hence t5: "(\<Uplus>\<^sub>m M) a = Some y" using t5 unfolding Merge_def apply simp
        by (smt (verit, ccfv_threshold) Collect_cong option.distinct(1) singleton_conv the_equality)
      then show ?thesis using t5 unfolding merge_def
        by (simp add: insert_commute t4)
    qed
    then show "(\<Uplus>\<^sub>m (M \<union> {m})) a = (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a" by (simp add: a2)
  qed
next
  show h2: "(\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) \<subseteq>\<^sub>m (\<Uplus>\<^sub>m (M \<union> {m}))"
  proof (simp only: map_le_def; standard)
    fix a
    assume a3: "a \<in> dom (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m)"
    then obtain y where b1: "Some y = (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a" by force
    have b2: "Some y = (\<Uplus>\<^sub>m (M \<union> {m})) a"
    proof (cases "a \<in> dom m")
      case True
      hence b3: "m a = Some y" using b1 unfolding merge_def
        by (smt (z3) Diff_iff domIff empty_Collect_eq insert_Diff1 insert_Diff_single insert_absorb 
            insert_commute insert_iff insert_not_empty merge_def not_Some_eq singletonD singletonI theI)
      hence b5: "\<forall>m' \<in> M. m' a = Some y \<or> m' a = None"
        using True d by blast
      hence b6: "\<forall>m' \<in> M\<union>{m}. m' a = Some y \<or> m' a = None" using b3 by fastforce
      then show ?thesis unfolding Merge_def
        by (smt (z3) Collect_cong True Un_insert_right domIff insert_iff singleton_conv2 the_equality)
    next
      case False
      hence b7: "m a = None" by blast
      hence b8: "Some y = (\<Uplus>\<^sub>m M) a" using b1 unfolding merge_def
        by (metis Diff_iff insertI1 insert_absorb2 option.distinct(1) singletonD the_equality)
      hence b9: "\<forall>m' \<in> M. m' a = Some y \<or> m' a = None" unfolding Merge_def 
        by (metis (mono_tags, lifting) mem_Collect_eq option.simps(3) singleton_iff the_equality)
      hence t8: "\<forall>m' \<in> M\<union>{m}. m' a = Some y \<or> m' a = None" using b7 by simp
      from b8 b9 obtain m' where x1: "m' \<in> M" and x2: "m' a = Some y" unfolding Merge_def
        by (smt (verit, best) all_not_in_conv empty_not_insert mem_Collect_eq option.distinct(1))
      then show ?thesis using t8 unfolding Merge_def
        by (smt (z3) Collect_cong Collect_empty_eq UnCI singleton_conv the_equality)
    qed
    show "(\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a = (\<Uplus>\<^sub>m (M \<union> {m})) a"
      using b1 b2 by presburger
  qed
qed

lemma merge_Merge_diff: 
  assumes m: "m \<in> M"
      and d: "\<forall>m' \<in> M-{m}. dom m \<inter> dom m' = {}"
  shows "\<Uplus>\<^sub>m M = \<Uplus>\<^sub>m (M-{m}) \<uplus>\<^sub>m m"
  using d m merge_Merge_union[of "M-{m}" "m"] by (simp add: insert_absorb)

lemma map_add_merge:
  assumes d: "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
  shows "m\<^sub>1 ++ m\<^sub>2 = m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2"
proof (rule map_le_antisym)
  show "m\<^sub>1 ++ m\<^sub>2 \<subseteq>\<^sub>m m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2"
  proof (simp only: map_le_def; standard)
    fix a
    assume a1: "a \<in> dom (m\<^sub>1 ++ m\<^sub>2)"
    then obtain y where y1: "Some y = (m\<^sub>1 ++ m\<^sub>2) a" by (metis domD)
    hence "Some y = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      hence b0: "m\<^sub>2 a = None" using d by blast
      hence b1: "(m\<^sub>1 ++ m\<^sub>2) a = m\<^sub>1 a" using d by (simp add: domIff map_add_dom_app_simps(3))
      then show ?thesis using b0 y1 unfolding merge_def apply (simp add: b1)
        by (smt (verit, ccfv_SIG) Diff_insert_absorb empty_iff insertE insert_commute 
            option.distinct(1) the_equality)
    next
      case False
      hence b2: "(m\<^sub>1 ++ m\<^sub>2) a = m\<^sub>2 a" using d by (simp add: map_add_dom_app_simps(2))
      then show ?thesis using False y1 unfolding merge_def apply (simp add: b2)
        by (smt (verit, ccfv_threshold) Diff_insert_absorb domIff empty_iff insert_iff 
            option.distinct(1) the_equality)
    qed
    then show "(m\<^sub>1 ++ m\<^sub>2) a = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a" using y1 by presburger
  qed
next
  show "m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<subseteq>\<^sub>m m\<^sub>1 ++ m\<^sub>2"
  proof (simp only: map_le_def; standard)
    fix a
    assume a2: "a \<in> dom (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2)"
    then obtain y where y1: "Some y = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a" by (metis domD)
    hence "Some y = (m\<^sub>1 ++ m\<^sub>2) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      hence b3: "m\<^sub>2 a = None" using d by blast
      have b4: "m\<^sub>1 a = Some y" using y1 True d unfolding merge_def apply (simp only: b3)
        by (metis (no_types, lifting) Diff_iff insertE option.distinct(1) singletonI the_equality)
      then show ?thesis by (simp add: b3 map_add_def)
    next
      case False
      hence b5: "m\<^sub>1 a = None" by blast
      have b6: "m\<^sub>2 a = Some y" using y1 False d unfolding merge_def apply (simp only: b5)
        by (metis Diff_iff insertCI insertE not_None_eq theI)
      then show ?thesis by simp
    qed
    then show "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a = (m\<^sub>1 ++ m\<^sub>2) a" using y1 by presburger
  qed
qed

section "State and State Update Reordering by Way of Merging"

subsection "State and State Sequences"

fun map_add_seq where
  "map_add_seq s [] = s"
| "map_add_seq s (m#ms) = map_add_seq (s ++ m) ms"

lemma map_add_seq_foldl: "map_add_seq s ms = foldl map_add s ms"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by fastforce
next
  case (Cons a ms)
  then show ?case by simp
qed

(*
lemma map_add_seq_Merge_eq: 
  "\<lbrakk> \<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. m\<^sub>1 \<noteq> m\<^sub>2 \<longrightarrow> dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}; M = set ms; card M = length ms \<rbrakk> \<Longrightarrow> map_add_seq s ms = s ++ (\<Uplus>\<^sub>m M)"
proof (induction ms arbitrary: M s)
  case Nil
  have h1: "map_add_seq s [] = s" by simp
  hence h2: "M = {}" using Nil.prems(2) by auto  
  hence h2: "\<Uplus>\<^sub>m M = Map.empty" by simp
  then show ?case by simp
next
  case (Cons a ms)
  have h3: "a \<notin> set ms" by (metis Cons.prems(2) Cons.prems(3) card_distinct distinct.simps(2))
  have h4: "M = {a} \<union> set ms" by (simp add: Cons.prems(2))
  have h5: "card (M-{a}) = length ms" using h3 apply (simp add: h4)
    using Cons.prems(2) Cons.prems(3) by auto
  have x2: "\<forall>m \<in> M. a \<noteq> m \<longrightarrow> dom a \<inter> dom m = {}" by (simp add: Cons.prems(1) h4)
  have x3: "dom a \<inter> dom (\<Uplus>\<^sub>m (M - {a})) = {}"
     by (metis DiffD1 DiffD2 insertI1 not_dom_Merge x2)
  have h6: "map_add_seq (s ++ a) ms = (s ++ a) ++ \<Uplus>\<^sub>m (M-{a})"
    using Cons.IH[of "M-{a}" "s ++ a"] 
    using Cons.prems(1) h3 h4 h5 by force
  have h7: "map_add_seq s (a#ms) = (s ++ a) ++ \<Uplus>\<^sub>m (M-{a})"
    using Cons.prems(1) Cons.prems(2) h6 by simp
  have h8: "... = s ++ (a ++ \<Uplus>\<^sub>m (M-{a}))" by simp
  have h9: "... = s ++ (a \<uplus>\<^sub>m \<Uplus>\<^sub>m (M-{a}))" using map_add_merge[of a "\<Uplus>\<^sub>m (M - {a})"]
    using Cons.prems(1) Cons.prems(2) x3 by fastforce
  have x1: "... = s ++ (\<Uplus>\<^sub>m M)" using x2 merge_Merge_diff[of a M]
    by (metis Cons.prems(2) DiffD1 DiffD2 insertI1 list.set_intros(1) merge_comm)
  then show ?case using h7 h8 h9 x1 by presburger
qed
*)
lemma seq_set_dom:
  "\<forall>i j. i < length ms \<and> j < length ms \<and> dom (ms!i) \<inter> dom (ms!j) \<noteq> {} \<longrightarrow> i = j \<Longrightarrow> 
  \<forall>m\<^sub>1 \<in> set ms.\<forall>m\<^sub>2 \<in> set ms. m\<^sub>1 \<noteq> m\<^sub>2 \<longrightarrow> dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
proof (induction ms)
  case Nil
  then show ?case by auto
next
  case (Cons a ms)
  then show ?case by (metis in_set_conv_nth)
qed

lemma map_add_seq_Merge: 
  "\<forall>i j. i < length ms \<and> j < length ms \<and> dom (ms!i) \<inter> dom (ms!j) \<noteq> {} \<longrightarrow> i = j 
  \<Longrightarrow> map_add_seq s ms = s ++ (\<Uplus>\<^sub>m set ms)"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a ms)
  have h0: "\<forall>k. k < length ms \<longrightarrow> ms ! k = (a # ms) ! (Suc k)" by simp
  have h1: "\<forall>i j. i < length ms \<and> j < length ms \<and> dom (ms!i) \<inter> dom (ms!j) \<noteq> {} \<longrightarrow> i = j"
  proof (clarify)
    fix i j
    assume a1: "i < length ms"
       and a2: "j < length ms"
       and a3: "dom (ms!i) \<inter> dom (ms!j) \<noteq> {}"
    then show "i = j"
      by (metis Cons.prems(1) Suc_leI h0 le_imp_less_Suc length_Cons old.nat.inject)
  qed
  have h2: "\<forall>m \<in> set ms. a \<noteq> m \<longrightarrow> dom a \<inter> dom m = {}" 
    by (meson Cons.prems(1) list.set_intros(1) list.set_intros(2) seq_set_dom)
  have h3: "a \<noteq> Map.empty \<Longrightarrow> a \<notin> set ms"
  proof -
    assume a4: "a \<noteq> Map.empty"
    hence a5: "dom a \<noteq> {}" by simp
    thus "a \<notin> set ms" using h0 Cons.prems(1) 
      by (metis Diff_Diff_Int Diff_cancel Diff_empty Suc_less_eq in_set_conv_nth length_Cons 
          nat.simps(3) nth_Cons_0 zero_less_Suc)
  qed
  have h3: "dom a \<inter> dom (\<Uplus>\<^sub>m set ms) = {}"
    using h2 h3 not_dom_Merge by fastforce
  have h4: "map_add_seq (s ++ a) ms = (s ++ a) ++ \<Uplus>\<^sub>m set ms" using Cons.IH card_length h1 by blast
  have h5: "... = s ++ (a ++ \<Uplus>\<^sub>m set ms)" by simp
  have h6: "... = s ++ (a \<uplus>\<^sub>m \<Uplus>\<^sub>m set ms)" using map_add_merge[of a "\<Uplus>\<^sub>m set ms"] by (simp add: h3)
  have h7: "... = s ++ (\<Uplus>\<^sub>m (set ms \<union> {a}))" 
    using h2 h3 map_add_merge not_dom_Merge merge_Merge_union[of "set ms" a]
    by (smt (verit) DiffD1 DiffD2 DiffI Diff_empty Diff_insert_absorb Int_commute 
        Int_empty_right Un_empty_right disjoint_iff_not_equal domIff insert_Diff insert_Diff_single 
        map_add_dom_app_simps(1) merge_Merge_diff merge_comm mk_disjoint_insert)
  then show ?case by (metis h4 h5 h6 insert_is_Un list.simps(15) map_add_seq.simps(2) sup_commute)
qed

definition map_add_all where "map_add_all ms = map_add_seq Map.empty ms"

lemma add_all: "\<forall>i j. i < length ms \<and> j < length ms \<and>dom (ms!i) \<inter> dom (ms!j) \<noteq> {} \<longrightarrow> i = j 
    \<Longrightarrow> map_add_all ms = \<Uplus>\<^sub>m set ms"
  using map_add_seq_Merge[of ms Map.empty]
  by (simp add: map_add_all_def)

lemma add_all_empty[simp]: "map_add_all [] = Map.empty"
  by (simp add: map_add_all_def)

lemma add_all_left: "m ++ map_add_all ms = map_add_all (m#ms)"
proof (induction ms arbitrary: m)
  case Nil
  then show ?case by (simp add: map_add_all_def)
next
  case (Cons a ms)
  then show ?case by (metis map_add_all_def map_add_assoc map_add_seq.simps(2))
qed

fun map_Add_seq where
  "map_Add_seq S [] = S"
| "map_Add_seq S (M#Ms) = map_Add_seq (S ** M) Ms"

lemma map_Add_seq_foldl: "map_Add_seq S Ms = foldl map_Add S Ms"
proof (induction Ms arbitrary: S)
  case Nil
  then show ?case by fastforce
next
  case (Cons a ms)
  then show ?case by simp
qed

fun map_seq_in where
  "map_seq_in [] [] = True"
| "map_seq_in (x#xs) (X#XS) = (x \<in> X \<and> map_seq_in xs XS)"
| "map_seq_in _ _ = False"

lemma map_seq_in_ex: "\<lbrakk> m \<in> set ms; map_seq_in ms Ms \<rbrakk> \<Longrightarrow> \<exists>M \<in> set Ms. m \<in> M"
proof (induction Ms arbitrary: ms)
  case Nil
  then show ?case using map_seq_in.elims(2) by force
next
  case (Cons a ms)
  then show ?case by (metis list.set_cases list.set_intros(1) list.set_intros(2) map_seq_in.simps(2))
qed

lemma map_seq_in_length: "map_seq_in ms Ms \<Longrightarrow> length ms = length Ms"
proof (induction Ms arbitrary: ms)
  case Nil
  then show ?case using map_seq_in.elims(2) by auto
next
  case (Cons a Ms)
  then show ?case using map_seq_in.elims(2) by force
qed

lemma map_seq_in_index: "\<lbrakk>map_seq_in ms Ms; i < length Ms\<rbrakk> \<Longrightarrow> ms ! i \<in> Ms ! i"
proof (induction Ms arbitrary: ms i)
  case Nil
  then show ?case by simp
next
  case (Cons a Ms)
  have h1: "map_seq_in (tl ms) Ms"
    by (metis Cons.prems(1) list.exhaust_sel map_seq_in.simps(2) map_seq_in.simps(4))
  show ?case
  proof (cases "i = 0")
    case True
    then show ?thesis using Cons.prems(1) map_seq_in.elims(2) by fastforce
  next
    case False
    obtain j where j1: "Suc j = i" by (metis False old.nat.exhaust)
    hence h2: "j < length Ms" using Cons.prems(2) by force
    hence h3: "(tl ms) ! j \<in> Ms ! j" by (simp add: Cons.IH h1)
    then show ?thesis
      by (metis Cons.prems(1) j1 list.exhaust_sel map_seq_in.simps(4) nth_Cons_Suc)
  qed
qed

definition map_seq_of where
  "map_seq_of ms Ms \<equiv> map_seq_in ms Ms \<and> 
    (\<forall>i j. i < length ms \<and> j < length ms \<and> dom (ms!i) \<inter> dom (ms!j) \<noteq> {} \<longrightarrow> i = j) \<and> 
    (\<forall>M \<in> set Ms.\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 = dom m\<^sub>2)"

lemma map_seq_of_empty[simp]: "map_seq_of ms [] \<Longrightarrow> ms = []"
  using map_seq_in.elims(2) map_seq_of_def by blast

lemma map_seq_of_wk: "map_seq_of ms Ms \<Longrightarrow> map_seq_in ms Ms"
  using map_seq_of_def by blast

lemma map_seq_of_in: 
  "\<lbrakk> map_seq_of ms Ms;
     m\<^sub>1 \<in> set ms;
     m\<^sub>2 \<in> set ms;
     m\<^sub>1 \<noteq> m\<^sub>2 \<rbrakk> \<Longrightarrow> \<exists>M\<^sub>1 \<in> set Ms.\<exists>M\<^sub>2 \<in> set Ms. M\<^sub>1 \<noteq> M\<^sub>2 \<and> m\<^sub>1 \<in> M\<^sub>1 \<and> m\<^sub>2 \<in> M\<^sub>2"
proof (induction Ms arbitrary: ms)
  case Nil
  then show ?case
    unfolding map_seq_of_def by (metis empty_iff list.collapse map_seq_in.simps(3) set_empty)
next
  case (Cons a Ms)
  hence h0: "\<forall>k. k \<le> length (tl ms) \<longrightarrow> (tl ms) ! k = ms ! (Suc k)"
    unfolding map_seq_of_def apply clarify 
    by (metis equals0D hd_Cons_tl list.set(1) nth_Cons_Suc)  
  then have h1: "\<forall>i j. i < length (tl ms) \<and> j < length (tl ms) \<and> dom ((tl ms)!i) \<inter> dom ((tl ms)!j) \<noteq> {} \<longrightarrow> i = j"
    using Cons.prems unfolding map_seq_of_def apply clarify 
    by (metis Nitpick.size_list_simp(2) Suc_inject Suc_leI le_imp_less_Suc length_greater_0_conv 
        length_pos_if_in_set nth_tl)
  have h2: "\<forall>M\<in>set Ms. \<forall>m\<^sub>1\<in>M. \<forall>m\<^sub>2\<in>M. dom m\<^sub>1 = dom m\<^sub>2"
    using Cons.prems unfolding map_seq_of_def apply clarify by (meson list.set_intros(2))
  have h4: "map_seq_in (tl ms) Ms" using Cons.prems unfolding map_seq_of_def apply clarify
    by (metis length_greater_0_conv length_pos_if_in_set list.exhaust_sel map_seq_in.simps(2))
  have h5: "m\<^sub>1 \<noteq> m\<^sub>2" by (simp add: Cons.prems)
  then show ?case
  proof (cases "m\<^sub>1 \<in> set (tl ms)")
    case True
    hence h6: "m\<^sub>1 \<in> set (tl ms)" by simp
    then show ?thesis
    proof (cases "m\<^sub>2 \<in> set (tl ms)")
      case True
      hence h7: "m\<^sub>2 \<in> set (tl ms)" by simp
      have "\<exists>M\<^sub>1\<in>set Ms. \<exists>M\<^sub>2\<in>set Ms. M\<^sub>1 \<noteq> M\<^sub>2 \<and> m\<^sub>1 \<in> M\<^sub>1 \<and> m\<^sub>2 \<in> M\<^sub>2"
        using Cons.IH Cons.prems(4) h1 h2 h4 h6 h7 unfolding map_seq_of_def
        by (smt (verit, best) card_length)
      then show ?thesis by (meson list.set_intros(2))
    next
      case False
      hence h7: "m\<^sub>2 \<notin> set (tl ms)" by simp
      hence x1: "m\<^sub>2 \<in> a"
        using Cons.prems(1) Cons.prems(3) list.set_cases
        unfolding map_seq_of_def apply clarify by fastforce
      obtain M where "m\<^sub>1 \<in> M" and "M \<in> set Ms" by (meson h4 h6 map_seq_in_ex)
      then show ?thesis
        using Cons.prems(1) Cons.prems(2) Cons.prems(3) h5 x1 
        unfolding map_seq_of_def apply clarify
        by (smt (verit) dom_eq_empty_conv in_set_conv_nth inf.idem map_seq_in_ex)
    qed
  next
    case False
    hence h6: "m\<^sub>1 \<notin> set (tl ms)" by simp
    hence x1: "m\<^sub>1 \<in> a" using Cons.prems(1) Cons.prems(2) unfolding map_seq_of_def apply clarify
      using list.set_cases by fastforce
    then show ?thesis
    proof (cases "m\<^sub>2 \<in> set (tl ms)")
      case True
      hence h7: "m\<^sub>2 \<in> set (tl ms)" by simp
      then show ?thesis
        using Cons.prems(1) Cons.prems(2) Cons.prems(3) h5 unfolding map_seq_of_def apply clarify
        by (smt (verit, best) dom_eq_empty_conv in_set_conv_nth inf.idem map_seq_in_ex)
    next
      case False
      then show ?thesis
        by (metis Cons.prems(2) Cons.prems(3) h5 h6 list.exhaust_sel set_ConsD tl_Nil)
    qed
  qed
qed

lemma map_Add_seq_as_add_seq: 
  "map_Add_seq S Ms = {map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms Ms}"
proof (induction Ms arbitrary: S)
  case Nil
  then show ?case
  proof
    show "map_Add_seq S [] \<subseteq> {map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms []}"
    proof
      fix x
      assume "x \<in> map_Add_seq S []"
      then show "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms []}"
        apply simp
        by (metis map_add_seq.simps(1) map_seq_in.simps(1))
    qed
  next
    show "{map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms []} \<subseteq> map_Add_seq S []"
    proof
      fix x
      assume "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms []}"
      then show "x \<in> map_Add_seq S []"
        apply simp
        using map_seq_in.elims(1) by force
    qed
  qed
next
  case (Cons A Ms)
  have h1: "map_Add_seq (S ** A) Ms = {map_add_seq s ms | s ms. s \<in> (S ** A) \<and> map_seq_in ms Ms}"
    using local.Cons by blast
  show ?case
  proof
    show "map_Add_seq S (A#Ms) \<subseteq> {map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms (A#Ms)}"
    proof
      fix x
      assume a1: "x \<in> map_Add_seq S (A # Ms)"
      hence a2: "x \<in> map_Add_seq (S ** A) Ms" by simp
      obtain s a ms where p1: "s \<in> S" and
                          p2: "a \<in> A" and
                          p3: "map_seq_in ms Ms" and 
                          p4: "x = map_add_seq (s ++ a) ms"
        by (smt (verit, ccfv_SIG) a2 h1 map_Add_def mem_Collect_eq)
      have a3: "map_seq_in (a#ms) (A#Ms)" by (simp add: p2 p3)
      then show "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms (A # Ms)}"
        by (smt (verit) map_add_seq.simps(2) mem_Collect_eq p1 p4)
    qed
  next
    show "{map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms (A#Ms)} \<subseteq> map_Add_seq S (A#Ms)"
    proof
      fix x
      assume a4: "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms (A # Ms)}"
      then obtain s a ms where q1: "s \<in> S" and
                               q2: "a \<in> A" and
                               q3: "map_seq_in ms Ms" and
                               q4: "x = map_add_seq s (a#ms)" 
        by (smt (verit, del_insts) CollectD list.discI list.sel(1) list.sel(3) map_seq_in.elims(2))
      show "x \<in> map_Add_seq S (A # Ms)" 
        using h1 map_Add_def q1 q2 q3 q4 by fastforce
    qed
  qed
qed

definition Dom where "Dom X \<equiv> \<Union>x\<in>X. (dom x)"

lemma Dom_single: assumes "\<exists>y. P y" shows "Dom { [a \<mapsto> y] | y. P y } = {a}"
proof
  show "Dom {[a \<mapsto> y] |y. P y} \<subseteq> {a}"
    unfolding Dom_def dom_def apply (simp; clarify) using domIff by fastforce
next
  show "{a} \<subseteq> Dom {[a \<mapsto> y] |y. P y}"
    using assms unfolding Dom_def dom_def apply (simp; clarify) by fastforce
qed

definition seq_of_maps where
  "seq_of_maps Ms \<equiv> 
    (\<forall>i j. i < length Ms \<and> j < length Ms \<and> Dom (Ms!i) \<inter> Dom (Ms!j) \<noteq> {} \<longrightarrow> i = j) \<and>
    (\<forall>M \<in> set Ms.\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 = dom m\<^sub>2)"

lemma seq_of_maps_hd: assumes "seq_of_maps (M#Ms)" shows "seq_of_maps Ms"
proof -
  have h0: "\<forall>k. k < length Ms \<longrightarrow> Ms ! k = (M#Ms) ! (Suc k)"
    by simp
  thus ?thesis using assms unfolding seq_of_maps_def apply clarify
    by (metis Suc_inject Suc_leI le_imp_less_Suc length_Cons list.set_intros(2))
qed

lemma maps_seq_of: 
  assumes M1: "seq_of_maps Ms"
      and M2: "map_seq_in ms Ms"
    shows "map_seq_of ms Ms"
proof -
  have h1: "map_seq_in ms Ms" by (simp add: M2)
  have h2: "\<forall>i j. i < length ms \<and> j < length ms \<and> dom (ms ! i) \<inter> dom (ms ! j) \<noteq> {} \<longrightarrow> i = j"
  proof clarify
    fix i j
    assume a1: "i < length ms"
       and a2: "j < length ms"
       and a3: "dom (ms ! i) \<inter> dom (ms ! j) \<noteq> {}"
    have k1: "ms ! i \<in> Ms ! i" by (metis a1 h1 map_seq_in_index map_seq_in_length)
    have k2: "ms ! j \<in> Ms ! j" by (metis a2 h1 map_seq_in_index map_seq_in_length)
    obtain x where x1: "x \<in> dom (ms ! i)" and x2: "x \<in> dom (ms ! j)" using a3 by blast
    have k3: "x \<in> Dom (Ms!i)" using k1 x1 unfolding Merge_def Dom_def apply clarify by blast
    have k4: "x \<in> Dom (Ms!j)" using k2 x2 unfolding Merge_def Dom_def apply clarify by blast
    have k5: "Dom (Ms!i) \<inter> Dom (Ms!j) \<noteq> {}" using k3 k4 by blast
    show "i = j" using M1 unfolding seq_of_maps_def by (metis a1 a2 h1 k5 map_seq_in_length)
  qed
  have h3: "\<forall>M\<in>set Ms. \<forall>m\<^sub>1\<in>M. \<forall>m\<^sub>2\<in>M. dom m\<^sub>1 = dom m\<^sub>2" by (metis M1 seq_of_maps_def)
  have h4: "card (set Ms) \<le> length Ms" by (simp add: card_length)
  show ?thesis using h1 h2 h3 h4 unfolding map_seq_of_def by blast
qed

lemma map_add_shift: "M ** {map_add_all ms | ms. map_seq_in ms Ms} = {map_add_all ms | ms. map_seq_in ms (M#Ms)}"
proof
  show "M ** {map_add_all ms |ms. map_seq_in ms Ms} \<subseteq> {map_add_all ms |ms. map_seq_in ms (M # Ms)}"
  proof
    fix x
    assume a1: "x \<in> M ** {map_add_all ms |ms. map_seq_in ms Ms}"
    then obtain m ms where m1: "m \<in> M" and m2: "map_seq_in ms Ms" and m3: "x = m ++ map_add_all ms"
      unfolding map_Add_def by blast
    have "x = map_add_all (m#ms)" by (simp add: add_all_left m3)
    then show "x \<in> {map_add_all ms |ms. map_seq_in ms (M # Ms)}" using m1 m2 by fastforce
  qed
next
  show "{map_add_all ms |ms. map_seq_in ms (M # Ms)} \<subseteq> M ** {map_add_all ms |ms. map_seq_in ms Ms}"
  proof
    fix x
    assume a1: "x \<in> {map_add_all ms |ms. map_seq_in ms (M # Ms)}"
    then obtain m ms where m1: "m \<in> M" and m2: "map_seq_in (m#ms) (M # Ms)" and m3: "x = map_add_all (m#ms)"
      apply (simp; clarify) by (metis map_seq_in.elims(2) map_seq_in.simps(2) map_seq_in.simps(4))
    have h1: "map_seq_in ms Ms" using m2 by force
    have h2: "x = m ++ map_add_all ms" by (simp add: add_all_left m3)
    show "x \<in> M ** {map_add_all ms |ms. map_seq_in ms Ms}" 
      unfolding map_Add_def using h1 h2 m1 by blast
  qed
qed

lemma map_add_seq_of_shift: 
  assumes "seq_of_maps (M#Ms)"
  shows "M ** {map_add_all ms | ms. map_seq_of ms Ms} = {map_add_all ms | ms. map_seq_of ms (M#Ms)}"
proof
  show "M ** {map_add_all ms |ms. map_seq_of ms Ms} \<subseteq> {map_add_all ms |ms. map_seq_of ms (M # Ms)}"
  proof
    fix x
    assume a1: "x \<in> M ** {map_add_all ms |ms. map_seq_of ms Ms}"
    then obtain m ms where m1: "m \<in> M" and m2: "map_seq_of ms Ms" and m3: "x = m ++ map_add_all ms"
      unfolding map_Add_def by blast
    have h1: "x = map_add_all (m#ms)" by (simp add: add_all_left m3)
    have h2: "map_seq_of (m#ms) (M # Ms)"
      by (metis assms m1 m2 map_seq_in.simps(2) map_seq_of_def maps_seq_of)
    show "x \<in> {map_add_all ms |ms. map_seq_of ms (M # Ms)}" using h1 h2 by blast
  qed
next
  show "{map_add_all ms |ms. map_seq_of ms (M # Ms)} \<subseteq> M ** {map_add_all ms |ms. map_seq_of ms Ms}"
  proof
    fix x
    assume a1: "x \<in> {map_add_all ms |ms. map_seq_of ms (M # Ms)}"
    then obtain m ms where m1: "m \<in> M" and m2: "map_seq_of (m#ms) (M # Ms)" and m3: "x = map_add_all (m#ms)"
      apply (simp; clarify) using map_seq_in.elims(2) map_seq_of_def by blast
    have h1: "map_seq_of ms Ms" using m2
      by (metis assms map_seq_in.simps(2) map_seq_of_def maps_seq_of seq_of_maps_hd)
    have h2: "x = m ++ map_add_all ms" by (simp add: add_all_left m3)
    show "x \<in> M ** {map_add_all ms |ms. map_seq_of ms Ms}"
      using h1 h2 m1 map_Add_def by fastforce
  qed
qed

lemma map_Add_seq_all: "seq_of_maps Ms \<Longrightarrow> map_Add_seq S Ms = S ** {map_add_all ms | ms. map_seq_of ms Ms}"
proof (induction Ms arbitrary: S)
  case Nil
  have h1: "map_Add_seq S [] = S" by simp
  have "{map_add_all ms | ms. map_seq_of ms []} = {Map.empty}"
  proof
    show "{map_add_all ms |ms. map_seq_of ms []} \<subseteq> {Map.empty}"
      using map_seq_of_empty by fastforce
  next
    show "{Map.empty} \<subseteq> {map_add_all ms |ms. map_seq_of ms []}"
      apply (simp add: map_add_all_def)
      by (metis emptyE empty_set less_nat_zero_code list.size(3) map_add_seq.simps(1)
          map_seq_in.simps(1) map_seq_of_def)
  qed
  hence "S = S ** {map_add_all ms | ms. map_seq_of ms []}" by (metis map_Add_unit_right)
  then show ?case using h1 by blast
next
  case (Cons a Ms)
  have h1: "map_Add_seq (S ** a) Ms = (S ** a) ** {map_add_all ms | ms. map_seq_of ms Ms}" 
    using local.Cons seq_of_maps_hd by blast
  have h2: "... = S ** (a ** {map_add_all ms | ms. map_seq_of ms Ms})" by (simp add: map_Add_assoc)
  have h3: "... = S ** {map_add_all ms | ms. map_seq_of ms (a#Ms)}"
    by (simp add: Cons.prems map_add_seq_of_shift)
  then show ?case by (simp add: h1 h2)
qed
  

lemma map_Add_seq_Merge: 
  assumes "seq_of_maps Ms" 
  shows "map_Add_seq S Ms = S ** {\<Uplus>\<^sub>m set ms | ms. map_seq_of ms Ms}"
proof
  show "map_Add_seq S Ms \<subseteq> S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_of ms Ms}"
  proof
    fix x
    assume a1: "x \<in> map_Add_seq S Ms"
    hence h1: "x \<in> S ** {map_add_all ms | ms. map_seq_of ms Ms}" using assms map_Add_seq_all by blast
    then obtain s ms where s1: "s \<in> S" and s2: "map_seq_of ms Ms" and s3: "x = s ++ map_add_all ms"
      unfolding map_Add_def by blast
    have h2: "map_add_all ms = \<Uplus>\<^sub>m set ms" using s2 add_all[of ms] unfolding map_seq_of_def
      by (meson card_length)
    show "x \<in> S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_of ms Ms}" using h2 map_Add_def s1 s2 s3 by fastforce
  qed
next
  show "S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_of ms Ms} \<subseteq> map_Add_seq S Ms"
  proof
    fix x
    assume a1: "x \<in> S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_of ms Ms}"
    then show "x \<in> map_Add_seq S Ms" using assms add_all map_Add_seq_all[of Ms S] unfolding map_seq_of_def
      by (smt (verit) Collect_cong card_length)
  qed
qed

subsection "State Pair Sequences"

fun map_add_seq_pair where
  "map_add_seq_pair (s\<^sub>1, s\<^sub>2) [] = (s\<^sub>1, s\<^sub>2)"
| "map_add_seq_pair (s\<^sub>1, s\<^sub>2) ((m\<^sub>1, m\<^sub>2)#ms) = map_add_seq_pair (s\<^sub>1 ++ m\<^sub>1, s\<^sub>2 ++ m\<^sub>2) ms"

lemma map_add_seq_zip:
  "\<lbrakk>length ms = length ns; xs = zip ms ns \<rbrakk> \<Longrightarrow> map_add_seq_pair (s\<^sub>1, s\<^sub>2) xs = (map_add_seq s\<^sub>1 ms, map_add_seq s\<^sub>2 ns)"
proof (induction xs arbitrary: s\<^sub>1 s\<^sub>2 ms ns)
  case Nil
  then show ?case by force
next
  case (Cons a xs)
  then obtain a\<^sub>1 a\<^sub>2 where p1: "a = (a\<^sub>1, a\<^sub>2)" using old.prod.exhaust by blast
  obtain ms' where p2: "ms = a\<^sub>1#ms'" by (metis Cons.prems(2) p1 prod.inject zip_eq_ConsE)
  obtain ns' where p3: "ns = a\<^sub>2#ns'" by (metis Cons.prems(2) p1 prod.inject zip_eq_ConsE)
  have "map_add_seq_pair (s\<^sub>1, s\<^sub>2) (a#xs) = map_add_seq_pair (s\<^sub>1 ++ a\<^sub>1, s\<^sub>2 ++ a\<^sub>2) xs" by (simp add: p1)
  then show ?case using Cons.IH Cons.prems(1) Cons.prems(2) p2 p3 by force
qed

lemma map_add_seq_Merge_pair:
  assumes dM: "\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
      and dN: "\<forall>n\<^sub>1 \<in> N.\<forall>n\<^sub>2 \<in> N. dom n\<^sub>1 \<inter> dom n\<^sub>2 = {}"
      and sM: "M = set ms"
      and sN: "N = set ns"
      and cM: "card M = length ms"
      and cN: "card N = length ns"
      and cC: "card M = card N"
    shows "map_add_seq_pair (sm, sn) (zip ms ns) = (sm ++ (\<Uplus>\<^sub>m M), sn ++ (\<Uplus>\<^sub>m N))"
  using assms by (metis map_add_seq_Merge map_add_seq_zip nth_mem)

lemma map_update_merge:
  assumes d: "a \<notin> dom m"
  shows "[a\<mapsto>b] ++ m = [a\<mapsto>b] \<uplus>\<^sub>m m"
  by (simp add: d map_add_merge)

subsection "Indexed State and State Update Sequences"

fun map_upd_seq where 
  "map_upd_seq f s [] = s"
| "map_upd_seq f s (m#ms) = map_upd_seq f (s(m\<mapsto>f m)) ms"

lemma map_upd_seq_foldl: "map_upd_seq f s ms = foldl (\<lambda>s a. s(a\<mapsto>f a)) s ms"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by fastforce
next
  case (Cons a ms)
  then show ?case by simp
qed

lemma map_upd_seq_add: "map_upd_seq f s ms = map_add_seq s (map (\<lambda>a. [a\<mapsto>f a]) ms)"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a ms)
  have "map_upd_seq f (s(a\<mapsto>f a)) ms = map_add_seq (s(a\<mapsto>f a)) (map (\<lambda>a. [a \<mapsto> f a]) ms)"
    using local.Cons by blast
  then show ?case unfolding map_upd_seq_foldl
    by (smt (verit, best) foldl_Cons list.distinct(1) list.inject list.simps(9) 
        map_add_seq.elims singleton_map_upd)
qed

lemma map_upd_Merge:
  assumes c: "card (set xs) = length xs"
    shows "map_upd_seq f s xs = s ++ (\<Uplus>\<^sub>m { [x \<mapsto> f x] | x. x \<in> set xs })"
proof -
  have h0: "map_upd_seq f s xs = map_add_seq s (map (\<lambda>a. [a \<mapsto> f a]) xs)"
  proof (induction xs arbitrary: s)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case using map_upd_seq_add by blast
  qed
  have h4: "set (map (\<lambda>a. [a \<mapsto> f a]) xs) = { [x \<mapsto> f x] | x. x \<in> set xs }"
  proof (induction xs)
    case Nil
    then show ?case by force
  next
    case (Cons a xs)
    have x1: "set (map (\<lambda>a. [a \<mapsto> f a]) (a#xs)) \<subseteq> { [x \<mapsto> f x] | x. x \<in> set (a#xs) }"
    proof
      fix x
      assume a1: "x \<in> set (map (\<lambda>a. [a \<mapsto> f a]) (a # xs))"
      show "x \<in> {[x \<mapsto> f x] |x. x \<in> set (a # xs)}" using a1 by auto
    qed
    have x2: "{ [x \<mapsto> f x] | x. x \<in> set (a#xs) } \<subseteq> set (map (\<lambda>a. [a \<mapsto> f a]) (a#xs))"
    proof
      fix x
      assume a1: "x \<in> {[x \<mapsto> f x] |x. x \<in> set (a # xs)}"
      show "x \<in> set (map (\<lambda>a. [a \<mapsto> f a]) (a # xs))" using a1 by auto
    qed
    show ?case using x1 x2 by blast
  qed
  obtain ms where ms1: "ms = map (\<lambda>a. [a \<mapsto> f a]) xs" by blast
  have h1: "\<forall>i j. i < length ms \<and> j < length ms \<and> dom (ms!i) \<inter> dom (ms!j) \<noteq> {} \<longrightarrow> i = j"
    using c apply (simp add: ms1 singleton_unfold; clarify)
    by (smt (verit, best) card_distinct disjoint_iff domIff nth_eq_iff_index_eq nth_map)
  hence h2: "map_add_seq s ms = s ++ (\<Uplus>\<^sub>m set ms)" by (simp add: map_add_seq_Merge)
  hence h3: "... = s ++ (\<Uplus>\<^sub>m { [x \<mapsto> f x] | x. x \<in> set xs })" using h4 ms1 by presburger
  show ?thesis using h0 h2 h4 ms1 by auto    
qed

subsection "Indexed Sequences of State Sets"

fun map_Upd_seq where
  "map_Upd_seq f S [] = S"
| "map_Upd_seq f S (m#ms) = map_Upd_seq f { s(m\<mapsto>x) |s x. s \<in> S \<and> x \<in> f m } ms"

definition maps_of where "maps_of f x = { [x \<mapsto> y] | y. y \<in> f x }"

lemma map_maps_hd: "map (maps_of f) (x#xs) = { [x \<mapsto> y] | y. y \<in> f x }#map (maps_of f) xs"
  by (simp add: maps_of_def)

lemma Dom_maps_of:"Dom (\<Union> (set (map (maps_of f) xs))) \<subseteq> set xs"
proof (induction xs)
  case Nil
  then show ?case unfolding Dom_def dom_def maps_of_def by (simp; clarify)
next
  case (Cons a xs)
  then show ?case unfolding Dom_def dom_def maps_of_def apply simp by fastforce
qed

lemma Dom_maps_of_inner:"\<forall>x \<in> set xs. f x \<noteq> {} \<Longrightarrow> Dom (\<Union> (set (map (maps_of f) xs))) = set xs"
proof (induction xs)
  case Nil
  then show ?case using Dom_def by fastforce
next
  case (Cons a xs)
  have h1: "Dom (\<Union> (set (map (maps_of f) xs))) = set xs" using Cons.IH Cons.prems by force
  have h2: "Dom (\<Union> (set (map (maps_of f) (a # xs)))) = 
      Dom (\<Union> (set ({ [a \<mapsto> y] | y. y \<in> f a }#map (maps_of f) xs)))"
    by (metis map_maps_hd)
  have h3: "... = Dom (\<Union> ({{ [a \<mapsto> y] | y. y \<in> f a }} \<union> set (map (maps_of f) xs)))" by force
  have h4: "... = Dom ({ [a \<mapsto> y] | y. y \<in> f a } \<union> \<Union> (set (map (maps_of f) xs)))" by force
  have h5: "... = {a} \<union> Dom (\<Union> (set (map (maps_of f) xs)))" 
    unfolding Dom_def dom_def apply simp apply (rule antisym)
    using SUP_le_iff apply fastforce
    apply (simp; clarify)
    by (metis Cons.prems ex_in_conv fun_upd_same list.set_intros(1))
  then show ?case using h1 h2 by force
qed

lemma Dom_maps_of_outer:"\<lbrakk> \<forall>x \<in> set xs. f x \<noteq> {}; k < length xs \<rbrakk> \<Longrightarrow> Dom ((map (maps_of f) xs)!k) \<subseteq> set xs"
proof (induction xs arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
    then show ?case
    proof (cases "k = 0")
      case True
      have h1: "Dom (map (maps_of f) (a # xs) ! k) = Dom (({ [a \<mapsto> y] | y. y \<in> f a }#map (maps_of f) xs) ! k)"
        by (metis map_maps_hd)
      have h2: "... = Dom ({ [a \<mapsto> y] | y. y \<in> f a })" by (simp add: True)
      have h3: "... = {a}" using Cons.prems(1) by (simp add: Dom_single ex_in_conv)
      then show ?thesis using h1 h2 by force
    next
      case False
      have h1: "Dom (map (maps_of f) (a # xs) ! k) = Dom (({ [a \<mapsto> y] | y. y \<in> f a }#map (maps_of f) xs) ! k)"
        by (metis map_maps_hd)
      have h2: "... = Dom ((map (maps_of f) xs) ! (k-1))"
        by (simp add: False zero_less_iff_neq_zero)
      then show ?thesis
        using Cons.IH Cons.prems(1) Cons.prems(2) False apply (simp; clarify)
        by (metis Suc_less_eq Suc_pred subsetD)
    qed
qed

lemma Dom_maps_of_diff:"\<lbrakk> card (set xs) = length xs; \<forall>x \<in> set xs. f x \<noteq> {}; i < length xs; j < length xs; 
  i \<noteq> j \<rbrakk> \<Longrightarrow> Dom ((map (maps_of f) xs)!i) \<inter> Dom ((map (maps_of f) xs)!j) = {}"
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases "i = 0")
    case True
    hence h1: "Dom (map (maps_of f) (a # xs) ! i) = {a}"
      unfolding Dom_def dom_def maps_of_def apply simp apply (rule antisym)
      apply clarify 
       apply (metis option.distinct(1) singleton_unfold)
      apply clarify using Cons.prems(2) by auto
    have h2: "j > 0" using Cons.prems(5) True by force
    hence h3: "Dom (map (maps_of f) (a # xs) ! j) = Dom (({ [a \<mapsto> y] | y. y \<in> f a }#map (maps_of f) xs) ! j)"
      by simp
    have h4: "... = Dom (map (maps_of f) xs ! (j-1))" using h2 by force
    have h5: "... \<subseteq> set xs"
      using h2
      by (metis Cons.prems(2) Cons.prems(4) Dom_maps_of_outer One_nat_def Suc_less_eq Suc_pred 
          length_Cons set_subset_Cons subsetD)
    then show ?thesis
      by (metis Cons.prems(1) Int_insert_left_if0 card_distinct distinct.simps(2) h1 h3 h4 
          inf_bot_left subsetD)
  next
    case False
    hence h0: "i > 0" by simp
    then show ?thesis
    proof (cases "j = 0")
      case True
    hence h1: "Dom (map (maps_of f) (a # xs) ! j) = {a}"
      unfolding Dom_def dom_def maps_of_def apply simp apply (rule antisym)
      apply clarify 
       apply (metis option.distinct(1) singleton_unfold)
      apply clarify using Cons.prems(2) by auto
    have h2: "Dom (map (maps_of f) (a # xs) ! i) = Dom (({ [a \<mapsto> y] | y. y \<in> f a }#map (maps_of f) xs) ! i)"
      by (metis map_maps_hd)
    have h4: "... = Dom (map (maps_of f) xs ! (i-1))" using h1 False by force
    have h5: "... \<subseteq> set xs"
      by (metis Cons.prems(2) Cons.prems(3) Dom_maps_of_outer False One_nat_def Suc_less_eq 
          Suc_pred bot_nat_0.not_eq_extremum length_Cons set_subset_Cons subset_iff)
      then show ?thesis
        by (metis Cons.prems(1) Int_insert_right card_distinct distinct.simps(2) h1 h2 h4 inf_bot_right subsetD)
    next
      case False
      have h6: "Dom (map (maps_of f) (a # xs) ! i) = Dom (({ [a \<mapsto> y] | y. y \<in> f a }#map (maps_of f) xs) ! i)"
        by (simp add: maps_of_def)
      have i6: "... = Dom (map (maps_of f) xs ! (i-1))" by (simp add: h0)
      have h7: "Dom (map (maps_of f) (a # xs) ! j) = Dom (({ [a \<mapsto> y] | y. y \<in> f a }#map (maps_of f) xs) ! j)"
        by (simp add: maps_of_def)
      have i7: "... = Dom (map (maps_of f) xs ! (j-1))" by (simp add: False zero_less_iff_neq_zero)
      have x1: "i-1 < length xs" using Cons.prems(3) h0 by auto
      have x2: "j-1 < length xs" using Cons.prems(4) False by force
      have x3: "i-1 \<noteq> j-1" by (metis Cons.prems(5) False Suc_pred' gr_zeroI h0)
      have x4: "Dom (map (maps_of f) xs ! (i-1)) \<inter> Dom (map (maps_of f) xs ! (j-1)) = {}"
        by (metis Cons.IH Cons.prems(1) Cons.prems(2) card_distinct distinct.simps(2) distinct_card 
            list.set_intros(2) x1 x2 x3)
      then show ?thesis using h6 h7 i6 i7 by blast
    qed
  qed
qed

lemma map_Upd_seq_comp: "map_Upd_seq f (map_Upd_seq f S xs) ys = map_Upd_seq f S (xs @ ys)"
proof (induction xs arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

lemma map_Upd_comp_mono: "S \<subseteq> T \<Longrightarrow> map_Upd_seq f S xs \<subseteq> map_Upd_seq f T xs"
proof (induction xs arbitrary: S T)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof
    fix x
    assume "x \<in> map_Upd_seq f S (a # xs)"
    hence "x \<in> map_Upd_seq f {s(a \<mapsto> x) |s x. s \<in> S \<and> x \<in> f a} xs"
      by simp
    hence "x \<in> map_Upd_seq f {s(a \<mapsto> x) |s x. s \<in> T \<and> x \<in> f a} xs"
      using Cons.IH[of "{s(a \<mapsto> x) |s x. s \<in> S \<and> x \<in> f a}" "{s(a \<mapsto> x) |s x. s \<in> T \<and> x \<in> f a}"] Cons.prems by blast
    then show "x \<in> map_Upd_seq f T (a # xs)" using Cons.prems Cons.IH by simp
  qed
qed


lemma map_Upd_seq_comp_in: "\<lbrakk>x \<in> (map_Upd_seq f S xs); y \<in> map_Upd_seq f {x} ys\<rbrakk> \<Longrightarrow> y \<in> map_Upd_seq f S (xs @ ys)"
proof (induction xs arbitrary: S)
  case Nil
  then show ?case
    by (metis (no_types, opaque_lifting) empty_subsetI in_mono insert_subsetI map_Upd_comp_mono map_Upd_seq_comp)
next
  case (Cons a xs)
  then show ?case by simp
qed

lemma map_Upd_one: "map_Upd_seq f {a} [m] = { a(m\<mapsto>x) |x. x \<in> f m }" by force

lemma map_Upd_Add:
  assumes c: "card (set xs) = length xs"
  shows "map_Upd_seq f S xs = map_Add_seq S (map (maps_of f) xs)"
proof (induction xs arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have h1: "map_Upd_seq f (S ** { [a \<mapsto> y] | y. y \<in> f a }) xs = 
        map_Add_seq (S ** { [a \<mapsto> y] | y. y \<in> f a }) (map (maps_of f) xs)" using local.Cons by blast
  have h2: "map_Upd_seq f S (a # xs) = map_Upd_seq f { s(a\<mapsto>y) |s y. s \<in> S \<and> y \<in> f a } xs" by simp
  have h3: "{ s(a\<mapsto>y) |s y. s \<in> S \<and> y \<in> f a } = S ** { [a \<mapsto> y] | y. y \<in> f a }"
  proof
    show "{s(a \<mapsto> y) |s y. s \<in> S \<and> y \<in> f a} \<subseteq> S ** {[a \<mapsto> y] |y. y \<in> f a}"
      apply (simp add: map_Add_def; clarify) by force
  next 
    show "S ** {[a \<mapsto> y] |y. y \<in> f a} \<subseteq> {s(a \<mapsto> y) |s y. s \<in> S \<and> y \<in> f a}" 
      apply (simp add: map_Add_def; clarify) by auto
  qed
  have h4: "map_Add_seq (S ** { [a \<mapsto> y] | y. y \<in> f a }) (map (maps_of f) xs) = 
        map_Add_seq S (map (maps_of f) (a # xs))" 
    by (simp add: maps_of_def)
  then show ?case using h1 h2 h3 by presburger
qed

lemma "\<lbrakk> k < length xs; x \<notin> set xs \<rbrakk> \<Longrightarrow> x \<notin> Dom (map (maps_of f) xs ! k)"
proof (induction xs arbitrary: k)
  case Nil
  then show ?case
    unfolding Dom_def dom_def by fastforce
next
  case (Cons a xs)
  have k1: "k = 0 \<Longrightarrow> Dom (map (maps_of f) (a # xs) ! k) \<subseteq> {a}" 
    apply (simp add: map_maps_hd[of f a xs] maps_of_def Dom_def dom_def; clarify)
    by (metis domI domIff singleton_unfold)
  have k2: "k \<noteq> 0 \<Longrightarrow> Dom (map (maps_of f) (a # xs) ! k) \<subseteq> Dom (map (maps_of f) xs ! (k-1))" by auto
  show ?case using Cons.IH Cons.prems(1) Cons.prems(2) k1 k2
    apply (simp; clarify) 
    using less_Suc_eq_0_disj by auto
qed

lemma seq_of_map_maps: 
  "\<lbrakk>card (set xs) = length xs; \<forall>x \<in> set xs. f x \<noteq> {}\<rbrakk> \<Longrightarrow> seq_of_maps (map (maps_of f) xs)"
proof (induction xs)
  case Nil
  then show ?case by (simp add: seq_of_maps_def)
next
  case (Cons a xs)
  have h1: "seq_of_maps (map (maps_of f) xs)"
    by (meson Cons.IH Cons.prems(1) Cons.prems(2) card_distinct distinct.simps(2) distinct_card 
        list.set_intros(2))
  have h2: "\<forall>i j. i < length (map (maps_of f) (a # xs)) \<and> j < length (map (maps_of f) (a # xs)) \<and> 
      Dom ((map (maps_of f) (a # xs))!i) \<inter> Dom ((map (maps_of f) (a # xs))!j) \<noteq> {} \<longrightarrow> i = j" 
    using Dom_maps_of_diff by (metis Cons.prems(1) Cons.prems(2) length_map)
  have h3: "\<forall>M \<in> set (map (maps_of f) (a # xs)).\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 = dom m\<^sub>2"
    using h1 unfolding maps_of_def seq_of_maps_def apply clarify by fastforce
  then show ?case by (metis h2 seq_of_maps_def)
qed

subsection "Merging of Indexed Sequences of State Sets"

lemma map_Upd_Merge:
  assumes c: "card (set xs) = length xs"
  assumes f: "\<forall>x \<in> set xs. f x \<noteq> {}"
  shows "map_Upd_seq f S xs = S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of f) xs)}"
proof
  show "map_Upd_seq f S xs \<subseteq> S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of f) xs)}" 
  proof
    fix x
    assume a1: "x \<in> map_Upd_seq f S xs"
    hence h1: "x \<in> map_Add_seq S (map (maps_of f) xs)" using c map_Upd_Add by blast
    have h2: "seq_of_maps (map (maps_of f) xs)" using c f seq_of_map_maps by blast
    hence h2: "x \<in> S ** {\<Uplus>\<^sub>m set ms | ms. map_seq_of ms (map (maps_of f) xs)}"
      using h1 map_Add_seq_Merge by blast
    show "x \<in> S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of f) xs)}"
      using c f h2 map_seq_of_wk[of _ "map (maps_of f) xs"] 
        maps_seq_of[of "map (maps_of f) xs"] seq_of_map_maps[of xs f]
      by (smt (verit, best) Collect_cong)
  qed
next
  show "S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of f) xs)} \<subseteq> map_Upd_seq f S xs"
    using c f map_Upd_Add[of xs f S] map_seq_of_wk[of _ "map (maps_of f) xs"] 
      maps_seq_of[of "map (maps_of f) xs"] seq_of_map_maps[of xs f] 
    map_Add_seq_Merge[of "map (maps_of f) xs" S] apply clarify
    by (smt (z3) CollectD CollectI map_Add_def)
qed

lemma map_seq_in_dom: "\<lbrakk>map_seq_in ms (map (maps_of f) xs); m \<in> set ms\<rbrakk> \<Longrightarrow> dom m \<subseteq> set xs"
proof (induction xs arbitrary: ms)
  case Nil
  then show ?case using map_seq_in_length by fastforce
next
  case (Cons a xs)
  obtain z zs where z1: "ms = z#zs" by (meson Cons.prems(2) list.set_cases)
  hence h1: "m \<in> set zs \<Longrightarrow> dom m \<subseteq> set xs" using Cons.prems Cons.IH apply simp by blast
  have h2: "map (maps_of f) (a # xs) = {[a \<mapsto> y] |y. y \<in> f a}#map (maps_of f) xs"
    by (metis map_maps_hd)
  have "dom z \<subseteq> {a}" using Cons.prems(1) apply (simp add: h2 z1 maps_of_def)
    using dom_eq_singleton_conv by force
  then show ?case using Cons.prems(2) h1 z1 by auto
qed

lemma map_seq_merge_el: "\<lbrakk>map_seq_in ms (map (maps_of f) xs); c \<in> set xs; card (set xs) = length xs\<rbrakk> \<Longrightarrow> (\<Uplus>\<^sub>m set ms) $ c \<in> f c"
proof (induction xs arbitrary: ms)
  case Nil
  then show ?case using map_seq_in_length by fastforce
next
  case (Cons a as)
  obtain z zs where z1: "ms = z#zs"
    by (metis list.discI list.simps(9) local.Cons(2) map_seq_in.elims(2))
  hence z2: "map_seq_in zs (map (maps_of f) as)" using Cons.prems(1) by fastforce
  have h2: "map (maps_of f) (a # xs) = {[a \<mapsto> y] |y. y \<in> f a}#map (maps_of f) xs"
    by (metis map_maps_hd)
  have z3: "z $ a \<in> f a"
    using Cons.prems apply (simp add: z1)
    unfolding maps_of_def apply clarify
    by simp
  have h3: "z \<in> {[a \<mapsto> y] |y. y \<in> f a}" using Cons.prems(1) h2 z1 by force
  have z4: "card (set as) = length as" 
    by (meson Cons.prems(3) card_distinct distinct.simps(2) distinct_card)
  have z5: "c \<in> set as \<Longrightarrow> \<Uplus>\<^sub>m set zs $ c \<in> f c" using Cons.IH z2 z4 by blast
  have z6: "\<forall>x \<in> set zs. dom z \<inter> dom x = {}"
    using h3 z2 apply simp
    by (metis Cons.prems(3) Int_emptyI card_distinct distinct.simps(2) dom_empty dom_fun_upd 
        map_seq_in_dom option.distinct(1) singletonD subsetD)
  have z7: "dom (\<Uplus>\<^sub>m set zs) \<inter> dom z = {}"
    by (metis inf.idem inf_bot_right inf_commute not_dom_Merge z6)
  hence z8: "(\<Uplus>\<^sub>m set zs \<uplus>\<^sub>m z) $ c \<in> f c"
  proof (cases "c \<in> set as")
    case True
    then show ?thesis using h3 z5 z6 z7
      by (smt (verit) CollectD Cons.prems(3) card_distinct distinct.simps(2) domIff
          map_add_dom_app_simps(3) map_add_merge map_get_def singleton_unfold)
  next
    case False
    then show ?thesis using h3 z3 z6 z7
      by (smt (verit, best) Cons.prems(2) domI fun_upd_same inf.commute map_add_comm map_add_merge 
          map_some_val mem_Collect_eq set_ConsD map_le_def map_merge_left_sub)
  qed
  then show ?case
    by (smt (verit, best) Diff_insert_absorb dom_eq_empty_conv inf.idem list.set_intros(1) 
        list.simps(15) merge_Merge_diff merge_unit remdups.simps(2) set_remdups z1 z6)
qed

lemma map_seq_fun_dep:
  assumes "card (set xs) = length xs"
      and "c \<in> set xs"
      and "m \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of f) xs)}"
    shows "m $ c \<in> f c"
  using assms map_seq_merge_el by fastforce

lemma map_seq_merge_subset: "\<lbrakk>map_seq_in ms (map (maps_of f) xs)\<rbrakk> \<Longrightarrow> dom (\<Uplus>\<^sub>m set ms) \<subseteq> set xs"
proof (induction xs arbitrary: ms)
  case Nil
  then show ?case using map_seq_in_length by fastforce
next
  case (Cons a xs)
  then show ?case by (smt (verit) UN_least dual_order.trans map_Merge_dom_sub map_seq_in_dom)
qed

lemma map_seq_dom_sub:
  assumes "m \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of f) xs)}"
    shows "dom m \<subseteq> set xs"
  using assms map_seq_merge_subset by blast

lemma map_seq_merge_eq: "\<lbrakk>map_seq_in ms (map (maps_of f) xs); card (set xs) = length xs\<rbrakk> \<Longrightarrow> dom (\<Uplus>\<^sub>m set ms) = set xs"
proof
  show "\<lbrakk>map_seq_in ms (map (maps_of f) xs); card (set xs) = length xs \<rbrakk> \<Longrightarrow> dom (\<Uplus>\<^sub>m set ms) \<subseteq> set xs"
    by (simp add: map_seq_merge_subset)
next
  show "\<lbrakk>map_seq_in ms (map (maps_of f) xs); card (set xs) = length xs\<rbrakk> \<Longrightarrow> set xs \<subseteq> dom (\<Uplus>\<^sub>m set ms)"
  proof (induction xs arbitrary: ms)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    obtain z zs where z1: "ms = z#zs"
      by (meson Cons.prems list.discI list.map_disc_iff map_seq_in.elims(2))
    have z2: "map (maps_of f) (a # as) = {[a \<mapsto> y] |y. y \<in> f a}#map (maps_of f) as"
      by (metis map_maps_hd)
    have z3: "map_seq_in zs (map (maps_of f) as)" using Cons.prems z1 by auto
    then have z4: "set as \<subseteq> dom (\<Uplus>\<^sub>m set zs)" using Cons.IH
      by (meson Cons.prems(2) card_distinct distinct.simps(2) distinct_card)
    have z5: "z \<in> {[a \<mapsto> y] |y. y \<in> f a}" using Cons.prems z1 z2 by force
    then have z6: "a \<in> dom z" by fastforce
    have z7: "\<forall>x \<in> set zs. dom z \<inter> dom x = {}" using Cons.prems(2) z3 z5 apply simp
      by (metis Cons.prems(2) IntD2 card_distinct distinct.simps(2) dom_eq_singleton_conv 
          empty_subsetI insert_disjoint(2) le_iff_inf map_seq_in_dom)
    have a1: "a \<notin> set as" by (meson Cons.prems(2) card_distinct distinct.simps(2))
    have a2: "a \<notin> dom (\<Uplus>\<^sub>m set zs)" using a1 map_seq_merge_subset z3 by blast
    have a3: "\<Uplus>\<^sub>m set ms = \<Uplus>\<^sub>m (set zs \<union> {z})" by (simp add: z1)
    have a4: "... = \<Uplus>\<^sub>m set zs \<uplus>\<^sub>m z" using merge_Merge_union z7 by blast
    show ?case using a3 a4 z3 z4 z6 z7
      by (smt (verit, ccfv_threshold) inf_commute insert_Diff insert_disjoint(2) insert_subset 
          list.simps(15) map_le_implies_dom_le map_merge_left_sub map_merge_right_sub 
          map_seq_merge_subset not_dom_Merge subset_antisym)
  qed
qed

lemma map_seq_dom_dep:
  assumes "card (set xs) = length xs"
      and "m \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of f) xs)}"
    shows "dom m = set xs"
  using assms map_seq_merge_eq by fastforce

end